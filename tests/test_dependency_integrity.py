import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from dependency_integrity import content, identity, export_checkout, verify_bundle, verify_git, sha


class GitCrateIntegrity(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.source = self.root / "source"
        self.source.mkdir()
        def git(*args):
            return subprocess.check_output(["git", "-C", str(self.source), *args], stderr=subprocess.DEVNULL)
        self.git = git
        git("init", "-q")
        (self.source / "Cargo.toml").write_text('[package]\nname="example"\nversion="0.1.0"\n')
        (self.source / "lib.rs").write_text("pub fn answer() -> u8 { 42 }\n")
        git("add", ".")
        git("-c", "user.name=Test", "-c", "user.email=test@example.invalid", "commit", "-qm", "fixture")
        self.revision = git("rev-parse", "HEAD").decode().strip()
        self.bundle = self.root / "bundle"
        self.checkout = "git/checkouts/example/" + self.revision[:7]
        self.dest = self.bundle / "cargo" / self.checkout
        self.source_id = "git+https://example.invalid/test#" + self.revision

    def export(self):
        files = export_checkout(self.source, self.dest, self.revision)
        crate = {"name": "example", "version": "0.1.0", "source": self.source_id,
                 "commit": self.revision, "checkout": self.checkout, "crateRoot": ".", "contentSHA256": identity(files)}
        (self.bundle / "DEPENDENCIES.json").write_text(json.dumps({"rust": [crate]}))
        (self.bundle / "GIT-CRATES.json").write_text(json.dumps({"schema": 1, "crates": [crate], "checkouts": {
            self.checkout: {"commit": self.revision, "files": files, "contentSHA256": identity(files)}}}))
        self.reseal_outer()

    def reseal_outer(self):
        checks = {p.relative_to(self.bundle).as_posix(): sha(p) for p in self.bundle.rglob("*")
                  if p.is_file() and p.name != "CACHE-SHA256.json"}
        (self.bundle / "CACHE-SHA256.json").write_text(json.dumps(checks))

    def test_roundtrip_and_untracked_source_exclusion(self):
        (self.source / "injected.rs").write_text("not in the pinned commit")
        self.export()
        self.assertFalse((self.dest / "injected.rs").exists())
        self.assertEqual(verify_git(self.bundle), 1)
        verify_bundle(self.bundle)

    def test_modified_tracked_source_rejected(self):
        (self.source / "lib.rs").write_text("changed")
        with self.assertRaises(subprocess.CalledProcessError):
            self.export()

    def test_wrong_commit_rejected(self):
        with self.assertRaises(ValueError):
            export_checkout(self.source, self.dest, "0" * 40)

    def test_cached_content_tamper_rejected_even_if_outer_list_resealed(self):
        self.export()
        (self.dest / "lib.rs").write_text("changed")
        self.reseal_outer()
        with self.assertRaisesRegex(ValueError, "content mismatch"):
            verify_bundle(self.bundle)

    def test_extra_cached_file_rejected(self):
        self.export()
        (self.dest / "extra.rs").write_text("extra")
        self.reseal_outer()
        with self.assertRaisesRegex(ValueError, "content mismatch"):
            verify_bundle(self.bundle)

    def test_missing_crate_record_rejected(self):
        self.export()
        p = self.bundle / "GIT-CRATES.json"
        record = json.loads(p.read_text()); record["crates"] = []; p.write_text(json.dumps(record))
        self.reseal_outer()
        with self.assertRaisesRegex(ValueError, "inventory coverage"):
            verify_bundle(self.bundle)

    def test_executable_bit_tamper_rejected(self):
        self.export()
        (self.dest / "lib.rs").chmod(0o755)
        with self.assertRaisesRegex(ValueError, "content mismatch"):
            verify_bundle(self.bundle)

    def test_unlisted_bundle_file_rejected(self):
        self.export()
        (self.bundle / "extra").write_text("extra")
        with self.assertRaisesRegex(ValueError, "file set mismatch"):
            verify_bundle(self.bundle)

    def test_internal_git_symlink_materialized_from_commit(self):
        (self.source / "alias.rs").symlink_to("lib.rs")
        self.git("add", ".")
        self.git("-c", "user.name=Test", "-c", "user.email=test@example.invalid", "commit", "-qm", "link")
        revision = self.git("rev-parse", "HEAD").decode().strip()
        export_checkout(self.source, self.dest, revision)
        self.assertFalse((self.dest / "alias.rs").is_symlink())
        self.assertEqual((self.dest / "alias.rs").read_bytes(), (self.dest / "lib.rs").read_bytes())

    def test_external_git_symlink_rejected(self):
        (self.source / "alias.rs").symlink_to("../outside")
        self.git("add", ".")
        self.git("-c", "user.name=Test", "-c", "user.email=test@example.invalid", "commit", "-qm", "link")
        revision = self.git("rev-parse", "HEAD").decode().strip()
        with self.assertRaises(ValueError):
            export_checkout(self.source, self.dest, revision)

    def test_archive_preserves_executable_identity(self):
        import tarfile
        from release import archive
        (self.source / "lib.rs").chmod(0o755)
        self.git("add", ".")
        self.git("-c", "user.name=Test", "-c", "user.email=test@example.invalid", "commit", "-qm", "mode")
        self.revision = self.git("rev-parse", "HEAD").decode().strip()
        self.source_id = "git+https://example.invalid/test#" + self.revision
        self.export()
        path = self.root / "cache.tar.gz"
        archive(path, [(p.relative_to(self.bundle).as_posix(), p, 0o755 if p.stat().st_mode & 0o111 else 0o644)
                       for p in self.bundle.rglob("*") if p.is_file()])
        extracted = self.root / "extracted"
        with tarfile.open(path) as tar:
            tar.extractall(extracted, filter="data")
        verify_bundle(extracted)

    def test_cargo_generated_metadata_excluded_only_in_build_copy(self):
        import shutil
        self.export()
        copied = self.root / "copied-cargo"
        shutil.copytree(self.bundle / "cargo", copied)
        metadata = copied / self.checkout / ".git"
        metadata.mkdir(); (metadata / "config").write_text("generated by Cargo")
        self.assertEqual(verify_git(self.bundle, cargo_override=copied), 1)
        (copied / self.checkout / "lib.rs").write_text("changed")
        with self.assertRaisesRegex(ValueError, "content mismatch"):
            verify_git(self.bundle, cargo_override=copied)

    def test_escaping_runtime_link_rejected(self):
        import shutil
        self.export()
        copied = self.root / "copied-cargo"
        shutil.copytree(self.bundle / "cargo", copied)
        f = copied / self.checkout / "lib.rs"
        f.unlink(); f.symlink_to(self.source / "lib.rs")
        with self.assertRaisesRegex(ValueError, "escaping"):
            verify_git(self.bundle, cargo_override=copied)
