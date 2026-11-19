import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from build_provenance import capture_source, check_files, copy_tracked, sha, verify_build, verify_source, verify_runtime
from dependency_integrity import verify_bundle
from heavy_job import heavy_job
from build_verified_prover import builder_command


class ProvenanceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.root = self.base / "source"
        self.root.mkdir()
        self.git("init", "-q")
        self.git("config", "core.autocrlf", "false")
        (self.root / ".gitignore").write_bytes(b"ignored/\n")
        (self.root / "input.txt").write_bytes(b"first\n")
        self.commit()
        self.identity = capture_source(self.root)

    def git(self, *args):
        return subprocess.check_output(["git", "-C", str(self.root), *args], stderr=subprocess.DEVNULL)

    def commit(self):
        self.git("add", ".")
        self.git("-c", "user.name=Test", "-c", "user.email=test@example.invalid", "commit", "-qm", "fixture")

    def record(self):
        output = self.base / "binary"
        output.write_bytes(b"old executable")
        return {"status": "PASS", "sourceIdentity": self.identity,
                "binaries": {"binary": sha(output)}}

    def test_old_binary_rejected_after_source_commit_even_with_current_hash(self):
        record = self.record()
        (self.root / "input.txt").write_bytes(b"second\n")
        self.commit()
        with self.assertRaisesRegex(ValueError, "stale build source"):
            verify_build(self.root, record, ["binary"], self.base)

    def test_missing_provenance_and_required_binary_rejected(self):
        record = self.record()
        del record["sourceIdentity"]
        with self.assertRaisesRegex(ValueError, "source identity"):
            verify_build(self.root, record, ["binary"], self.base)
        with self.assertRaisesRegex(ValueError, "omits required"):
            verify_build(self.root, self.record(), ["missing"], self.base)

    def test_output_tamper_and_source_tamper_rejected(self):
        record = self.record()
        (self.base / "binary").write_bytes(b"replacement executable")
        with self.assertRaisesRegex(ValueError, "output mismatch"):
            verify_build(self.root, record, ["binary"], self.base)
        (self.root / "input.txt").write_bytes(b"changed\n")
        with self.assertRaises(ValueError):
            verify_source(self.root, self.identity)

    def test_assume_unchanged_does_not_bypass_committed_byte_check(self):
        self.git("update-index", "--assume-unchanged", "input.txt")
        (self.root / "input.txt").write_bytes(b"rogue\n")
        with self.assertRaisesRegex(ValueError, "committed blob"):
            capture_source(self.root)

    def test_copy_excludes_ignored_files_and_verifies_copied_bytes(self):
        (self.root / "ignored").mkdir()
        (self.root / "ignored/injected.rs").write_bytes(b"unreviewed")
        dest = self.base / "copy"
        copy_tracked(self.root, "", dest, self.identity)
        self.assertFalse((dest / "ignored").exists())
        check_files(dest, self.identity)
        (dest / "input.txt").write_bytes(b"tampered")
        with self.assertRaisesRegex(ValueError, "source content mismatch"):
            check_files(dest, self.identity)

    def test_archive_identity_roundtrip_and_tamper(self):
        dest = self.base / "archive"
        copy_tracked(self.root, "", dest, self.identity)
        (dest / "SOURCE-IDENTITY.json").write_text(json.dumps(self.identity))
        (dest / "SOURCE-COMMIT").write_text(self.identity["commit"])
        self.assertEqual(capture_source(dest), self.identity)
        (dest / "input.txt").write_bytes(b"tampered")
        with self.assertRaisesRegex(ValueError, "source content mismatch"):
            capture_source(dest)

    def test_trusted_cache_hash_checked_before_parsing(self):
        bundle = self.base / "bundle"
        bundle.mkdir()
        manifest = bundle / "CACHE-SHA256.json"
        manifest.write_bytes(b"not json")
        with self.assertRaisesRegex(ValueError, "trusted cache hash"):
            verify_bundle(bundle, expected_manifest_sha256="0" * 64)

    def test_source_record_rejects_escaping_path(self):
        record = self.record()
        record["binaries"] = {"../elsewhere": "0" * 64}
        with self.assertRaisesRegex(ValueError, "invalid source path"):
            verify_build(self.root, record, [], self.base)

    def runtime_fixture(self):
        for name in ("geth", "ream"):
            folder = self.root / "client" / name
            folder.mkdir(parents=True)
            (folder / "source.json").write_text(json.dumps({"treeManifestSHA256": "1" * 64}))
        self.commit()
        identity = capture_source(self.root)
        runtime = self.base / "runtime"
        records = runtime / "share/build"
        records.mkdir(parents=True)
        (records / "source-identity.json").write_text(json.dumps(identity))
        groups = {
            "clients": ("", ["bin/geth", "bin/ream", "lib/libpq_final_native.so", "lib/libpq_migrate_tree.so"]),
            "demo-tools": ("libexec/", ["profile-tool", "profile-tool-three", "fresh-public-keys", "export-signed", "audit-history", "pqlean-txs", "pq-n1-txs"]),
            "prover": ("prover-runtime/bin/", ["pq-migrate-leaf", "pq-migrate-tree", "pq-test-crypto", "pq-final-verify"]),
            "aggregate": ("aggregate-runtime/", ["bin/pq-migrate-tree", "bin/aggregate-verify", "lib/libpq_migrate_tree.so"]),
        }
        for name, (prefix, binaries) in groups.items():
            hashes = {}
            for relative in binaries:
                destination = "libexec/" + relative[4:] if name == "clients" and relative.startswith("bin/") else prefix + relative
                path = runtime / destination
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes((name + ":" + relative).encode())
                hashes[relative] = sha(path)
            record = {"status": "PASS", "sourceIdentity": identity, "binaries": hashes, "dependencyManifestSHA256": "2" * 64}
            (records / (name + ".json")).write_text(json.dumps(record))
        manifest = {"sourceIdentity": identity, "dependencyManifestSHA256": "2" * 64,
                    "gethSourceManifestSHA256": "1" * 64, "reamSourceManifestSHA256": "1" * 64}
        return runtime, manifest

    def test_paused_optional_profile_cannot_be_relabelled_as_default(self):
        runtime, manifest = self.runtime_fixture()
        verify_runtime(self.root, runtime, manifest)
        with self.assertRaisesRegex(ValueError, "unsupported optional profile"):
            verify_runtime(self.root, runtime, dict(manifest, optionalProfiles=["paused-research-profile"]))
        path = runtime / "share/build/clients.json"
        record = json.loads(path.read_text())
        record["optionalProfiles"] = ["paused-research-profile"]
        path.write_text(json.dumps(record))
        with self.assertRaisesRegex(ValueError, "unsupported optional profile"):
            verify_runtime(self.root, runtime, manifest)

    def test_runtime_current_stamp_cannot_cover_stale_component(self):
        runtime, manifest = self.runtime_fixture()
        verify_runtime(self.root, runtime, manifest)
        record_path = runtime / "share/build/prover.json"
        record = json.loads(record_path.read_text())
        record["sourceIdentity"] = self.identity
        record_path.write_text(json.dumps(record))
        with self.assertRaisesRegex(ValueError, "stale build source"):
            verify_runtime(self.root, runtime, manifest)

    def test_runtime_checks_real_executable_and_client_manifest(self):
        runtime, manifest = self.runtime_fixture()
        changed = dict(manifest, gethSourceManifestSHA256="3" * 64)
        with self.assertRaisesRegex(ValueError, "client source manifest"):
            verify_runtime(self.root, runtime, changed)
        (runtime / "libexec/geth").write_bytes(b"stale executable")
        with self.assertRaisesRegex(ValueError, "output mismatch"):
            verify_runtime(self.root, runtime, manifest)


class HeavyLockTests(unittest.TestCase):
    def test_busy_lock_preserved_and_own_lock_released(self):
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / "lock"
            with heavy_job(path, owner="test") as row:
                with self.assertRaisesRegex(RuntimeError, "occupied"):
                    with heavy_job(path, owner="other"):
                        self.fail("acquired another job's lock")
                self.assertEqual(json.loads(path.read_text())["token"], row["token"])
            self.assertFalse(path.exists())

    def test_replaced_lock_never_removed(self):
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / "lock"
            with heavy_job(path, owner="test"):
                path.write_text('{"token":"someone-else"}')
            self.assertEqual(json.loads(path.read_text())["token"], "someone-else")


class BuilderCompatibilityTests(unittest.TestCase):
    def test_builder_requires_and_receives_the_trusted_bundle_hash(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            for version in (0, 1, 2):
                with self.subTest(version=version):
                    builder = directory / (str(version) + ".py")
                    source = "import argparse, json\np=argparse.ArgumentParser()\n"
                    source += "p.add_argument('--out', required=True)\np.add_argument('--jobs', type=int, required=True)\n"
                    if version >= 1:
                        source += "p.add_argument('--dependencies', required=True)\n"
                    if version >= 2:
                        source += "p.add_argument('--expect-cache-sha256', required=True)\n"
                    source += "print(json.dumps(vars(p.parse_args())))\n"
                    builder.write_bytes(source.encode())
                    command = builder_command(builder, directory / "out", 2, directory / "deps", "a" * 64)
                    if version < 2:
                        result = subprocess.run(command, capture_output=True, text=True)
                        self.assertEqual(result.returncode, 2)
                        continue
                    result = json.loads(subprocess.check_output(command, text=True))
                    self.assertEqual(result["jobs"], 2)
                    if version >= 1:
                        self.assertEqual(result["dependencies"], str(directory / "deps"))
                    if version >= 2:
                        self.assertEqual(result["expect_cache_sha256"], "a" * 64)
            refusal = subprocess.run([sys.executable, "-B", str(ROOT / "tools/build_prover.py"),
                                      "--out", str(directory / "out"), "--dependencies", str(directory / "deps")],
                                     capture_output=True, text=True)
            self.assertEqual(refusal.returncode, 2)
            self.assertIn("--expect-cache-sha256", refusal.stderr)
            self.assertFalse((directory / "out").exists())


if __name__ == "__main__":
    unittest.main()
