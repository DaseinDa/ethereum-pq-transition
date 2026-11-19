"""Small static/model tests; none builds or runs a native prover/verifier."""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import shutil
import sys
import tempfile
import tomllib
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from aggregate_support import HEADER, clean_environment, read_owner, statement_from_pis, verify_package
from heavy_job import heavy_job


class AggregatePackageTests(unittest.TestCase):
    def setUp(self):
        self.package = ROOT / "prover/aggregate"
        self.statement = (self.package / "fixtures/four-owner/statement.bin").read_bytes()
        self.pis = [self.statement[6 + i * 198:6 + (i + 1) * 198] for i in range(4)]

    def test_frozen_inputs_and_fixture_have_exact_recorded_bytes(self):
        manifest = verify_package(ROOT)
        self.assertEqual(manifest["importedSourceCount"], 58)
        self.assertEqual(manifest["importedSourceBytes"], 2308562)
        self.assertEqual(manifest["profile"]["statementBytes"], 798)
        self.assertEqual(statement_from_pis(self.pis), self.statement)
        self.assertEqual(hashlib.sha256(self.statement).hexdigest(),
                         "1af7a4381356e6975d788ee454dda05caa47a9dfcbae6b54ab5fdaca1f1e9b7a")

    def test_shared_workspace_paths_and_cargo_resolution(self):
        cargo = tomllib.loads((self.package / "Cargo.toml").read_text())
        self.assertEqual(cargo["package"]["name"], "pq-migrate-tree")
        self.assertEqual(cargo["lib"]["crate-type"], ["rlib", "staticlib", "cdylib"])
        self.assertEqual((self.package / "Cargo.lock").read_bytes(), (ROOT / "prover/tree/Cargo.lock").read_bytes())
        for dependency in list(cargo["dependencies"].values()) + list(cargo["patch"]["crates-io"].values()):
            if isinstance(dependency, dict) and "path" in dependency:
                self.assertTrue((self.package / dependency["path"] / "Cargo.toml").is_file())
        self.assertNotIn("default", cargo["features"])

    def test_local_dependency_edits_only_guard_diagnostics(self):
        manifest = json.loads((self.package / "SOURCE.json").read_text(encoding="utf-8"))
        changes = manifest["localSharedInputChanges"]
        self.assertEqual(len(changes), 2)
        self.assertEqual(len(changes[1]["files"]), 20)
        self.assertEqual(changes[0]["enabledBy"], "PQ_PROVER_DIAGNOSTICS=1")
        self.assertEqual(len(changes[0]["files"]), 6)
        added = '''// Optional process/shape diagnostics; disabled unless explicitly requested.
fn diagnostics_enabled() -> bool {
    std::env::var_os("PQ_PROVER_DIAGNOSTICS").as_deref() == Some(std::ffi::OsStr::new("1"))
}
fn memory_event(stage: &str) {
    if !diagnostics_enabled() {
        return;
    }'''
        for relative, row in changes[0]["files"].items():
            raw = (ROOT / relative).read_bytes()
            newline = "\r\n" if b"\r\n" in raw else "\n"
            source = raw.decode("utf-8")
            self.assertEqual(hashlib.sha256(raw).hexdigest(), row["packagedSHA256"])
            if relative in changes[1]["files"]:
                notice = changes[1]["notice"] + newline
                self.assertEqual(source.count(notice), 1)
                source = source.replace(notice, "")
            self.assertEqual(source.count(added.replace("\n", newline)), 1)
            original = source.replace(added.replace("\n", newline), 'fn memory_event(stage: &str) {')
            pattern = (r'(?m)^([ \t]*)if diagnostics_enabled\(\) \{\r?\n\1    '
                       r'(std::eprintln!\("(?:MATRICES|SALTS)[^\r\n]*;)\r?\n\1\}')
            original, count = re.subn(pattern, lambda m: m[1] + m[2], original)
            self.assertEqual(count, row["directPrintSitesGated"])
            self.assertEqual(hashlib.sha256(original.encode("utf-8")).hexdigest(), row["researchSHA256"])

    def test_all_statement_fields_preserved_in_owner_order(self):
        swapped = [self.pis[1], self.pis[0], *self.pis[2:]]
        self.assertEqual(statement_from_pis(swapped), HEADER + b"".join(swapped))
        self.assertNotEqual(statement_from_pis(swapped), self.statement)
        for offset in (0, 32, 84, 92, 93, 129, 137, 169, 170, 190):
            with self.subTest(offset=offset):
                changed = bytearray(self.pis[0])
                changed[offset] ^= 1
                self.assertEqual(statement_from_pis([bytes(changed), *self.pis[1:]])[6:204], bytes(changed))

    def test_wrong_count_lengths_version_and_duplicate_owners_rejected(self):
        candidates = [self.pis[:3], self.pis + [self.pis[0]], [self.pis[0][:-1], *self.pis[1:]],
                      [self.pis[0] + b"\0", *self.pis[1:]], [self.pis[0], self.pis[0], *self.pis[2:]]]
        version = bytearray(self.pis[0])
        version[128] ^= 1
        candidates.append([bytes(version), *self.pis[1:]])
        for pis in candidates:
            with self.subTest(lengths=list(map(len, pis))):
                with self.assertRaises(ValueError):
                    statement_from_pis(pis)

    def test_owner_reader_only_consumes_public_export_files(self):
        with tempfile.TemporaryDirectory() as td:
            path = Path(td)
            (path / "statement").mkdir()
            (path / "f").mkdir()
            (path / "statement/pi198.hex").write_text(self.pis[0].hex() + "\n")
            (path / "f/proof.postcard").write_bytes(b"public-F-placeholder")
            (path / "witness.json").write_text("not JSON and must not be read")
            (path / "PROOF.json").write_text('{"publicTestOnly":true}')
            pi, proof, public = read_owner(path)
            self.assertEqual(pi, self.pis[0])
            self.assertEqual(proof, b"public-F-placeholder")
            self.assertTrue(public)
            (path / "PROOF.json").unlink()
            self.assertFalse(read_owner(path)[2])
            (path / "f/proof.postcard").write_bytes(bytes(196609))
            with self.assertRaises(ValueError):
                read_owner(path)

    def test_frozen_source_tampering_fails_before_build(self):
        with tempfile.TemporaryDirectory() as td:
            copied = Path(td)
            manifest = json.loads((self.package / "SOURCE.json").read_text())
            for relative in ["SOURCE.json", *manifest["imports"]]:
                target = copied / "prover/aggregate" / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(self.package / relative, target)
            target = copied / "prover/aggregate/src/fkernel.rs"
            target.write_bytes(target.read_bytes() + b"\n")
            with self.assertRaisesRegex(ValueError, "imported aggregate source mismatch"):
                verify_package(copied)

    def test_external_trace_and_custody_environment_is_removed(self):
        with patch.dict("os.environ", {"PQ_AG_TRACE_ONLY": "1", "PQ_MEMORY_IO": "bad",
                                        "LD_PRELOAD": "bad", "RUSTFLAGS": "bad"}):
            env = clean_environment(RAYON_NUM_THREADS="8")
        self.assertEqual(env["RAYON_NUM_THREADS"], "8")
        for key in ("PQ_AG_TRACE_ONLY", "PQ_MEMORY_IO", "LD_PRELOAD", "RUSTFLAGS"):
            self.assertNotIn(key, env)


class HeavyJobTests(unittest.TestCase):
    def test_busy_lock_is_not_inherited_or_removed(self):
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "lock"
            with heavy_job(path, owner="outer") as row:
                self.assertEqual(json.loads(path.read_text())["token"], row["token"])
                with self.assertRaisesRegex(RuntimeError, "occupied"):
                    with heavy_job(path, owner="nested"):
                        self.fail("must not inherit lock")
                self.assertTrue(path.exists())
            self.assertFalse(path.exists())

    def test_exception_releases_only_owned_token(self):
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "lock"
            with self.assertRaisesRegex(ValueError, "failure"):
                with heavy_job(path, owner="test"):
                    raise ValueError("failure")
            self.assertFalse(path.exists())
            with heavy_job(path, owner="test"):
                path.write_text('{"token":"replacement"}')
            self.assertEqual(json.loads(path.read_text())["token"], "replacement")


if __name__ == "__main__":
    unittest.main()
