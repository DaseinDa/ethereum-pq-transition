"""Strict export/provenance checks; synthetic bytes, no native verifier or keys."""
import copy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from proof_input import (CHAIN, OWNER, VERSION, MAX_PROOF, installed_verifier_binding,
                         read_public_recovery)


class ProofInputTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        (self.root / "statement").mkdir()
        (self.root / "f").mkdir()
        self.now = 2000000000
        self.pi = bytearray(198)
        self.pi[:32] = CHAIN.to_bytes(32, "big")
        self.pi[64:84] = OWNER
        self.pi[92] = 1
        self.pi[93:125] = b"c" * 32
        self.pi[125:129] = VERSION.to_bytes(4, "big")
        self.pi[129:137] = (self.now + 7200).to_bytes(8, "big")
        self.pi[137:169] = (88000000000000000).to_bytes(32, "big")
        self.proof = b"synthetic proof: no acceptance claim"
        self.write_fixture()

    def write_json(self, name, value):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(value))

    def write_fixture(self):
        psha = hashlib.sha256(self.proof).hexdigest()
        isha = hashlib.sha256(self.pi).hexdigest()
        (self.root / "f/proof.postcard").write_bytes(self.proof)
        (self.root / "statement/pi198.hex").write_text(self.pi.hex() + "\n")
        self.record = {"status": "PASS", "publicTestOnly": True, "proofSHA256": psha, "piSHA256": isha}
        self.statement = {"schema": "pq-proof-pipeline/statement/v2", "publicTestOnly": True,
                          "pi198_hex": self.pi.hex(), "pi198_sha256": isha}
        public_key = b"k" * 1312
        self.key = {"publicTestOnly": True, "alg_id": 1, "public_key_hex": public_key.hex(),
                    "public_key_bytes": len(public_key), "public_key_sha256": hashlib.sha256(public_key).hexdigest(),
                    "pq_pk_commit": bytes(self.pi[93:125]).hex()}
        for name, obj in (("PROOF.json", self.record), ("statement/statement.json", self.statement),
                          ("statement/pq-key.json", self.key)):
            self.write_json(name, obj)

    def load(self):
        return read_public_recovery(self.root, now=self.now)

    def test_exact_package_export_preserves_bytes_and_current_expiry(self):
        fixture = self.load()
        self.assertEqual(fixture.pi, self.pi)
        self.assertEqual(fixture.proof, self.proof)
        self.assertEqual(fixture.expiry, self.now + 7200)
        self.assertEqual(fixture.commitment, b"c" * 32)

    def test_tampered_proof_pi_and_key_metadata_are_refused(self):
        mutations = [("f/proof.postcard", self.proof + b"!"),
                     ("statement/pi198.hex", ("00" * 198).encode())]
        for name, data in mutations:
            with self.subTest(name=name):
                self.write_fixture()
                (self.root / name).write_bytes(data)
                with self.assertRaises(ValueError):
                    self.load()
        self.write_fixture()
        self.key["public_key_sha256"] = "00" * 32
        self.write_json("statement/pq-key.json", self.key)
        with self.assertRaisesRegex(ValueError, "public key metadata"):
            self.load()

    def test_public_flags_schema_and_seed_bearing_exports_are_refused(self):
        for name, key, value in (("PROOF.json", "publicTestOnly", 1),
                                 ("statement/statement.json", "schema", "pq-proof-pipeline/statement/v1"),
                                 ("statement/pq-key.json", "xi_hex", "00" * 32),
                                 ("statement/pq-key.json", "alg_id", True)):
            with self.subTest(name=name, key=key):
                self.write_fixture()
                obj = json.loads((self.root / name).read_text())
                obj[key] = value
                self.write_json(name, obj)
                with self.assertRaises(ValueError):
                    self.load()

    def test_only_initial_unsponsored_public_fixture_statement_is_accepted(self):
        original = bytes(self.pi)
        for index in (31, 64, 91, 92, 125, 169, 170, 197):
            with self.subTest(index=index):
                self.pi = bytearray(original)
                self.pi[index] ^= 1
                self.write_fixture()
                with self.assertRaisesRegex(ValueError, "initial unsponsored recovery"):
                    self.load()

    def test_expiry_boundary_and_oversized_proof_refused_without_rewriting(self):
        for remaining in (0, 3600, 604801):
            with self.subTest(remaining=remaining):
                self.pi[129:137] = (self.now + remaining).to_bytes(8, "big")
                self.write_fixture()
                before = (self.root / "statement/pi198.hex").read_bytes()
                with self.assertRaisesRegex(ValueError, "expiry"):
                    self.load()
                self.assertEqual((self.root / "statement/pi198.hex").read_bytes(), before)
        self.pi[129:137] = (self.now + 7200).to_bytes(8, "big")
        self.proof = bytes(MAX_PROOF + 1)
        self.write_fixture()
        with self.assertRaisesRegex(ValueError, "oversized"):
            self.load()

    def test_duplicate_json_fields_refused(self):
        (self.root / "PROOF.json").write_text('{"status":"PASS","status":"FAIL"}')
        with self.assertRaisesRegex(ValueError, "duplicate JSON field"):
            self.load()

    def test_installed_source_dependency_and_actual_binary_bindings(self):
        source = {"commit": "commit", "filesSHA256": "source"}
        paths = {"prover-runtime/bin/pq-test-crypto": b"public helper", "lib/libpq_final_native.so": b"native verifier"}
        hashes = {}
        for relative, data in paths.items():
            path = self.root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
            hashes[relative] = hashlib.sha256(data).hexdigest()
        manifest = {"sourceIdentity": source, "dependencyManifestSHA256": "deps",
                    "payloads": {name: {"sha256": digest} for name, digest in hashes.items()}}
        prover = {"status": "PASS", "sourceIdentity": source, "dependencyManifestSHA256": "deps",
                  "binaries": {"pq-test-crypto": hashes["prover-runtime/bin/pq-test-crypto"]}}
        clients = dict(prover, binaries={"lib/libpq_final_native.so": hashes["lib/libpq_final_native.so"]})
        self.write_json("share/build/source-identity.json", source)
        self.write_json("prover-runtime/BUILD.json", prover)
        self.write_json("share/build/clients.json", clients)
        result = installed_verifier_binding(self.root, manifest)
        self.assertEqual(result["binaries"], hashes)
        self.assertIn("unattested", result["exportOrigin"])
        changed = copy.deepcopy(prover)
        changed["sourceIdentity"]["commit"] = "old"
        self.write_json("prover-runtime/BUILD.json", changed)
        with self.assertRaisesRegex(ValueError, "source/dependency"):
            installed_verifier_binding(self.root, manifest)
        self.write_json("prover-runtime/BUILD.json", prover)
        (self.root / "lib/libpq_final_native.so").write_bytes(b"changed")
        with self.assertRaisesRegex(ValueError, "binary hash"):
            installed_verifier_binding(self.root, manifest)


if __name__ == "__main__":
    unittest.main()
