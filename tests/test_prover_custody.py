import hashlib
import io
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "prover"))
from custody import MemoryArtifacts
import statement
BUILD = Path(os.environ.get("PQ_TEST_PROVER_BUILD", "/nonexistent"))


class MemoryCustody(unittest.TestCase):
    def test_memory_roundtrip_and_close(self):
        memory = MemoryArtifacts()
        marker = b"synthetic-memory-only-credential"
        path = memory.add("leaf/proof", marker * 100000)
        fd = memory.fds[str(path)]
        self.assertFalse(path.exists())
        self.assertEqual(memory.read("leaf/proof"), marker * 100000)
        mapping = memory.environment()["PQ_CUSTODY_FDS"]
        self.assertNotIn(marker.decode(), mapping)
        memory.close()
        with self.assertRaises(OSError):
            os.fstat(fd)

    def test_private_file_input_rejected_and_stdin_accepted(self):
        obj = {"credential": {"seed64_hex": "01" * 64, "public": False}}
        with tempfile.TemporaryDirectory() as directory:
            p = Path(directory) / "private.json"
            p.write_text(json.dumps(obj))
            with self.assertRaises(ValueError):
                statement.read_input(str(p))
        with patch("sys.stdin", io.StringIO(json.dumps(obj))):
            self.assertEqual(statement.read_input("-"), obj)

    def test_value_bearing_credential_options_refused_by_the_parser(self):
        # The parser itself must refuse them (exit 2, fixed message) before any file or helper is opened.
        marker = "synthetic-secret-never-echo"
        for option in (["--seed-mnemonic", marker], ["--xi", marker], ["--path", marker], ["--credentials-stdin", marker]):
            with self.subTest(option=option[0]):
                p = subprocess.run([sys.executable, "-B", ROOT / "prover/statement.py", "decode", "pi.hex", *option,
                                    "--repo", str(ROOT), "--crypto", "x", "--crypto-sha256", "x"], capture_output=True)
                self.assertEqual(p.returncode, 2)
                self.assertEqual(p.stderr, b"invalid arguments; credentials must be supplied on stdin\n")
                self.assertNotIn(marker.encode(), p.stdout + p.stderr)

    def test_decode_credentials_shape(self):
        bad = [[], {}, {"mnemonic": "a b c"}, {"path": "m/44'/60'/0'/0/0"}, {"passphrase": "x"},
               {"mnemonic": "a", "path": "p", "seed64_hex": "00"}, {"xi": 1}]
        for value in bad:
            with self.subTest(value=value), patch("sys.stdin", io.StringIO(json.dumps(value))):
                with self.assertRaises(ValueError):
                    statement.read_decode_credentials()
        good = {"mnemonic": "a b c", "passphrase": "", "path": "m/44'/60'/0'/0/0", "xi": "00" * 32}
        with patch("sys.stdin", io.StringIO(json.dumps(good))):
            self.assertEqual(statement.read_decode_credentials(), good)


@unittest.skipUnless((BUILD / "BUILD.json").is_file(), "set PQ_TEST_PROVER_BUILD to the real prover build")
class RealToolsCustody(unittest.TestCase):
    def setUp(self):
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.manifest = json.loads((BUILD / "BUILD.json").read_text())
        self.inp = json.loads((ROOT / "demo/public-input.json").read_text())
        # Public synthetic vector, deliberately marked private to test the owner policy.
        self.inp["credential"]["public"] = False
        self.inp["pi"]["expiry"] = int(time.time()) + 86400
        self.crypto = BUILD / "bin/pq-test-crypto"
        self.hash = self.manifest["binaries"]["pq-test-crypto"]

    def test_public_outputs_contain_no_witness_or_signing_seed(self):
        witness, public, key = statement.prepare(self.inp, ROOT, self.crypto, self.hash)
        statement.save_public(self.root / "statement", public, key)
        data = b"".join(p.read_bytes() for p in (self.root / "statement").iterdir())
        self.assertNotIn(witness["seed64_hex"].encode(), data)
        self.assertNotIn(self.inp["credential"]["mnemonic"].encode(), data)
        self.assertNotIn(b"xi_hex", data)
        self.assertNotIn(b"seed64_hex", data)
        self.assertFalse(public["publicTestOnly"])
        self.assertEqual(public["fields"]["legacy_address"]["hex"], "9858effd232b4033e47d90003d41ec34ecaeda94")

    def test_decode_uses_stdin_and_does_not_echo_seed(self):
        witness, public, key = statement.prepare(self.inp, ROOT, self.crypto, self.hash)
        pi = self.root / "pi.hex"; pi.write_text(public["pi198_hex"])
        cmd = [sys.executable, "-B", ROOT / "prover/statement.py", "decode", pi, "--credentials-stdin",
               "--repo", ROOT, "--crypto", self.crypto, "--crypto-sha256", self.hash]
        mnemonic = self.inp["credential"]["mnemonic"].encode()
        cred = {"mnemonic": self.inp["credential"]["mnemonic"], "path": self.inp["path"]}
        if "passphrase" in self.inp["credential"]:
            cred["passphrase"] = self.inp["credential"]["passphrase"]
        p = subprocess.run(cmd, input=json.dumps(cred).encode(), capture_output=True)
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertTrue(json.loads(p.stdout)["address_from_credential"]["equals_pi_field"])
        self.assertNotIn(mnemonic, p.stdout + p.stderr)
        self.assertNotIn(witness["seed64_hex"].encode(), p.stdout + p.stderr)

    def test_owner_keep_inner_refused_before_output_creation(self):
        out = self.root / "denied"
        p = subprocess.run([sys.executable, "-B", ROOT / "prover/prove.py", "--build", BUILD,
             "--input", "-", "--out", out, "--keep-inner"], input=json.dumps(self.inp).encode(), capture_output=True)
        self.assertNotEqual(p.returncode, 0)
        self.assertFalse(out.exists())

    def test_leaf_rejects_file_witness(self):
        source = self.root / "input.json"; source.write_text("SYNTHETIC_FILE_WITNESS")
        p = subprocess.run([BUILD / "bin/pq-migrate-leaf", "prove-statement", "--input", source,
             "--vk", ROOT / "prover/keys/leaf.json", "--out", self.root / "out"], capture_output=True)
        self.assertNotEqual(p.returncode, 0)
        self.assertIn(b"stdin", p.stderr)
        self.assertNotIn(b"SYNTHETIC_FILE_WITNESS", p.stdout + p.stderr)

    def test_child_failure_diagnostics_not_persisted(self):
        build = self.root / "build"; (build / "bin").mkdir(parents=True)
        binaries = {}
        for name in self.manifest["binaries"]:
            target = build / "bin" / name
            if name == "pq-migrate-leaf":
                target.write_text('#!/usr/bin/python3\nimport sys\nsys.stderr.write("SYNTHETIC_PRIVATE_ASSERT:" + sys.stdin.read())\nraise SystemExit(99)\n')
                target.chmod(0o755)
            else:
                target.symlink_to(BUILD / "bin" / name)
            binaries[name] = hashlib.sha256(target.read_bytes()).hexdigest()
        (build / "BUILD.json").write_text(json.dumps({"status": "PASS", "binaries": binaries}))
        out = self.root / "failed"
        p = subprocess.run([sys.executable, "-B", ROOT / "prover/prove.py", "--build", build, "--input", "-",
             "--out", out], input=json.dumps(self.inp).encode(), capture_output=True)
        self.assertNotEqual(p.returncode, 0)
        record = json.loads((out / "PROOF.json").read_text())
        self.assertEqual(record["commands"][0]["exit"], 99)
        data = p.stdout + p.stderr + b"".join(f.read_bytes() for f in out.rglob("*") if f.is_file())
        for marker in [b"SYNTHETIC_PRIVATE_ASSERT", b"seed64_hex", self.inp["credential"]["mnemonic"].encode()]:
            self.assertNotIn(marker, data)
        self.assertFalse((out / "leaf").exists())
        self.assertFalse((out / "b").exists())
