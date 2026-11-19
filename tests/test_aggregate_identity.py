"""Installer preflight policy tests with mocked native ABI and geth processes.

These tests exercise real descriptor, payload-manifest and installation-marker
reads. They do not load a native library, execute geth, or establish C/F proof
acceptance. Each tampered descriptor is re-pinned to isolate semantic checks.
"""
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("aggregate_identity_installer", ROOT / "demo/install.py")
installer = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(installer)


class AggregateIdentityTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.prefix = self.root / "runtime"
        identity = self.prefix / "share/identity"
        identity.mkdir(parents=True)
        self.descriptor = json.loads((ROOT / "demo/identity/c-native.json").read_text())
        self.f_identity = json.loads((ROOT / "demo/identity/f-native.json").read_text())
        (identity / "f-native.json").write_text(json.dumps(self.f_identity))
        self.genesis = json.loads((ROOT / "demo/templates/migration-genesis.json").read_text())
        self.genesis_path = self.root / "genesis.json"
        self.genesis_path.write_text(json.dumps(self.genesis))
        self.inputs = self.root / "inputs"
        recovery = self.inputs / "recovery"
        recovery.mkdir(parents=True)
        self.proof = b"mock F verification input; not a real proof"
        pi = bytearray(198)
        pi[:32] = installer.PROFILE["chainId"].to_bytes(32, "big")
        self.pi = bytes(pi)
        (recovery / "proof.postcard").write_bytes(self.proof)
        (recovery / "pi.bin").write_bytes(self.pi)
        (recovery / "config.json").write_text('{"fields":{"expiry":30}}')
        self.f_native = SimpleNamespace(
            pq_f_identity_v1=Mock(return_value=json.dumps(self.f_identity).encode()),
            pq_f_ready_v1=Mock(return_value=0),
            pq_f_verify_v1=Mock(side_effect=lambda proof, proof_len, pi, pi_len:
                                0 if proof == self.proof and pi == self.pi else 1))
        self.c_native = SimpleNamespace(
            pq_aggregate_key_v1=Mock(return_value=self.descriptor["key"].encode()),
            pq_aggregate_ready_v1=Mock(return_value=0))
        def library(path):
            name = Path(path).name
            if name == "libpq_final_native.so":
                return self.f_native
            if name == "libpq_migrate_tree.so":
                return self.c_native
            self.fail("unexpected native library: " + path)
        def command(argv, **kwargs):
            if argv[1] == "version":
                return subprocess.CompletedProcess(argv, 0, stdout="geth mocked-version\n", stderr="")
            if argv[1] == "init":
                return subprocess.CompletedProcess(argv, 0, stdout="", stderr="Successfully wrote genesis state hash=mocked-genesis\n")
            self.fail("unexpected subprocess: " + repr(argv))
        self.cdll = self.enterContext(patch.object(installer.ctypes, "CDLL", side_effect=library))
        self.command = self.enterContext(patch.object(installer.subprocess, "run", side_effect=command))
        self.write_descriptor(self.descriptor)

    def repin(self):
        payloads = {}
        for path in self.prefix.rglob("*"):
            if path.is_file() and path.name not in ("manifest.json", "INSTALL-COMPLETE.json"):
                payloads[path.relative_to(self.prefix).as_posix()] = {
                    "sha256": installer.sha(path), "bytes": path.stat().st_size,
                    "mode": oct(path.stat().st_mode & 0o777)}
        manifest = {"format": 1, "profile": "pq-lean-f-native-lab-v1", "productionEnabled": False,
                    "payloads": payloads}
        manifest_path = self.prefix / "manifest.json"
        manifest_path.write_text(json.dumps(manifest))
        (self.prefix / "INSTALL-COMPLETE.json").write_text(json.dumps({"manifestSHA256": installer.sha(manifest_path)}))

    def write_descriptor(self, descriptor):
        (self.prefix / "share/identity/c-native.json").write_text(json.dumps(descriptor))
        self.repin()

    def preflight(self):
        return installer.preflight(self.prefix, self.genesis_path, self.inputs)

    def test_unchanged_descriptor_passes_full_preflight_with_mocked_native(self):
        result = self.preflight()
        self.assertEqual(result["gethInitHash"], "mocked-genesis")
        self.assertEqual(result["chainId"], installer.PROFILE["chainId"])
        self.c_native.pq_aggregate_ready_v1.assert_called_once_with()
        self.c_native.pq_aggregate_key_v1.assert_called_once_with()
        self.assertEqual(self.f_native.pq_f_verify_v1.call_count, 5)
        self.assertEqual([call.args[0][1] for call in self.command.call_args_list], ["version", "init"])
        self.assertEqual(installer.aggregate_descriptor(self.prefix), self.descriptor)

    def test_every_descriptor_value_tamper_fails_even_when_manifest_repinned(self):
        for name, value in self.descriptor.items():
            with self.subTest(field=name):
                changed = dict(self.descriptor)
                changed[name] = value + 1 if type(value) is int else value + "-tampered"
                self.write_descriptor(changed)
                installer.require_installed(self.prefix)
                with self.assertRaisesRegex(installer.Refused, "C descriptor field mismatch: " + name):
                    self.preflight()
                with self.assertRaisesRegex(installer.Refused, "C descriptor field mismatch: " + name):
                    installer.selfcheck(self.prefix)
        self.cdll.assert_not_called()
        self.command.assert_not_called()

    def test_paused_profile_is_refused_before_loading_native_libraries(self):
        path = self.prefix / "manifest.json"
        manifest = json.loads(path.read_text())
        manifest["optionalProfiles"] = ["paused-research-profile"]
        path.write_text(json.dumps(manifest))
        (self.prefix / "INSTALL-COMPLETE.json").write_text(json.dumps({"manifestSHA256": installer.sha(path)}))
        with self.assertRaisesRegex(installer.Refused, "unsupported optional profile"):
            self.preflight()
        with self.assertRaisesRegex(installer.Refused, "unsupported optional profile"):
            installer.selfcheck(self.prefix)
        self.cdll.assert_not_called()
        self.command.assert_not_called()

    def test_missing_extra_duplicate_and_equivalent_wrong_types_fail(self):
        candidates = [dict(self.descriptor, extra="unrecognized")]
        for name in self.descriptor:
            changed = dict(self.descriptor)
            del changed[name]
            candidates.append(changed)
        for name, value in self.descriptor.items():
            if type(value) is int:
                candidates.append(dict(self.descriptor, **{name: float(value)}))
        candidates.append(dict(self.descriptor, format=True))
        for changed in candidates:
            with self.subTest(descriptor=changed):
                self.write_descriptor(changed)
                with self.assertRaisesRegex(installer.Refused, "C descriptor field"):
                    self.preflight()
        path = self.prefix / "share/identity/c-native.json"
        path.write_text(json.dumps(self.descriptor)[:-1] + ', "owners": 4}')
        self.repin()
        with self.assertRaisesRegex(installer.Refused, "duplicate C descriptor"):
            self.preflight()
        self.cdll.assert_not_called()

    def test_native_key_and_readiness_must_match_descriptor(self):
        self.c_native.pq_aggregate_key_v1.return_value = b"00" * 32
        with self.assertRaisesRegex(installer.Refused, "C identity/key initialization"):
            self.preflight()
        self.c_native.pq_aggregate_key_v1.return_value = self.descriptor["key"].encode()
        self.c_native.pq_aggregate_ready_v1.return_value = 1
        with self.assertRaisesRegex(installer.Refused, "C identity/key initialization"):
            self.preflight()
        self.command.assert_not_called()

    def test_genesis_aggregate_fields_and_types_must_match_descriptor(self):
        aggregate = self.genesis["config"]["pqMigrate"]["aggregateResearch"]
        for name, value in aggregate.items():
            for replacement in ([value + 1, float(value)] if type(value) is int else [value + "-tampered"]):
                with self.subTest(field=name, replacement=replacement):
                    changed = copy.deepcopy(self.genesis)
                    changed["config"]["pqMigrate"]["aggregateResearch"][name] = replacement
                    self.genesis_path.write_text(json.dumps(changed))
                    with self.assertRaisesRegex(installer.Refused, "C descriptor/genesis"):
                        self.preflight()
        for name in ("version", "maxProofBytes"):
            changed = copy.deepcopy(self.genesis)
            changed["config"]["pqMigrate"]["fullResearch"][name] = float(self.descriptor[name])
            self.genesis_path.write_text(json.dumps(changed))
            with self.assertRaisesRegex(installer.Refused, "C descriptor/fullResearch"):
                self.preflight()
        self.cdll.assert_not_called()
        self.command.assert_not_called()

    # Start-up check S8 of the client (spec section 24.6 rule 3, vectors TB-5 to
    # TB-9 in Route A form), mirrored by the preflight on the genesis file.
    IMAGE = {"balance": "0", "nonce": "0x1", "code": "0x00"}

    def s8_genesis(self, registry, facts, timestamp="0xc"):
        """The template with its genesis at T0 = 12, where S8 applies, and the
        given entries at the two registries (None: absent)."""
        genesis = copy.deepcopy(self.genesis)
        genesis["timestamp"] = timestamp
        p = genesis["config"]["pqMigrate"]
        for address, account in ((p["registry"], registry), (p["factRegistry"], facts)):
            for key in [key for key in genesis["alloc"] if key.lower() == address.lower()]:
                del genesis["alloc"][key]
            if account is not None:
                genesis["alloc"][address] = account
        return genesis

    def test_s8_genesis_with_the_images_or_outside_the_genesis_case_passes(self):
        image = self.IMAGE
        p = self.genesis["config"]["pqMigrate"]
        unprefixed = self.s8_genesis(None, image)
        unprefixed["alloc"][p["registry"][2:].upper()] = dict(image, nonce=1, code="0X00")
        record = dict(image, balance="1000000000", storage={"0x" + "00" * 31 + "01": "0x" + "00" * 31 + "01"})
        bridge = self.s8_genesis(None, None)
        bridge["config"]["pqStateBridge"] = {"researchOnly": True}
        # geth's encoding/json reads a key in any case, rune by rune.
        folded = self.s8_genesis({"balance": "0", "Code": "0x00", "Nonce": "0x1"}, image)
        folded["Alloc"] = folded.pop("alloc")
        bridge_folded = self.s8_genesis(None, None)
        bridge_folded["config"]["PQStateBridge"] = {"researchOnly": True}
        ligature = self.s8_genesis(None, None)
        ligature["time\ufb06amp"] = ligature.pop("timestamp")
        for name, genesis in [("TB-5", self.s8_genesis(image, image)),
                              ("TB-7 preloaded slot and balance", self.s8_genesis(record, image)),
                              ("decimal and integer spellings", self.s8_genesis(dict(image, nonce="1"), dict(image, nonce=1), timestamp=12)),
                              ("key without 0x, upper-case code prefix", unprefixed),
                              ("T0 before the genesis", self.s8_genesis(image, image, timestamp="100")),
                              ("TB-8: T0 one second after the genesis", self.s8_genesis(None, None, timestamp="0xb")),
                              ("state bridge", bridge),
                              ("Alloc, Code and Nonce in other cases, read by geth", folded),
                              ("state bridge under PQStateBridge, read by geth", bridge_folded),
                              ("timestamp spelled with an st ligature, a key geth ignores", ligature)]:
            with self.subTest(case=name):
                self.genesis_path.write_text(json.dumps(genesis))
                self.assertEqual(self.preflight()["T0"], 12)

    def test_s8_genesis_without_the_images_is_refused_before_any_client_runs(self):
        image = self.IMAGE
        p = self.genesis["config"]["pqMigrate"]
        twice = self.s8_genesis(image, image)
        twice["alloc"][p["registry"][2:]] = image
        capitals = self.s8_genesis(None, None)
        capitals["Timestamp"] = capitals.pop("timestamp")
        two_timestamps = self.s8_genesis(None, image, timestamp="0x0")
        two_timestamps["TIMESTAMP"] = "0xc"
        registry, facts = "PQ_REGISTRY " + p["registry"], "FACT_REGISTRY " + p["factRegistry"]
        for name, genesis, reason in [
                ("TB-6 registry absent", self.s8_genesis(None, image), registry + " is absent"),
                ("TB-6 fact registry nonce 0", self.s8_genesis(image, dict(image, nonce="0x0")), facts + " holds nonce 0;"),
                ("TB-6 registry code 0x5b", self.s8_genesis(dict(image, code="0x5b"), image), registry + " holds code 0x5b;"),
                ("TB-9 neither image", self.s8_genesis(None, None), registry + " is absent"),
                ("the template's balance-only entry", self.s8_genesis({"balance": "1000000000"}, image), registry + " holds no code;"),
                ("code 0x0000", self.s8_genesis(dict(image, code="0x0000"), image), registry + " holds code 0x0000;"),
                ("nonce left out", self.s8_genesis({"balance": "0", "code": "0x00"}, image), registry + " holds nonce 0;"),
                ("nonce as a float", self.s8_genesis(dict(image, nonce=1.0), image), registry + " nonce = 1.0 is not a genesis integer"),
                ("nonce as true", self.s8_genesis(dict(image, nonce=True), image), registry + " nonce = True is not a genesis integer"),
                ("timestamp as an integer", self.s8_genesis(None, image, timestamp=12), registry + " is absent"),
                ("timestamp in decimal", self.s8_genesis(None, image, timestamp="12"), registry + " is absent"),
                ("registry listed twice", twice, registry + " is listed more than once"),
                ("Timestamp 0xc, read by geth, and no images", capitals, registry + " is absent"),
                ("timestamp spelled twice, geth keeping the last", two_timestamps, "the genesis spells timestamp more than once"),
                ("code spelled twice, geth keeping the last", self.s8_genesis(dict(image, Code="0x5b"), image),
                 registry + " spells code more than once")]:
            with self.subTest(case=name):
                self.genesis_path.write_text(json.dumps(genesis))
                with self.assertRaises(installer.Refused) as refused:
                    self.preflight()
                self.assertIn("start-up check S8", str(refused.exception))
                self.assertIn(reason, str(refused.exception))
        self.cdll.assert_not_called()
        self.command.assert_not_called()


if __name__ == "__main__":
    unittest.main()
