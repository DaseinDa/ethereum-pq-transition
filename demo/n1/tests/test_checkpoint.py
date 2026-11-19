"""Real BLS authorization and checkpoint refusal tests (pinned N1 environment)."""
import contextlib
import copy
import hashlib
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
try:
    import checkpoint
    import n1lib as L
    import register
    import scenario
except ModuleNotFoundError as exc:
    if exc.name.split(".")[0] not in {"eth_hash", "py_ecc", "Crypto", "eth_typing", "eth_utils", "cytoolz", "pydantic", "typing_extensions"}:
        raise
    raise unittest.SkipTest("requires the pinned N1 Python environment: " + str(exc))


class CheckpointTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.snapshot = scenario.make_snapshot()
        cls.snap = {v["index"]: v for v in cls.snapshot["validators"]}
        cls.profile = scenario.make_profile(cls.snapshot, 1000, 1000, "fixture", "0x" + "00" * 32)
        cls.domain = register.domain_of(cls.profile)
        cls.key = b"\x01\x00\x00\x00" * 13

    def make(self, index=0, signer=None, **overrides):
        payload, _ = register.build(self.profile, self.snapshot, index, self.key, self.key,
                                    L.interop_sk(index if signer is None else signer), **overrides)
        return L.decode_payload(payload)

    def reasons(self, message, signature):
        return checkpoint.validate(message, signature, self.profile, self.snap, self.domain)[0]

    def test_real_bls_signature_and_wrong_signer(self):
        self.assertEqual(self.reasons(*self.make()), [])
        self.assertEqual(self.reasons(*self.make(signer=1)), ["bls-invalid"])

    def test_domain_separation_and_eligibility(self):
        for overrides, expected in (({"chain_id": 1}, "chain-id"), ({"scheme_id": b"\x00" * 32}, "scheme-id"),
                                    ({"activation": 1}, "lean-interval"), ({"num_active": 2**18 - 1}, "lean-interval")):
            with self.subTest(expected=expected):
                self.assertIn(expected, self.reasons(*self.make(**overrides)))
        self.assertEqual(self.reasons(*self.make(index=9)), ["withdrawal-credentials"])
        msg, sig = self.make()
        changed = copy.deepcopy(self.profile)
        changed["genesisForkVersion"] = "0x01000000"
        self.assertIn("bls-invalid", checkpoint.validate(msg, sig, changed, self.snap, register.domain_of(changed))[0])

    def test_noncanonical_key_even_with_valid_bls(self):
        bad_key = L.KOALABEAR_P.to_bytes(4, "little") + self.key[4:]
        payload, _ = register.build(self.profile, self.snapshot, 0, bad_key, self.key, L.interop_sk(0))
        self.assertIn("lean-key-noncanonical", self.reasons(*L.decode_payload(payload)))

    def test_profile_snapshot_and_common_deadline(self):
        checkpoint.validate_profile_snapshot(self.profile, self.snapshot)
        changed = copy.deepcopy(self.profile)
        changed["S"] += 1
        with self.assertRaisesRegex(checkpoint.Refused, "timing"):
            checkpoint.validate_profile_snapshot(changed, self.snapshot)
        changed = copy.deepcopy(self.profile)
        del changed["T0"]
        with self.assertRaisesRegex(checkpoint.Refused, "missing-explicit-t0"):
            checkpoint.validate_profile_snapshot(changed, self.snapshot)
        snapshot = copy.deepcopy(self.snapshot)
        snapshot["validators"][0]["effectiveBalanceGwei"] += 1
        with self.assertRaisesRegex(checkpoint.Refused, "snapshot-root"):
            checkpoint.validate_profile_snapshot(self.profile, snapshot)

    def test_checkpoint_strict_deadline_canonical_and_finalized(self):
        block = {"hash": "0xabc", "number": "0x5", "timestamp": hex(999), "stateRoot": "0xstate"}
        finalized = dict(block)

        def rpc(url, method, args):
            return finalized if args[0] == "finalized" else block

        with patch.object(L, "rpc", side_effect=rpc):
            self.assertEqual(len(checkpoint.step1(self.profile, "0xabc", ["node1", "node2"])), 2)
            block["timestamp"] = hex(1000)
            with self.assertRaisesRegex(checkpoint.Refused, "at-or-after-dreg"):
                checkpoint.step1(self.profile, "0xabc", ["node1", "node2"])
            block["timestamp"] = hex(999)
            finalized["number"] = "0x4"
            with self.assertRaisesRegex(checkpoint.Refused, "not-finalized"):
                checkpoint.step1(self.profile, "0xabc", ["node1", "node2"])
            finalized["number"] = "0x6"
            with self.assertRaisesRegex(checkpoint.Refused, "bck-not-last-finalized"):
                checkpoint.step1(self.profile, "0xabc", ["node1", "node2"])
            finalized["number"] = "0x5"
            finalized["hash"] = "0xdef"
            with self.assertRaisesRegex(checkpoint.Refused, "bck-not-last-finalized"):
                checkpoint.step1(self.profile, "0xabc", ["node1", "node2"])
            finalized["hash"] = block["hash"]
            with self.assertRaisesRegex(checkpoint.Refused, "not-canonical"):
                checkpoint.step1(self.profile, "0xother", ["node1", "node2"])

    def test_checkpoint_genesis_digest_and_explicit_t0_binding(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "genesis.json"
            genesis = {"config": {"chainId": self.profile["elChainId"], "pqMigrate": {"t0": 1000}}}
            def write(value):
                raw = json.dumps(value).encode()
                path.write_bytes(raw)
                return hashlib.sha256(raw).hexdigest()
            digest = write(genesis)
            self.assertEqual(checkpoint.validate_genesis_binding(self.profile, path, digest), digest)
            with self.assertRaisesRegex(checkpoint.Refused, "genesis-digest-mismatch"):
                checkpoint.validate_genesis_binding(self.profile, path, "00" * 32)
            genesis["config"]["pqMigrate"]["t0"] = 999
            with self.assertRaisesRegex(checkpoint.Refused, "t0-genesis-mismatch"):
                checkpoint.validate_genesis_binding(self.profile, path, write(genesis))
            genesis["config"]["pqMigrate"]["t0"] = 1000
            genesis["config"]["chainId"] += 1
            with self.assertRaisesRegex(checkpoint.Refused, "chain-id-genesis-mismatch"):
                checkpoint.validate_genesis_binding(self.profile, path, write(genesis))

    def test_missing_registry_log_is_refused(self):
        profile = dict(self.profile, registryRuntimeKeccak="0x" + L.keccak(b"code").hex())

        def rpc(url, method, args):
            if method == "eth_getCode":
                return "0x" + b"code".hex()
            if method == "eth_getStorageAt":
                return hex({"0x0": 1000, "0x1": 0, "0x2": 1}[args[1]])
            if method == "eth_getLogs":
                return []
            raise AssertionError((method, args))

        with patch.object(L, "rpc", side_effect=rpc), self.assertRaisesRegex(checkpoint.Refused, "count-mismatch"):
            checkpoint.step2(profile, 5, "0xabc", ["node1", "node2"])


class CheckpointLayoutTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.checkpoint_dir = self.root / "checkpoint"
        self.checkpoint_dir.mkdir()
        self.store = self.root / "operator"
        self.directory = self.store / "hash-sig-keys" / "honest"
        self.directory.mkdir(parents=True)
        self.keys = (b"\x01\x00\x00\x00" * 13, b"\x02\x00\x00\x00" * 13)
        for role, public in zip(("attestation", "proposal"), self.keys):
            (self.directory / (role + ".pub")).write_bytes(public)
            # Layout reads public bytes and checks private-file presence only.
            # No key generation or signing occurs in this regression.
            (self.directory / (role + ".ssz")).write_bytes(b"not-a-signing-key")
        self.entry = {"leanIndex": 0, "beaconIndex": 0,
                      "attestation": "0x" + self.keys[0].hex(), "proposal": "0x" + self.keys[1].hex()}

    def arguments(self, entries, bindings=None, keystores=None):
        content = json.dumps({"leanSet": entries}).encode()
        (self.checkpoint_dir / "lean-validators.json").write_bytes(content)
        manifest = json.dumps({"lean-validators.json": hashlib.sha256(content).hexdigest()}).encode()
        (self.checkpoint_dir / "MANIFEST.json").write_bytes(manifest)
        return SimpleNamespace(checkpoint=self.checkpoint_dir, expect_manifest_sha256=hashlib.sha256(manifest).hexdigest(),
                               keystore=keystores if keystores is not None else ["H=" + str(self.store)],
                               binding=bindings if bindings is not None else ["H:0=honest"], out=self.root / "layout")

    def test_copied_registered_tuple_leaves_the_copier_unbound(self):
        # Fix list F-04: one copied registration must not block provisioning.
        # The honest operator binds its own index; the copier's index stays
        # unbound (offline) and both are reported.
        snapshot = scenario.make_snapshot()
        profile = scenario.make_profile(snapshot, 1000, 1000, "fixture", "0x" + "00" * 32)
        snap = {v["index"]: v for v in snapshot["validators"]}
        registrations = []
        for index in (0, 1):
            payload, _ = register.build(profile, snapshot, index, *self.keys, L.interop_sk(index))
            message, signature = L.decode_payload(payload)
            self.assertEqual(checkpoint.validate(message, signature, profile, snap, register.domain_of(profile))[0], [])
            registrations.append({"seq": index, "index": index, "valid": True, "reasons": [],
                                  "message": L.message_json(message)})
        _, included, _ = checkpoint.resolve_registrations(snap, registrations)
        self.assertEqual([item["index"] for item in included], [0, 1])
        copied = [dict(self.entry, leanIndex=i, beaconIndex=item["index"],
                       attestation=item["attestation"], proposal=item["proposal"]) for i, item in enumerate(included)]
        args = self.arguments(copied)
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(checkpoint.layout(args), 0)
        registry = json.loads((args.out / "registry-H.yaml").read_text())["H"]
        self.assertEqual({entry["index"] for entry in registry}, {0})
        self.assertEqual(len(registry), 2)
        self.assertEqual({entry["privkey_file"] for entry in registry}, {"honest/attestation.ssz", "honest/proposal.ssz"})
        summary = json.loads((args.out / "layout.json").read_text())
        self.assertEqual(summary["unheldLeanIndices"], [1])
        self.assertEqual(summary["sharedKeyTuples"], [{"leanIndices": [0, 1], "boundIndices": [0]}])
        self.assertFalse(list(self.store.rglob("history-provisioned-once")), "layout never provisions history")

    def test_one_tuple_bound_to_two_indices_is_refused_before_any_write(self):
        # Copies of the same key files under another directory would sign for
        # two indices and reuse one-time keys.
        copy = self.store / "hash-sig-keys" / "copy"
        copy.mkdir()
        for name in ("attestation.pub", "proposal.pub", "attestation.ssz", "proposal.ssz"):
            (copy / name).write_bytes((self.directory / name).read_bytes())
        twin = dict(self.entry, leanIndex=1, beaconIndex=1)
        args = self.arguments([self.entry, twin], ["H:0=honest", "H:1=copy"])
        with self.assertRaisesRegex(SystemExit, "key-tuple-bound-twice"):
            checkpoint.layout(args)
        self.assertFalse(args.out.exists(), "refusal must not even create the output directory")

    def test_operator_index_is_checked_against_both_public_keys_before_any_write(self):
        other = dict(self.entry, leanIndex=1, beaconIndex=1, proposal="0x" + (b"\x03\x00\x00\x00" * 13).hex())
        args = self.arguments([self.entry, other], ["H:1=honest"])
        with self.assertRaisesRegex(SystemExit, "key-tuple-does-not-match-operator-index"):
            checkpoint.layout(args)
        self.assertFalse(args.out.exists())

    def test_all_bindings_are_preflighted_before_registry_output(self):
        for bindings, reason in (([], "explicit-key-index-bindings-required"),
                                 (["H:0=honest", "H:0=honest"], "duplicate-key-index-binding"),
                                 (["H:0=honest", "H:99=honest"], "binding-index-not-in-checkpoint"),
                                 (["H:0=../honest"], "unsafe-key-directory")):
            with self.subTest(bindings=bindings):
                args = self.arguments([self.entry], bindings)
                with self.assertRaisesRegex(SystemExit, reason):
                    checkpoint.layout(args)
                self.assertFalse(args.out.exists())
        args = self.arguments([self.entry], keystores=["H=" + str(self.store), "H=" + str(self.store)])
        with self.assertRaisesRegex(SystemExit, "duplicate-keystore-node"):
            checkpoint.layout(args)
        self.assertFalse(args.out.exists())

    def test_unbound_indices_stay_offline_and_existing_output_is_never_overwritten(self):
        other = dict(self.entry, leanIndex=1, beaconIndex=1, proposal="0x" + (b"\x03\x00\x00\x00" * 13).hex())
        args = self.arguments([self.entry, other])
        with contextlib.redirect_stdout(io.StringIO()):
            checkpoint.layout(args)
        summary = json.loads((args.out / "layout.json").read_text())
        self.assertEqual(summary["nodes"], {"H": [0]})
        self.assertEqual(summary["unheldLeanIndices"], [1])
        before = {path.name: path.read_bytes() for path in args.out.iterdir()}
        with self.assertRaises(FileExistsError):
            checkpoint.layout(args)
        self.assertEqual({path.name: path.read_bytes() for path in args.out.iterdir()}, before)


if __name__ == "__main__":
    unittest.main()
