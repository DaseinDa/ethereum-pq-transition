"""Synthetic export-boundary regressions with explicit model verifier and ML-DSA callbacks."""
from dataclasses import replace
import hashlib
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

import wallet
from authorization_tracking import Account, AccountState, Authorization, AuthorizationTracker
from wallet_epochs import CanonicalState, DerivationScope, WalletEpochStore, local_seed_identity

# Independent decoder: no production wallet encoding helper is used.
from _test_reference_wire import rlp_decode

W = 365 * 24 * 3600


def model_crypto(op, value):
    if op == "pk":
        return (hashlib.sha512(value).digest() * 21)[:1312]
    if op == "hash":
        return hashlib.sha256(value).digest()
    raise AssertionError(op)


class ExportTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.store = WalletEpochStore(self.tmp.name)
        self.tracker = AuthorizationTracker(self.tmp.name)
        self.seed = bytes(range(64))  # Public synthetic fixture, never a user's seed.
        self.scope = DerivationScope(local_seed_identity(self.seed), (0x8000002c, 0x8000003c, 0x80000000, 0, 0))
        # Frozen gate at B (rule 10 (c)): LEGACY, nonce 0, header.timestamp >= T.
        self.state = CanonicalState(13376, "11" * 32, "22" * 20, "33" * 32, 0,
                                    timestamp=1000, fork_time=900, override_window=W)
        self.account = Account(13376, "11" * 32, "22" * 20)
        self.head = AccountState(self.account, "33" * 32, 10, 1000, 0, 0, "LEGACY", False,
                                 None, 900, W, 0)
        self.tracker.observe_head(self.scope, self.head)
        self.config = {"chain_id": 13376, "domain_tag": "44" * 32, "verifier_version": 0x80000005,
                       "max_priority_fee_per_gas": 2, "max_fee_per_gas": 3, "migration_gas_limit": 6000000}
        self.plan = wallet.prepare_recovery(self.scope, self.state, self.store, self.seed, model_crypto,
                    tracker=self.tracker, domain_tag=bytes.fromhex(self.config["domain_tag"]),
                    verifier_version=self.config["verifier_version"], expiry=1200, max_account_fee=20000000)
        self.proof = b"SYNTHETIC-NOT-A-PROOF"
        self.sent = []

    def export(self, **kw):
        args = dict(head=self.head, proof=self.proof, journal=self.plan.pi, config=self.config,
                    verify_proof=lambda proof, pi: proof == self.proof and pi == self.plan.pi,
                    deliver=lambda raw: self.sent.append(raw), seed64=self.seed, crypto=model_crypto)
        args.update(kw)
        return wallet.export_recovery(self.plan, self.scope, self.state, self.store, self.tracker, **args)

    def test_wire_binding_and_record_before_delivery_without_history_backup(self):
        def send(raw):
            reopened = AuthorizationTracker(self.tmp.name).records(self.scope)
            auth = Authorization.from_pi(Account(13376, "11" * 32, "22" * 20), self.plan.pi, epoch=0)
            self.assertEqual(reopened[auth.group_id][auth.variant_id]["carriers"][hashlib.sha256(raw).hexdigest()], raw.hex())
            self.sent.append(raw)
            return "delivered"
        self.assertEqual(self.export(deliver=send), "delivered")
        raw = self.sent[0]
        self.assertEqual(raw[0], 0x7e)
        fields = rlp_decode(raw[1:])
        number = lambda x: int.from_bytes(x, "big")
        self.assertEqual(len(fields), 17)
        self.assertEqual(number(fields[0]), 13376)
        self.assertEqual(fields[1], bytes.fromhex("22" * 20))
        self.assertEqual(number(fields[2]), 0)
        self.assertEqual(number(fields[3]), 1)
        self.assertEqual(fields[4], self.plan.key.commitment)
        self.assertEqual(number(fields[5]), 1200)
        self.assertEqual(number(fields[6]), 20000000)
        self.assertEqual(number(fields[7]), 0)
        self.assertEqual(fields[8], bytes(20))
        self.assertEqual(number(fields[9]), 0)
        self.assertEqual([number(v) for v in fields[10:13]], [2, 3, 6000000])
        self.assertEqual(fields[13], [])
        self.assertEqual(number(fields[14]), self.config["verifier_version"])
        self.assertEqual(fields[15], [b"", self.proof])
        self.assertEqual(fields[16], [])
        self.assertNotIn(self.plan.key.xi, raw)
        self.assertNotIn(self.plan.key.xi.hex(), self.tracker.path.read_text())
        # No record and no second backup are needed (D-1); none was written.
        self.assertEqual(self.store.security(self.scope).compromised_epochs, frozenset())
        self.assertFalse(self.store.security_path.exists())

    def test_bad_or_missing_journal_rejected_before_verification(self):
        for journal in (b"", bytes(198), self.plan.pi[:-1]):
            with self.subTest(journal=journal[:2]), self.assertRaisesRegex(ValueError, "JOURNAL"):
                self.export(journal=journal, verify_proof=lambda *_: self.fail("should not verify"))
        self.assertEqual(self.sent, [])

    def test_verifier_rejection_or_truthy_non_boolean_never_delivers(self):
        for value in (False, 1, "true", None):
            with self.subTest(value=value), self.assertRaisesRegex(ValueError, "INVALID_PROOF"):
                self.export(verify_proof=lambda *_: value)
        # The head is observed in setUp; no authorization was recorded.
        self.assertEqual(self.tracker.records(self.scope), {})
        self.assertEqual(self.sent, [])

    def test_config_chain_domain_version_are_bound(self):
        for key, value in (("chain_id", 1), ("domain_tag", "55" * 32), ("verifier_version", 3)):
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, "CONFIGURATION"):
                self.export(config={**self.config, key: value})
        self.assertEqual(self.sent, [])

    def test_stale_plan_or_edited_pi_is_rejected(self):
        self.plan = replace(self.plan, anchor="stale")
        with self.assertRaisesRegex(ValueError, "STALE"):
            self.export()
        self.assertEqual(self.sent, [])

    def test_known_leak_received_during_verification_blocks_export(self):
        def verify(*_):
            self.store.mark_compromised(self.scope, 0, "synthetic notification")
            return True
        with self.assertRaisesRegex(ValueError, "NO_LONGER_SAFE"):
            self.export(verify_proof=verify)
        self.assertEqual(self.sent, [])

    def test_late_link_to_exposed_commitment_blocks_before_record(self):
        # prepare_recovery linked the planned key to epoch 0, so an exposure known
        # only by commitment reaches the ledger at once and the export is refused before

        account = Account(13376, "11" * 32, "22" * 20)
        self.tracker.mark_exposed(self.scope, account, self.plan.key.commitment, "known key, epoch not yet learned")
        self.assertIn(0, self.store.security(self.scope).compromised_epochs)
        with self.assertRaisesRegex(ValueError, "NO_LONGER_SAFE"):
            self.export()
        self.assertIn(0, self.store.security(self.scope).compromised_epochs)
        self.assertEqual(self.tracker.records(self.scope), {})
        self.assertEqual(self.sent, [])

    def test_store_mismatch_cannot_hide_a_leak(self):
        self.tracker = AuthorizationTracker(Path(self.tmp.name) / "other")
        with self.assertRaisesRegex(ValueError, "STORE_MISMATCH"):
            self.export()
        self.assertEqual(self.sent, [])

    def test_failed_persistence_prevents_delivery(self):
        with patch("authorization_tracking._atomic_json", side_effect=OSError("disk full")):
            with self.assertRaises(OSError):
                self.export()
        self.assertEqual(self.sent, [])

    def test_failed_delivery_retains_authorization_after_restart(self):
        def failed(_):
            raise ConnectionError("connection dropped")
        with self.assertRaises(ConnectionError):
            self.export(deliver=failed)
        self.assertTrue(AuthorizationTracker(self.tmp.name).records(self.scope))

    def test_export_needs_the_observed_head_of_the_bound_block(self):
        for head in (replace(self.head, block_hash="34" * 32), replace(self.head, timestamp=1001),
                     replace(self.head, fork_time=None), replace(self.head, migration_nonce=1)):
            with self.subTest(head=head), self.assertRaisesRegex(ValueError, "HEAD_STATE_MISMATCH"):
                self.export(head=head)
        with self.assertRaisesRegex(ValueError, "HEAD_ACCOUNT_STATE_REQUIRED"):
            self.export(head=self.state)
        self.tracker.observe_head(self.scope, replace(self.head, block_hash="35" * 32, number=11))
        with self.assertRaisesRegex(ValueError, "stale or unobserved export head"):
            self.export()
        self.assertEqual(self.sent, [])
        self.assertEqual(self.tracker.records(self.scope), {})

    def test_rule10c_prepare_recovery_needs_an_open_state_gate(self):
        params = dict(domain_tag=bytes.fromhex(self.config["domain_tag"]),
                      verifier_version=self.config["verifier_version"], expiry=1200,
                      max_account_fee=20000000)
        commit = self.plan.key.commitment
        closed = [
            (replace(self.state, timestamp=899), "FORK_NOT_ACTIVE"),
            (replace(self.state, fork_time=None), "FORK_NOT_ACTIVE"),
            (replace(self.state, code_kind="OTHER"), "NOT_AN_EOA"),
            (replace(self.state, timestamp=None), "STATE_GATE_UNEVALUATED"),
            (replace(self.state, migration_nonce=1, status="PQ_BY_PROOF", activated=True, commitment=commit),
             "ALREADY_MIGRATED"),
            (replace(self.state, migration_nonce=1, status="PQ_NATIVE", activated=True, commitment=commit),
             "ALREADY_MIGRATED"),
            (replace(self.state, migration_nonce=1, status="PQ_BY_ENROLL", commitment=b"\xee" * 32,
                     timestamp=900 + W, enrolled_at=800), "OVERRIDE_WINDOW_CLOSED"),
        ]
        for value, reason in closed:
            with self.subTest(reason=reason, status=value.status), self.assertRaisesRegex(ValueError, reason):
                wallet.prepare_recovery(self.scope, value, self.store, self.seed, model_crypto,
                                        tracker=self.tracker, **params)
        # Open gates: a stealth enrollment while T is unscheduled (l. 61) is overridable,
        # with the epoch of the pre-write nonce (31.2 rule 2; vector WE-6 (ii)). (31.2 rule 10
        # (e); l. 252, l. 417): the enrolled key's holder can sweep the balance before the override, so
        # the wallet does not choose own ETH there by itself; the owner's choice (here mode 2) is needed.
        stealth = replace(self.state, migration_nonce=1, status="PQ_BY_ENROLL", commitment=b"\xee" * 32,
                          fork_time=None, enrolled_at=800)
        with self.assertRaisesRegex(ValueError, "FEE_CHOICE_REQUIRED"):
            wallet.prepare_recovery(self.scope, stealth, self.store, self.seed, model_crypto,
                                    tracker=self.tracker, **params)
        override = wallet.prepare_recovery(self.scope, stealth, self.store, self.seed, model_crypto,
                                           tracker=self.tracker, fee=wallet.FeeChoice(fee_mode=2), **params)
        self.assertEqual((override.key.epoch, override.pi[169], override.warnings), (1, 2, ()))
        recommit = replace(self.state, migration_nonce=1, status="PQ_BY_PROOF", commitment=commit)
        self.assertEqual(wallet.prepare_recovery(self.scope, recommit, self.store, self.seed,
                                                 model_crypto, tracker=self.tracker, **params).key.epoch, 1)

        for tracker, reason in ((None, "AUTHORIZATION_TRACKER_REQUIRED"),
                                (AuthorizationTracker(Path(self.tmp.name) / "other"), "TRACKER_SECURITY_STORE_MISMATCH")):
            with self.subTest(reason=reason), self.assertRaisesRegex(ValueError, reason):
                wallet.prepare_recovery(self.scope, recommit, self.store, self.seed, model_crypto,
                                        tracker=tracker, **params)


if __name__ == "__main__":
    unittest.main()
