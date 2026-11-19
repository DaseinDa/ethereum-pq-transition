"""v1.31 wallet gate and planning regressions using explicit synthetic crypto.

These are model tests, not proof or client-execution validation. Temporary wallet
metadata stays in the test worktree and is removed by unittest cleanup.
"""
from dataclasses import replace
import hashlib
from pathlib import Path
import tempfile
import unittest

import wallet
from authorization_tracking import (
    Account, AccountState, Authorization, AuthorizationTracker, _Model,
    binding_conditions_allow, single_write_preview, state_gate,
)
from reachability import Config, Step, apply, critical_times, gate, state_of, valid
from wallet_epochs import CanonicalState, DerivationScope, WalletEpochStore, check5_gate, local_seed_identity


ROOT = Path(__file__).resolve().parent.parent
ACCOUNT = Account(13378, "11" * 32, "22" * 20)
KEY = hashlib.sha256(b"public synthetic target").digest()


def head(**changes):
    values = dict(account=ACCOUNT, block_hash="33" * 32, number=1, timestamp=150,
                  migration_nonce=0, account_nonce=0, mode="LEGACY", activated=False,
                  commitment=None, fork_time=200, override_window=100,
                  protocol_time=100, legacy_seed_proof_from_t0=True)
    values.update(changes)
    return AccountState(**values)


def canonical(h):
    return CanonicalState(h.account.chain_id, h.account.genesis_hash, h.account.address,
                          h.block_hash, h.migration_nonce, status=h.mode, activated=h.activated,
                          commitment=h.commitment, timestamp=h.timestamp, fork_time=h.fork_time,
                          override_window=h.override_window, enrolled_at=h.enrolled_at,
                          code_kind=h.effective_code_kind, protocol_time=h.protocol_time,
                          legacy_seed_proof_from_t0=h.legacy_seed_proof_from_t0)


def config(h):
    return Config(h.fork_time, h.override_window, h.protocol_time, h.legacy_seed_proof_from_t0)


def model_crypto(op, value):
    if op == "pk":
        return (hashlib.sha512(value).digest() * 21)[:1312]
    if op == "hash":
        return hashlib.sha256(value).digest()
    raise AssertionError(op)


class GateTests(unittest.TestCase):
    def assert_gates(self, h, expected):
        self.assertEqual(check5_gate(canonical(h))[0], expected)
        self.assertEqual(state_gate(h), expected)
        self.assertEqual(gate(state_of(h), h.timestamp, config(h)), expected)

    def test_t0_and_t_boundaries_both_profiles_and_code_kinds(self):
        for enabled in (False, True):
            for code in ("EMPTY", "DELEGATION", "OTHER"):
                for timestamp in (99, 100, 199, 200):
                    with self.subTest(enabled=enabled, code=code, timestamp=timestamp):
                        expected = None
                        if code != "OTHER" and timestamp >= 100:
                            expected = "FROZEN" if timestamp >= 200 else "PRE_T_LEGACY" if enabled else None
                        self.assert_gates(head(timestamp=timestamp, code_kind=code,
                                               legacy_seed_proof_from_t0=enabled), expected)

    def test_missing_authenticated_t0_or_timestamp_fails_closed(self):
        self.assert_gates(head(protocol_time=None), None)
        self.assertEqual(check5_gate(replace(canonical(head()), timestamp=None)),
                         (None, "STATE_GATE_UNEVALUATED"))
        self.assertEqual(check5_gate(canonical(head(protocol_time=None))),
                         (None, "STATE_GATE_UNEVALUATED"))

    def test_legacy_marker_metadata_is_rejected_at_every_gate(self):
        for enabled in (False, True):
            for timestamp in (150, 200):
                with self.subTest(enabled=enabled, timestamp=timestamp):
                    h = head(timestamp=timestamp, code_kind="PQ_MARKER",
                             legacy_seed_proof_from_t0=enabled)
                    with self.assertRaisesRegex(ValueError, "LEGACY state"):
                        canonical(h)
                    self.assertIsNone(state_gate(h))
                    self.assertIsNone(gate(state_of(h), timestamp, config(h)))
                    # The gate must also fail closed if inconsistent metadata
                    # reaches it without the dataclass constructor validation.
                    s = canonical(replace(h, code_kind="EMPTY"))
                    object.__setattr__(s, "code_kind", "PQ_MARKER")
                    self.assertEqual(check5_gate(s), (None, "NOT_AN_EOA"))

    def test_unscheduled_t_and_historical_flag(self):
        self.assert_gates(head(fork_time=None), "PRE_T_LEGACY")
        self.assert_gates(head(fork_time=None, legacy_seed_proof_from_t0=False), None)
        self.assert_gates(head(timestamp=200, protocol_time=None, legacy_seed_proof_from_t0=False), "FROZEN")

    def test_other_modes_and_override_deadline_do_not_change(self):
        for enabled in (False, True):
            base = head(migration_nonce=1, commitment=KEY, legacy_seed_proof_from_t0=enabled)
            self.assert_gates(replace(base, mode="PQ_BY_ENROLL", enrolled_at=120, timestamp=299), "OVERRIDE")
            self.assert_gates(replace(base, mode="PQ_BY_ENROLL", enrolled_at=120, timestamp=300), None)
            self.assert_gates(replace(base, mode="PQ_BY_PROOF"), "RECOMMIT")
            self.assert_gates(replace(base, mode="PQ_BY_PROOF", activated=True), None)
            self.assert_gates(replace(base, mode="PQ_NATIVE", activated=True), None)

    def test_t0_is_a_reachability_threshold(self):
        h = head(timestamp=80)
        self.assertIn(100, critical_times(92, config(h), (state_of(h),), ()))

    def test_implicit_and_explicit_code_metadata_compare_equally(self):
        self.assertEqual(head().to_dict(), head(code_kind="EMPTY").to_dict())

    def test_old_state_serialization_keeps_the_historical_configuration(self):
        old = head(legacy_seed_proof_from_t0=False, protocol_time=None).to_dict()
        for name in ("code_kind", "protocol_time", "legacy_seed_proof_from_t0"):
            old.pop(name)
        restored = AccountState.from_dict(old)
        self.assertEqual(restored.effective_code_kind, "EMPTY")
        self.assertIsNone(restored.protocol_time)
        self.assertFalse(restored.legacy_seed_proof_from_t0)
        self.assertIsNone(state_gate(restored))
        self.assertEqual(AccountState.from_dict(restored.to_dict()), replace(restored, code_kind="EMPTY"))

    def test_write_clears_code_preserves_account_nonce_and_ends_ecdsa(self):
        h = head(account_nonce=7, code_kind="DELEGATION")
        st, cfg = state_of(h), config(h)
        write = Step("WRITE", 0, KEY, expiry=250)
        ecdsa = Step("ECDSA", 7)
        enroll = Step("ENROLL", 7, KEY)
        self.assertTrue(valid(ecdsa, st, 150, cfg))
        self.assertTrue(valid(write, apply(ecdsa, st, 150, cfg), 150, cfg))
        end = apply(write, st, 150, cfg)
        self.assertEqual((end.mode, end.mn, end.an, end.code_kind), ("PQ_BY_PROOF", 1, 7, "EMPTY"))
        self.assertFalse(valid(ecdsa, end, 150, cfg))
        self.assertFalse(valid(enroll, end, 150, cfg))
        self.assertTrue(valid(Step("ACTIVATION", 7, KEY), end, 150, cfg))

    def test_attacker_enrollment_requires_new_nonce_for_override(self):
        h = head()
        st, cfg = state_of(h), config(h)
        attacker = Step("ENROLL", 0, hashlib.sha256(b"attacker").digest())
        end = apply(attacker, st, 150, cfg)
        self.assertEqual(gate(end, 150, cfg), "OVERRIDE")
        self.assertFalse(valid(Step("WRITE", 0, KEY, expiry=250), end, 150, cfg))
        self.assertTrue(valid(Step("WRITE", 1, KEY, expiry=250), end, 150, cfg))


class PlanningTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix=".wallet-test-", dir=ROOT)
        self.addCleanup(self.temp.cleanup)
        self.store = WalletEpochStore(self.temp.name)
        self.tracker = AuthorizationTracker(self.temp.name)
        self.seed = bytes(range(64))
        self.scope = DerivationScope(local_seed_identity(self.seed), (0x8000002c, 0x8000003c, 0x80000000, 0, 0))
        self.h = head(code_kind="DELEGATION")
        self.s = canonical(self.h)
        self.options = dict(tracker=self.tracker, domain_tag=bytes.fromhex("44" * 32),
                            verifier_version=0x80000005, expiry=250, max_account_fee=20000000)

    def prepare(self, state=None, **options):
        return wallet.prepare_recovery(self.scope, state or self.s, self.store, self.seed,
                                       model_crypto, **{**self.options, **options})

    def plan(self, acts, **options):
        return wallet.plan_payload(self.scope, self.s, self.store, self.seed, model_crypto,
                                   acts=acts, **{**self.options, "head": self.h, **options})

    def test_prepare_self_and_sponsored_pi_and_preview(self):
        for fee in (wallet.SELF_PAY, wallet.FeeChoice(fee_mode=2)):
            with self.subTest(fee_mode=fee.fee_mode):
                plan = self.prepare(fee=fee)
                self.assertEqual((len(plan.pi), plan.nonce, plan.key.epoch, plan.pi[169]), (198, 0, 0, fee.fee_mode))
                auth = Authorization.from_pi(ACCOUNT, plan.pi, epoch=0)
                self.assertTrue(binding_conditions_allow(auth, self.h))
                end = single_write_preview(auth, self.h)
                self.assertEqual((end.mode, end.migration_nonce, end.account_nonce, end.effective_code_kind),
                                 ("PQ_BY_PROOF", 1, 0, "EMPTY"))
                self.assertEqual(plan.pi[137:169], (20000000).to_bytes(32, "big"))

    def test_write_and_activation_plan_and_rebind_across_t(self):
        plan = self.plan(("WRITE_NEW_KEY", "ACTIVATION"))
        self.assertEqual(plan.elements[0].migration_nonce, 0)
        self.assertEqual(plan.elements[1].account_nonce, 0)
        self.assertEqual(plan.elements[1].planning_state[:4], ("PQ_BY_PROOF", 1, 0, False))
        later = replace(self.h, block_hash="55" * 32, number=2, timestamp=200)
        rebound = wallet.replan_payload(plan, self.scope, canonical(later), self.store, self.seed, model_crypto,
                                        tracker=self.tracker, head=later)
        self.assertEqual(rebound.status, "REBOUND")
        self.assertEqual(rebound.plan.elements[0].pi, plan.elements[0].pi)

    def test_attacker_enrollment_stales_plan_and_regenerates_override(self):
        old = self.prepare()
        attacker = replace(self.h, block_hash="55" * 32, number=2, timestamp=160, mode="PQ_BY_ENROLL",
                           migration_nonce=1, account_nonce=1, commitment=KEY, enrolled_at=155, code_kind="EMPTY")
        with self.assertRaisesRegex(ValueError, "STALE_RECOVERY_PLAN"):
            wallet.validate_plan(old, self.scope, canonical(attacker), self.store)
        new = self.prepare(canonical(attacker), fee=wallet.FeeChoice(fee_mode=2))
        self.assertEqual((new.nonce, new.key.epoch), (1, 1))
        self.assertNotEqual(new.pi, old.pi)

    def test_reorg_below_t0_voids_the_plan_even_if_next_slot_reaches_t0(self):
        plan = self.plan(("WRITE_NEW_KEY", "ACTIVATION"))
        earlier = replace(self.h, block_hash="66" * 32, timestamp=99)
        result = wallet.replan_payload(plan, self.scope, canonical(earlier), self.store, self.seed, model_crypto,
                                      tracker=self.tracker, head=earlier)
        self.assertEqual(result.status, "VOID")
        self.assertIn("GATE", result.elements[0]["changed"])
        self.assertIsNone(result.plan)

    def test_unpublished_default_and_explicit_enrollment_choice(self):
        self.assertEqual(self.tracker.migration_choice(self.scope, self.h), "SEED_PROOF")
        self.assertEqual(self.tracker.migration_choice(self.scope, self.h, knowingly_enroll=True), "ENROLL")
        with self.assertRaisesRegex(ValueError, "UNPUBLISHED_KEY_USE_SEED_PROOF"):
            self.plan(("ENROLL", "ACTIVATION"))
        plan = self.plan(("ENROLL", "ACTIVATION"), knowingly_enroll=True)
        self.assertIn(wallet.ENROLLMENT_EXPOSURE_WARNING, plan.warnings)

    def test_known_disclosures_keep_enrollment_as_the_cheap_path(self):
        for i, reason in enumerate(("sent transaction", "typed-data signature", "7702 tuple", "co-signature",
                                    "off-chain disclosure")):
            with self.subTest(reason=reason):
                scope = replace(self.scope, path=self.scope.path[:-1] + (i + 1,))
                self.tracker.mark_secp256k1_published(scope, ACCOUNT, reason)
                self.assertEqual(self.tracker.migration_choice(scope, self.h), "ENROLL")
        self.assertEqual(self.tracker.migration_choice(self.scope, replace(self.h, account_nonce=1)), "ENROLL")

    def test_explicit_enrollment_of_published_key_needs_no_exposure_warning(self):
        self.tracker.mark_secp256k1_published(self.scope, ACCOUNT, "off-chain disclosure")
        plan = self.plan(("ENROLL", "ACTIVATION"), knowingly_enroll=True)
        self.assertNotIn(wallet.ENROLLMENT_EXPOSURE_WARNING, plan.warnings)
        self.assertEqual(tuple(element.kind for element in plan.elements), ("ENROLL", "ACTIVATION"))

    def test_planner_selects_seed_proof_precursor_without_known_disclosure(self):
        s = self.tracker._scope(self.tracker._read(), self.scope)
        precursor = _Model(self.tracker, s, set(), self.h).precursor()
        self.assertEqual((precursor["role"], precursor["case"], precursor["nonce"]),
                         ("WRITE", "PRE_T_LEGACY", 0))
        s["published"][ACCOUNT.key] = "off-chain signature"
        self.assertEqual(_Model(self.tracker, s, set(), self.h).precursor()["role"], "ENROLL")

    def test_configuration_is_bound_and_missing_t0_refuses_preparation(self):
        plan = self.prepare()
        for changed in (replace(self.s, protocol_time=101), replace(self.s, legacy_seed_proof_from_t0=False)):
            with self.assertRaisesRegex(ValueError, "STALE_RECOVERY_PLAN"):
                wallet.validate_plan(plan, self.scope, changed, self.store)
        for changed in (replace(self.s, protocol_time=None), replace(self.s, timestamp=99)):
            with self.assertRaisesRegex(ValueError, "STATE_GATE_UNEVALUATED|FORK_NOT_ACTIVE"):
                self.prepare(changed)
        with self.assertRaisesRegex(ValueError, "HEAD_STATE_MISMATCH"):
            self.plan(("WRITE_NEW_KEY", "ACTIVATION"), head=replace(self.h, protocol_time=101))


if __name__ == "__main__":
    unittest.main()
