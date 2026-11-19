"""Authorization persistence and decision-boundary regressions for sections 32 and 34.

PI/carrier/key commitments are synthetic. FinalizedView is an authenticated caller
assertion, not consensus verification. These tests do not run native signatures,
proofs, execution clients or network acceptance.
"""
from dataclasses import replace
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from authorization_tracking import (
    Account, AccountState, Authorization, AuthorizationTracker, FinalizedView,
    binding_conditions_allow, end_reason,
)
from wallet_epochs import DerivationScope, HARDENED, MetadataError, UINT64_MAX


PATH = (44 | HARDENED, 60 | HARDENED, HARDENED, 0, 0)
SCOPE = DerivationScope("synthetic-authorizations-public-test-identity", PATH)
ACCOUNT = Account(13376, "11" * 32, "22" * 20)


def commitment(epoch):
    return hashlib.sha256(b"synthetic-tracking-key:" + str(epoch).encode()).digest()


def state(**kwargs):
    values = dict(account=ACCOUNT, block_hash="33" * 32, number=10,
                  timestamp=110, migration_nonce=1, account_nonce=7,
                  mode="PQ_BY_PROOF", activated=False, commitment=commitment(0),
                  fork_time=90, override_window=200, enrolled_at=80)
    values.update(kwargs)
    return AccountState(**values)


def pi_auth(nonce=1, epoch=1, expiry=200, *, account=ACCOUNT, variant=0):
    # Complete-length synthetic layout-2 input: only the tracker-bound fields
    # have semantics in this fixture; this is not a valid migration proof.
    pi = bytearray(198)
    pi[:32] = account.chain_id.to_bytes(32, "big")
    pi[64:84] = bytes.fromhex(account.address)
    pi[84:92] = nonce.to_bytes(8, "big")
    pi[92] = 1
    pi[93:125] = commitment(epoch)
    pi[129:137] = expiry.to_bytes(8, "big")
    pi[-1] = variant
    return Authorization.from_pi(account, bytes(pi), epoch=epoch)


def rotate(epoch=3, nonce=7, *, activating=True, signer=0, account=ACCOUNT):
    return Authorization(account, "ROTATE", nonce, commitment(epoch),
                         activating=activating, signer_commitment=commitment(signer),
                         epoch=epoch)


def enrollment(epoch=0, nonce=0, *, account=ACCOUNT):
    return Authorization(account, "ENROLL", nonce, commitment(epoch), epoch=epoch)


class TrackingTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.tracker = AuthorizationTracker(self.temp.name)

    def record(self, auth, carrier=b"synthetic-carrier", scope=SCOPE):
        self.tracker.record(scope, auth, carrier)
        return auth.group_id, auth.variant_id

    def record_data(self, auth, scope=SCOPE):
        return self.tracker.records(scope)[auth.group_id][auth.variant_id]

    def assert_pending(self, auth):
        self.assertIsNone(self.record_data(auth)["ended"])

    def actions(self, result):
        return {item["action"] for item in result["offers"]}

    def test_we14_head_expiry_and_reorg_keep_tracking_and_report_current_exposure(self):
        auth = pi_auth()
        self.record(auth)
        self.tracker.observe_finalized(SCOPE, FinalizedView(state(timestamp=100)))
        self.tracker.epochs.mark_compromised(SCOPE, 1, "synthetic leak")
        expired_head = state(block_hash="44" * 32, number=12, timestamp=201)
        notice = self.tracker.observe_head(SCOPE, expired_head)
        self.assert_pending(auth)
        self.assertIn("WAIT_FINALITY_WATCH_REORG", self.actions(notice))
        self.assertFalse(notice["sends_transaction"])
        # A legal competing branch includes the carrier before expiry.
        restored = state(block_hash="55" * 32, number=11, timestamp=190,
                         migration_nonce=2, commitment=commitment(1))
        carrier_hash = hashlib.sha256(b"synthetic-carrier").hexdigest()
        notice = self.tracker.observe_head(
            SCOPE, restored,
            inclusions=[(auth.group_id, auth.variant_id, carrier_hash, "APPLIED", 1)])
        self.assert_pending(auth)
        self.assertTrue(notice["current_key_exposed"])
        self.assertIn("REPLACE_EXPOSED_CURRENT_KEY_WITH_CONFIRMATION", self.actions(notice))
        self.assertTrue(notice["offers"][0]["race"])

    def test_we22_pi_expiry_is_strict_and_requires_finalized_not_head(self):
        auth = pi_auth(expiry=200)
        self.record(auth)
        equal = state(timestamp=200)
        self.assertIsNone(end_reason(auth, equal))
        self.assertEqual(self.tracker.observe_finalized(SCOPE, FinalizedView(equal)), [])
        self.tracker.observe_head(SCOPE, state(number=12, timestamp=202))
        self.assert_pending(auth)
        expired = state(number=11, timestamp=201, block_hash="44" * 32)
        ended = self.tracker.observe_finalized(SCOPE, FinalizedView(expired, equal.block_hash))
        self.assertEqual(ended, [(auth.group_id, auth.variant_id, "PI_EXPIRED")])

    def test_we15_finalized_commitment_change_does_not_retire_rotate(self):
        first, second, r = pi_auth(1, 0), pi_auth(2, 0), rotate()
        for auth in (first, second, r):
            self.record(auth)
        v = state(migration_nonce=2, commitment=commitment(1))
        ended = self.tracker.observe_finalized(SCOPE, FinalizedView(v))
        self.assertEqual(ended, [(first.group_id, first.variant_id, "MIGRATION_NONCE_CONSUMED")])
        self.assert_pending(second)
        self.assert_pending(r)
        self.assertFalse(binding_conditions_allow(r, v))
        self.tracker.epochs.mark_compromised(SCOPE, 3, "synthetic rotate target leak")
        notice = self.tracker.observe_head(SCOPE, v)
        self.assertIn("OFFER_ACCOUNT_NONCE_CONSUMPTION", self.actions(notice))
        self.assertFalse(self.tracker.resubmission_allowed(
            SCOPE, second, v, replace(v, migration_nonce=3, commitment=commitment(0))))

    def test_we16_skipped_batch_and_carrier_deadline_do_not_end_leaf(self):
        leaf = pi_auth(2, 2, expiry=300)
        batch = b"synthetic-0x7f:sponsor_valid_until=120:status=1"
        self.record(leaf, batch)
        h = state(timestamp=150)
        inclusion = (leaf.group_id, leaf.variant_id, hashlib.sha256(batch).hexdigest(), "SKIPPED", 1)
        self.tracker.observe_head(SCOPE, h, inclusions=[inclusion])
        self.tracker.observe_finalized(SCOPE, FinalizedView(h))
        self.assert_pending(leaf)
        self.tracker.mark_exposed(SCOPE, ACCOUNT, leaf.commitment, "known leaf leak")
        notice = self.tracker.observe_head(SCOPE, h)
        self.assertEqual(next(x["pi_expiry"] for x in notice["offers"] if "pi_expiry" in x), 300)
        # D-2, WE-16 (iii): the leaf binds nonce 2 above the head's 1, the re-commit
        # gate is open and the current key is not exposed, so the first act is the
        # activation of the current key only, never an advance through nonce 2.
        self.assertIn("OFFER_CURRENT_KEY_ACTIVATION_DO_NOT_ADVANCE_MIGRATION_NONCE", self.actions(notice))
        self.assertNotIn("OFFER_FINALIZING_ACTIVATION_OR_ADVANCE_PAST_PI_NONCE", self.actions(notice))
        leaf_offer = next(x for x in notice["offers"] if x.get("variant") == leaf.variant_id)
        self.assertIs(leaf_offer["advance_migration_nonce"], False)
        self.assertEqual(leaf_offer["pi_nonce_position"], "ABOVE_HEAD")
        # A later aggregator carrier is retained with the very same leaf PI.
        self.record(leaf, b"synthetic-new-batch:sponsor_nonce=8")
        self.assertEqual(len(self.record_data(leaf)["carriers"]), 2)
        self.assertEqual(self.record_data(leaf)["observations"][0]["outcome"], "SKIPPED")

    def test_we16_unexposed_same_key_retry_cannot_make_exposed_future_leaf_live(self):
        first, leaf = pi_auth(1, 0), pi_auth(2, 2)
        self.record(first)
        self.record(leaf)
        self.tracker.epochs.mark_compromised(SCOPE, 2, "future leaf key leaked")
        h = state()
        self.tracker.observe_head(SCOPE, h)
        self.assertFalse(binding_conditions_allow(leaf, h))
        after = replace(h, migration_nonce=2)
        self.assertTrue(binding_conditions_allow(leaf, after))
        self.assertFalse(self.tracker.resubmission_allowed(SCOPE, first, h, after))

    def test_we17_activated_enrollment_is_not_final_and_retry_must_not_reopen_rotate(self):
        r, recovery = rotate(2, nonce=2), pi_auth(1, 0)
        self.record(r)
        self.record(recovery)
        self.tracker.epochs.mark_compromised(SCOPE, 2, "orphan key leak")
        f = state(mode="PQ_BY_ENROLL", activated=True, account_nonce=2)
        self.assertFalse(f.binding_final)
        self.assertIsNone(end_reason(r, f))
        self.tracker.observe_finalized(SCOPE, FinalizedView(f))
        self.assert_pending(r)
        self.tracker.observe_head(SCOPE, f)
        after = replace(f, mode="PQ_BY_PROOF", activated=False, migration_nonce=2)
        self.assertTrue(binding_conditions_allow(r, after))
        self.assertFalse(self.tracker.resubmission_allowed(SCOPE, recovery, f, after))
        consumed = replace(f, block_hash="44" * 32, number=11, timestamp=111, account_nonce=3)
        self.tracker.observe_finalized(SCOPE, FinalizedView(consumed, f.block_hash))
        self.assertEqual(self.record_data(r)["ended"]["reason"], "ACCOUNT_NONCE_CONSUMED")

    def test_we18_enrollment_waits_until_finality_at_T_and_reorg_still_reports_key(self):
        e = enrollment()
        self.record(e)
        self.tracker.epochs.mark_compromised(SCOPE, 0, "enrollment key leak")
        f = state(mode="LEGACY", commitment=None, migration_nonce=0,
                  account_nonce=0, timestamp=90, fork_time=100)
        self.tracker.observe_finalized(SCOPE, FinalizedView(f))
        h = replace(f, timestamp=100, number=11, block_hash="44" * 32)
        notice = self.tracker.observe_head(SCOPE, h)
        self.assert_pending(e)
        self.assertIn("WAIT_FINALITY_WATCH_REORG", self.actions(notice))
        branch = replace(h, timestamp=99, mode="PQ_BY_ENROLL", commitment=commitment(0),
                         migration_nonce=1, account_nonce=1, block_hash="55" * 32)
        self.assertTrue(self.tracker.observe_head(SCOPE, branch)["current_key_exposed"])
        self.tracker.observe_finalized(SCOPE, FinalizedView(h, f.block_hash))
        self.assertEqual(self.record_data(e)["ended"]["reason"], "ENROLLMENT_CLOSED")

    def test_we19_extended_window_uses_current_config_and_only_finalized_closes(self):
        a = pi_auth(expiry=500)
        self.record(a)
        self.tracker.epochs.mark_compromised(SCOPE, 1, "override target leak")
        f = state(mode="PQ_BY_ENROLL", timestamp=120, override_window=50)
        self.assertEqual(f.deadline, 140)
        self.tracker.observe_finalized(SCOPE, FinalizedView(f))
        closed_head = replace(f, number=12, timestamp=150, block_hash="44" * 32)
        self.assertIn("WAIT_FINALITY_WATCH_REORG", self.actions(self.tracker.observe_head(SCOPE, closed_head)))
        self.assert_pending(a)
        extended = replace(closed_head, override_window=150, block_hash="55" * 32)
        self.assertEqual(extended.deadline, 240)
        self.tracker.observe_finalized(SCOPE, FinalizedView(extended, f.block_hash))
        self.assert_pending(a)
        notice = self.tracker.observe_head(SCOPE, extended)
        self.assertNotIn("WAIT_FINALITY_WATCH_REORG", self.actions(notice))
        closed_final = replace(extended, number=13, timestamp=240, block_hash="66" * 32)
        self.tracker.observe_finalized(SCOPE, FinalizedView(closed_final, extended.block_hash))
        self.assertEqual(self.record_data(a)["ended"]["reason"], "BINDING_FINAL")

    def test_unscheduled_T_is_not_zero_and_deadline_uses_unbounded_addition(self):
        e = enrollment()
        unscheduled = state(mode="LEGACY", commitment=None, fork_time=None,
                            migration_nonce=0, account_nonce=0, timestamp=UINT64_MAX)
        self.assertIsNone(end_reason(e, unscheduled))
        self.assertTrue(binding_conditions_allow(e, unscheduled))
        self.assertIsNone(unscheduled.deadline)
        overflow = state(mode="PQ_BY_ENROLL", fork_time=UINT64_MAX - 5,
                         override_window=10, timestamp=UINT64_MAX)
        self.assertEqual(overflow.deadline, UINT64_MAX + 5)
        self.assertFalse(overflow.binding_final)
        p = pi_auth(expiry=UINT64_MAX)
        self.assertIsNone(end_reason(p, overflow))
        self.assertFalse(replace(overflow, fork_time=None).binding_final)
        later_enrollment = state(mode="PQ_BY_ENROLL", fork_time=90,
                                 enrolled_at=120, override_window=50)
        self.assertEqual(later_enrollment.deadline, 170)

    def test_we20_revived_rotate_reports_range_repair_without_automatic_write(self):
        r = rotate(epoch=4)
        self.record(r)
        v = state(migration_nonce=2, commitment=commitment(1))
        self.tracker.observe_finalized(SCOPE, FinalizedView(v))
        self.assert_pending(r)
        restarted = AuthorizationTracker(self.temp.name)
        applied = state(number=11, timestamp=130, block_hash="44" * 32,
                        migration_nonce=4, account_nonce=8,
                        activated=True, commitment=commitment(4))
        inclusion = (r.group_id, r.variant_id, hashlib.sha256(b"synthetic-carrier").hexdigest(), "APPLIED", 3)
        notice = restarted.observe_head(SCOPE, applied, inclusions=[inclusion])
        self.assertIn("OFFER_RANGE_REPAIR", self.actions(notice))
        self.assertFalse(notice["sends_transaction"])
        self.assertEqual(next(x["epoch"] for x in notice["offers"] if x["action"] == "OFFER_RANGE_REPAIR"), 4)
        self.assertEqual(applied.migration_nonce, 4)

    def test_we20_exposed_current_epoch_never_offers_same_key_range_repair(self):
        r = rotate(epoch=4)
        self.record(r)
        self.tracker.epochs.mark_compromised(SCOPE, 4, "current key exposed")
        h = state(migration_nonce=4, account_nonce=8, activated=True, commitment=commitment(4))
        inclusion = (r.group_id, r.variant_id, hashlib.sha256(b"synthetic-carrier").hexdigest(), "APPLIED", 3)
        notice = self.tracker.observe_head(SCOPE, h, inclusions=[inclusion])
        self.assertNotIn("OFFER_RANGE_REPAIR", self.actions(notice))
        self.assertIn("REPLACE_EXPOSED_KEY_WITH_CONFIRMATION", self.actions(notice))
        self.assertIn("REPLACE_EXPOSED_CURRENT_KEY_WITH_CONFIRMATION", self.actions(notice))

    def test_we20_skipped_or_in_range_rotate_does_not_offer_range_repair(self):
        r = rotate(epoch=4)
        self.record(r)
        carrier = hashlib.sha256(b"synthetic-carrier").hexdigest()
        for outcome, prestate in (("SKIPPED", 3), ("APPLIED", 4), ("APPLIED", 5), ("APPLIED", None)):
            with self.subTest(outcome=outcome, prestate=prestate):
                current = state(migration_nonce=4, account_nonce=8,
                                activated=True, commitment=commitment(4))
                notice = self.tracker.observe_head(SCOPE, current, inclusions=[(
                    r.group_id, r.variant_id, carrier, outcome, prestate)])
                self.assertNotIn("OFFER_RANGE_REPAIR", self.actions(notice))

    def test_we21_never_included_dropped_plan_survives_head_changes_and_restart(self):
        a = pi_auth()
        self.record(a, b"synthetic-broadcast-before-any-inclusion")
        self.tracker.epochs.mark_compromised(SCOPE, 1, "key learned exposed after eviction")
        self.tracker.observe_head(SCOPE, state(migration_nonce=2))
        self.assert_pending(a)
        self.assertEqual(self.record_data(a)["observations"], [])
        self.tracker = AuthorizationTracker(self.temp.name)
        reverted = state(block_hash="44" * 32, migration_nonce=1)
        notice = self.tracker.observe_head(SCOPE, reverted)
        self.assertIn((a.group_id, a.variant_id), notice["exposed_pending"])
        self.assertIn("OFFER_FINALIZING_ACTIVATION_OR_ADVANCE_PAST_PI_NONCE", self.actions(notice))
        # The preview is the state after O alone, which commits a.commitment.
        self.assertFalse(self.tracker.resubmission_allowed(
            SCOPE, a, reverted, replace(reverted, migration_nonce=2, commitment=a.commitment)))

    def test_we22_each_permanent_end_condition(self):
        cases = [
            (pi_auth(), state(migration_nonce=2), "MIGRATION_NONCE_CONSUMED"),
            (pi_auth(), state(activated=True), "BINDING_FINAL"),
            (pi_auth(), state(mode="PQ_NATIVE"), "BINDING_FINAL"),
            (pi_auth(), state(mode="PQ_BY_ENROLL", timestamp=290), "BINDING_FINAL"),
            (rotate(), state(account_nonce=8), "ACCOUNT_NONCE_CONSUMED"),
            (rotate(), state(activated=True), "FINAL_AND_ACTIVATED"),
            (enrollment(), state(account_nonce=1), "ACCOUNT_NONCE_CONSUMED"),
            (enrollment(), state(account_nonce=0), "NO_LONGER_LEGACY"),
            (enrollment(), state(mode="LEGACY", commitment=None, account_nonce=0,
                                 timestamp=90), "ENROLLMENT_CLOSED"),
        ]
        for a, f, expected in cases:
            with self.subTest(kind=a.kind, expected=expected, mode=f.mode):
                self.assertEqual(end_reason(a, f), expected)

    def test_we22_retirement_keeps_current_key_leak_warning_and_epoch_record(self):
        a = pi_auth()
        self.record(a)
        self.tracker.epochs.mark_compromised(SCOPE, 1, "must not be forgotten")
        f = state(migration_nonce=2, activated=True, commitment=commitment(1))
        self.tracker.observe_finalized(SCOPE, FinalizedView(f))
        self.tracker = AuthorizationTracker(self.temp.name)
        result = self.tracker.observe_head(SCOPE, f)
        self.assertEqual(result["pending"], [])
        self.assertEqual(result["exposed_pending"], [])
        self.assertTrue(result["current_key_exposed"])
        self.assertIn("REPLACE_EXPOSED_CURRENT_KEY_WITH_CONFIRMATION", self.actions(result))
        self.assertIn(1, self.tracker.epochs.security(SCOPE).compromised_epochs)
        self.assertEqual(len(self.record_data(a)["carriers"]), 1)

    def test_same_rotate_nonce_groups_variants_but_activation_does_not_retire_nonactivating(self):
        activating, ordinary = rotate(), rotate(epoch=4, activating=False)
        self.assertEqual(activating.group_id, ordinary.group_id)
        self.assertNotEqual(activating.variant_id, ordinary.variant_id)
        self.record(activating, b"synthetic-activating-rotate")
        self.record(ordinary, b"synthetic-ordinary-rotate")
        f = state(activated=True)
        self.tracker.observe_finalized(SCOPE, FinalizedView(f))
        self.assertEqual(self.record_data(activating)["ended"]["reason"], "FINAL_AND_ACTIVATED")
        self.assert_pending(ordinary)
        consumed = replace(f, number=11, timestamp=111, block_hash="44" * 32, account_nonce=8)
        self.tracker.observe_finalized(SCOPE, FinalizedView(consumed, f.block_hash))
        self.assertEqual(self.record_data(ordinary)["ended"]["reason"], "ACCOUNT_NONCE_CONSUMED")

    def test_multiple_PI_variants_and_shared_carrier_are_independent(self):
        first, same_fields_different_PI = pi_auth(1, 1), pi_auth(1, 1, variant=1)
        later = pi_auth(2, 2)
        for a in (first, same_fields_different_PI, later):
            self.record(a, b"synthetic-multi-PI-batch")
        self.assertEqual(len(self.tracker.records(SCOPE)), 3)
        self.tracker.observe_finalized(SCOPE, FinalizedView(state(migration_nonce=2)))
        self.assertIsNotNone(self.record_data(first)["ended"])
        self.assertIsNotNone(self.record_data(same_fields_different_PI)["ended"])
        self.assert_pending(later)

    def test_late_carrier_and_epoch_discovery_preserve_retirement_and_identity(self):
        a = pi_auth()
        without_epoch = replace(a, epoch=None)
        self.record(without_epoch)
        self.tracker.observe_finalized(SCOPE, FinalizedView(state(migration_nonce=2)))
        self.record(a, b"synthetic-second-carrier-learned-late")
        r = self.record_data(a)
        self.assertEqual(r["authorization"]["epoch"], 1)
        self.assertEqual(len(r["carriers"]), 2)
        self.assertEqual(r["ended"]["reason"], "MIGRATION_NONCE_CONSUMED")
        before = self.tracker.path.read_bytes()
        with self.assertRaises(ValueError):
            self.record(replace(a, epoch=9))
        self.assertEqual(self.tracker.path.read_bytes(), before)

    def test_authorization_learned_after_finality_evaluates_existing_checkpoint(self):
        f = state(migration_nonce=2)
        self.tracker.observe_finalized(SCOPE, FinalizedView(f))
        a = pi_auth()
        self.record(a)
        self.assertEqual(self.record_data(a)["ended"]["reason"], "MIGRATION_NONCE_CONSUMED")

    def test_account_chain_genesis_address_and_scope_isolation(self):
        accounts = [ACCOUNT, replace(ACCOUNT, chain_id=1),
                    replace(ACCOUNT, genesis_hash="44" * 32),
                    replace(ACCOUNT, address="55" * 20)]
        authorizations = [pi_auth(account=a) for a in accounts]
        self.assertEqual(len({a.group_id for a in authorizations}), 4)
        for a in authorizations:
            self.record(a)
        self.tracker.observe_finalized(SCOPE, FinalizedView(state(migration_nonce=2)))
        for a in authorizations[1:]:
            self.assert_pending(a)
            notice = self.tracker.observe_head(SCOPE, state(account=a.account))
            self.assertEqual(notice["pending"], [(a.group_id, a.variant_id)])
            self.assertFalse(notice["exposed_pending"])
        other_scope = DerivationScope("other-synthetic-seed-identity", PATH)
        self.record(authorizations[0], scope=other_scope)
        self.assertIsNone(self.record_data(authorizations[0], other_scope)["ended"])

    def test_finality_requires_monotone_same_account_checkpoints_and_rejects_conflict(self):
        a = pi_auth()
        self.record(a)
        f = state()
        self.tracker.observe_finalized(SCOPE, FinalizedView(f))
        before = self.tracker.path.read_bytes()
        self.assertEqual(self.tracker.observe_finalized(SCOPE, FinalizedView(f)), [])
        self.assertEqual(self.tracker.path.read_bytes(), before)
        bad_states = [
            replace(f, number=9, timestamp=111, block_hash="44" * 32),
            replace(f, block_hash="44" * 32),
            replace(f, number=11, timestamp=110, block_hash="44" * 32),
            replace(f, number=11, timestamp=111, block_hash="44" * 32, migration_nonce=0),
            replace(f, number=11, timestamp=111, block_hash="44" * 32, account_nonce=6),
            replace(f, number=11, timestamp=111, block_hash="44" * 32, mode="LEGACY", commitment=None),
        ]
        for bad in bad_states:
            with self.subTest(state=bad):
                with self.assertRaises(MetadataError):
                    self.tracker.observe_finalized(SCOPE, FinalizedView(bad, f.block_hash))
                self.assertEqual(self.tracker.path.read_bytes(), before)
        advance = replace(f, number=11, timestamp=111, block_hash="44" * 32)
        with self.assertRaises(MetadataError):
            self.tracker.observe_finalized(SCOPE, FinalizedView(advance, "55" * 32))
        with self.assertRaises(ValueError):
            self.tracker.observe_finalized(SCOPE, f)

    def test_finality_cannot_reopen_binding_final_gate(self):
        f = state(mode="PQ_BY_ENROLL", timestamp=300)
        self.assertTrue(f.binding_final)
        self.tracker.observe_finalized(SCOPE, FinalizedView(f))
        reopened = replace(f, number=11, timestamp=301, override_window=400, block_hash="44" * 32)
        with self.assertRaises(MetadataError):
            self.tracker.observe_finalized(SCOPE, FinalizedView(reopened, f.block_hash))

    def test_resubmission_needs_fresh_same_head_preview_and_known_unexposed_authorization(self):
        a = pi_auth()
        h = state()
        self.record(a)
        after = replace(h, migration_nonce=2, commitment=a.commitment)
        with self.assertRaises(ValueError):
            self.tracker.resubmission_allowed(SCOPE, a, h, after)
        self.tracker.observe_head(SCOPE, h)
        self.assertTrue(self.tracker.resubmission_allowed(SCOPE, a, h, after))
        for changed in (replace(after, number=11), replace(after, timestamp=111),
                        replace(after, block_hash="44" * 32),
                        replace(after, override_window=201),
                        replace(after, fork_time=91),
                        replace(after, account=replace(ACCOUNT, chain_id=1))):
            with self.subTest(changed=changed):
                with self.assertRaises(ValueError):
                    self.tracker.resubmission_allowed(SCOPE, a, h, changed)
        with self.assertRaises(ValueError):
            self.tracker.resubmission_allowed(SCOPE, pi_auth(2, 2), h, after)
        self.tracker.observe_head(SCOPE, replace(h, block_hash="55" * 32))
        with self.assertRaises(ValueError):
            self.tracker.resubmission_allowed(SCOPE, a, h, after)

    def test_unknown_history_does_not_gate_recording_or_unexposed_retry(self):
        self.assertEqual(self.tracker.epochs.security(SCOPE).compromised_epochs, frozenset())
        self.assertEqual(self.tracker.records(SCOPE), {})
        self.assertFalse(self.tracker.epochs.security_path.exists())
        a = pi_auth()
        self.record(a)
        h = state()
        notice = self.tracker.observe_head(SCOPE, h)
        self.assertFalse(notice["exposed_pending"])
        self.assertTrue(self.tracker.resubmission_allowed(
            SCOPE, a, h, replace(h, migration_nonce=2, commitment=a.commitment)))
        self.assertFalse(self.tracker.epochs.security_path.exists())

    def test_atomic_record_failure_keeps_old_carriers_and_does_not_reset_history(self):
        a = pi_auth()
        self.record(a, b"synthetic-durable-carrier")
        before = self.tracker.path.read_bytes()
        with patch("wallet_epochs.os.replace", side_effect=OSError("injected rename failure")):
            with self.assertRaises(OSError):
                self.record(a, b"synthetic-uncommitted-carrier")
        self.assertEqual(self.tracker.path.read_bytes(), before)
        self.assertEqual(len(self.record_data(a)["carriers"]), 1)
        self.assertEqual(list(Path(self.temp.name).glob("*.tmp")), [])

    def test_corrupt_carrier_or_retirement_record_fails_closed(self):
        a = pi_auth()
        self.record(a)
        original = self.tracker.path.read_bytes()
        d = json.loads(original)
        r = d["scopes"][SCOPE.key]["groups"][a.group_id][a.variant_id]
        r["carriers"][next(iter(r["carriers"]))] = "00"
        self.tracker.path.write_text(json.dumps(d), encoding="utf-8")
        with self.assertRaises(MetadataError):
            self.tracker.records(SCOPE)
        self.tracker.path.write_bytes(original)
        d = json.loads(original)
        r = d["scopes"][SCOPE.key]["groups"][a.group_id][a.variant_id]
        r["ended"] = {"reason": "PI_EXPIRED", "state": state(timestamp=200).to_dict()}
        self.tracker.path.write_text(json.dumps(d), encoding="utf-8")
        with self.assertRaises(MetadataError):
            self.tracker.records(SCOPE)

    def test_PI_and_inclusion_binding_mismatch_rejected_without_erasing_history(self):
        a = pi_auth()
        self.record(a)
        with self.assertRaises(ValueError):
            Authorization.from_pi(replace(ACCOUNT, address="44" * 20), a.pi)
        with self.assertRaises(ValueError):
            Authorization.from_pi(ACCOUNT, a.pi[:-1])
        with self.assertRaises(ValueError):
            self.tracker.observe_head(SCOPE, state(), inclusions=[(
                a.group_id, a.variant_id, "00" * 32, "APPLIED", 1)])
        with self.assertRaises(ValueError):
            self.tracker.observe_head(SCOPE, state(), inclusions=[(
                a.group_id, a.variant_id, hashlib.sha256(b"synthetic-carrier").hexdigest(), "BATCH_STATUS_1", 1)])
        self.assertEqual(self.record_data(a)["observations"], [])

    def test_export_persists_before_delivery_and_keeps_failed_delivery(self):
        a = pi_auth()
        raw = b"synthetic-export-carrier"
        deliveries = []
        h = state()
        self.tracker.observe_head(SCOPE, h)

        def deliver(carrier):
            # Another process instance must see the complete durable record
            # before the first byte can be handed to a network callback.
            on_disk = AuthorizationTracker(self.temp.name).records(SCOPE)
            r = on_disk[a.group_id][a.variant_id]
            self.assertIn(hashlib.sha256(carrier).hexdigest(), r["carriers"])
            deliveries.append(carrier)
            return "synthetic-delivery-id"

        self.assertEqual(self.tracker.export(SCOPE, a, raw, deliver, head=h), "synthetic-delivery-id")
        self.assertEqual(deliveries, [raw])
        # (spec 35.2 rule 1 (e)): a second PI at the head's migration_nonce (was pi_auth(2, 2), a write
        # above the head's nonce, which only a later planning state can carry and which no longer leaves alone).
        second = pi_auth(1, 1, variant=1)
        with self.assertRaisesRegex(OSError, "synthetic send failure"):
            self.tracker.export(SCOPE, second, b"synthetic-second-export",
                                lambda _: (_ for _ in ()).throw(OSError("synthetic send failure")), head=h)
        self.assert_pending(second)
        self.assertEqual(len(self.record_data(second)["carriers"]), 1)

    def test_export_atomic_failure_never_calls_delivery(self):
        a = pi_auth()
        deliveries = []
        h = state()
        self.tracker.observe_head(SCOPE, h)
        with patch("wallet_epochs.os.replace", side_effect=OSError("injected export failure")):
            with self.assertRaises(OSError):
                self.tracker.export(SCOPE, a, b"synthetic-unsaved-export", deliveries.append, head=h)
        self.assertEqual(deliveries, [])
        self.assertEqual(self.tracker.records(SCOPE), {})
        with self.assertRaises(ValueError):
            self.tracker.export(SCOPE, a, b"synthetic-invalid-callback", None, head=h)
        self.assertEqual(self.tracker.records(SCOPE), {})

    def test_resubmission_cannot_erase_persisted_exposed_epoch(self):
        a = pi_auth()
        self.record(a)
        self.tracker.epochs.mark_compromised(SCOPE, 1, "persisted epoch is exposed")
        h = state()
        self.tracker.observe_head(SCOPE, h)
        after = replace(h, migration_nonce=2, commitment=a.commitment)
        self.assertFalse(self.tracker.resubmission_allowed(SCOPE, replace(a, epoch=None), h, after))
        with self.assertRaises(ValueError):
            self.tracker.resubmission_allowed(SCOPE, replace(a, epoch=2), h, after)
        self.assertEqual(self.record_data(a)["authorization"]["epoch"], 1)

    def test_resubmission_persists_newly_learned_exposed_epoch(self):
        a = pi_auth()
        self.record(replace(a, epoch=None))
        self.tracker.epochs.mark_compromised(SCOPE, 1, "known epoch, newly learned binding")
        h = state()
        self.tracker.observe_head(SCOPE, h)
        after = replace(h, migration_nonce=2, commitment=a.commitment)
        self.assertFalse(self.tracker.resubmission_allowed(SCOPE, a, h, after))
        reopened = AuthorizationTracker(self.temp.name)
        self.assertEqual(reopened.records(SCOPE)[a.group_id][a.variant_id]["authorization"]["epoch"], 1)
        self.assertFalse(reopened.resubmission_allowed(SCOPE, replace(a, epoch=None), h, after))

    def test_we20_range_repair_survives_restart_until_key_changes_or_range_catches_up(self):
        r = rotate(epoch=4)
        self.record(r)
        applied = state(migration_nonce=4, account_nonce=8,
                        activated=True, commitment=commitment(4))
        inclusion = (r.group_id, r.variant_id, hashlib.sha256(b"synthetic-carrier").hexdigest(), "APPLIED", 3)
        self.tracker.observe_head(SCOPE, applied, inclusions=[inclusion])
        # Finality may retire the authorization, but the current key remains
        # beyond the mnemonic scan range until a separate repair has applied.
        self.tracker.observe_finalized(SCOPE, FinalizedView(applied))
        self.tracker = AuthorizationTracker(self.temp.name)
        self.assertIn("OFFER_RANGE_REPAIR", self.actions(self.tracker.observe_head(SCOPE, applied)))
        different = replace(applied, block_hash="44" * 32, commitment=commitment(5))
        self.assertNotIn("OFFER_RANGE_REPAIR", self.actions(self.tracker.observe_head(SCOPE, different)))
        repaired = replace(applied, block_hash="55" * 32, migration_nonce=5)
        self.assertNotIn("OFFER_RANGE_REPAIR", self.actions(self.tracker.observe_head(SCOPE, repaired)))

    def test_known_commitment_exposure_also_bans_epoch_across_accounts_and_algorithms(self):
        a = pi_auth()
        self.record(a)
        self.tracker.mark_exposed(SCOPE, ACCOUNT, a.commitment, "known exposed synthetic key")
        self.assertIn(1, self.tracker.epochs.security(SCOPE).compromised_epochs)
        other_account = replace(ACCOUNT, chain_id=1, address="44" * 20)
        other = pi_auth(account=other_account)
        other_pi = bytearray(other.pi)
        other_pi[92] = 2
        other_pi[93:125] = commitment("other-algorithm-same-epoch")
        other = Authorization.from_pi(other_account, bytes(other_pi), epoch=1)
        self.record(other)
        notice = self.tracker.observe_head(SCOPE, state(account=other_account))
        self.assertEqual(notice["exposed_pending"], [(other.group_id, other.variant_id)])

    def test_late_epoch_discovery_propagates_previous_commitment_exposure(self):
        a = pi_auth()
        self.tracker.mark_exposed(SCOPE, ACCOUNT, a.commitment, "commitment known before derivation")
        self.record(replace(a, epoch=None))
        self.assertNotIn(1, self.tracker.epochs.security(SCOPE).compromised_epochs)
        notice = self.tracker.observe_head(SCOPE, state())
        self.assertEqual(notice["exposed_pending"], [(a.group_id, a.variant_id)])
        self.record(a, b"synthetic-later-epoch-discovery")
        self.assertIn(1, self.tracker.epochs.security(SCOPE).compromised_epochs)
        self.tracker = AuthorizationTracker(self.temp.name)
        self.assertEqual(self.record_data(a)["authorization"]["epoch"], 1)
        self.assertIn(1, self.tracker.epochs.security(SCOPE).compromised_epochs)

    def test_current_epoch_scan_reports_exposed_key_without_authorization_history(self):
        self.tracker.epochs.mark_compromised(SCOPE, 4, "record restored independently")
        h = state(migration_nonce=5, activated=True, commitment=commitment(4))
        notice = self.tracker.observe_head(SCOPE, h, current_epoch=4)
        self.assertTrue(notice["current_key_exposed"])
        self.assertEqual(notice["pending"], [])
        self.assertIn("REPLACE_EXPOSED_CURRENT_KEY_WITH_CONFIRMATION", self.actions(notice))


if __name__ == "__main__":
    unittest.main()
