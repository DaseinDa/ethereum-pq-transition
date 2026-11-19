"""Policy, key selection and monotonic persistence regressions using synthetic keys."""

from dataclasses import fields, replace
import hashlib
import hmac
import json
import multiprocessing
from pathlib import Path
import struct
import tempfile
import unittest
from unittest.mock import patch

from wallet_epochs import (
    CanonicalState, DerivationScope, HARDENED, MetadataError, SecurityKnowledge,
    UINT32_MAX, UINT64_MAX, WalletEpochStore, check5_gate, derive_epoch_seed,
    key_derivation_message, local_seed_identity, requires_new_authorization,
    revalidate_key_use, scan_above_bound, scan_current_key, select_new_key_epoch,
    same_key_step_forms, STEP_0x7E_OVERRIDE, STEP_0x7E_RECOMMIT, STEP_ACTIVATING_ROTATE, STEP_ROTATE,
)
from _test_epoch_reference import v118_selection_epoch

PATH = (44 | HARDENED, 60 | HARDENED, HARDENED, 0, 0)
SCOPE = DerivationScope("public-vector-seed-identity", PATH)


def commitment(epoch):
    # Deliberately a policy fixture, not an ML-DSA/security measurement.
    return hashlib.sha256(b"policy-fixture" + epoch.to_bytes(4, "big")).digest()


def state(m=0, current=None, **kwargs):
    values = dict(chain_id=13376, genesis_hash="11" * 32,
                  legacy_address="22" * 20, block_hash="33" * 32,
                  migration_nonce=m, status="LEGACY", activated=False,
                  commitment=None if current is None else commitment(current))
    values.update(kwargs)
    return CanonicalState(**values)


def proof_state(m, current, **kwargs):
    """A PQ_BY_PROOF state; the mode must agree with its commitment."""
    return state(m, current, status="PQ_BY_PROOF", **kwargs)


def _record_from_process(directory, epoch):
    WalletEpochStore(directory).mark_compromised(SCOPE, epoch, f"process {epoch}")


class EpochPolicyTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.store = WalletEpochStore(self.temporary.name)

    def test_first_key_and_nonce_not_local_high(self):
        self.assertEqual(select_new_key_epoch(SCOPE, state(), self.store).epoch, 0)
        orphan = proof_state(2, 1, block_hash="44" * 32)
        key = scan_current_key(SCOPE, orphan, commitment).current_key
        self.store.sync_canonical(SCOPE, orphan, key)
        # Simulate the old cache's orphaned maximum. It is never selection input.
        cache = json.loads(self.store.cache_path.read_text())
        cache["scopes"][SCOPE.key][orphan.cache_key]["e_high"] = 1
        self.store.cache_path.write_text(json.dumps(cache))
        reverted = proof_state(1, 0)
        self.assertEqual(select_new_key_epoch(SCOPE, reverted, self.store).epoch, 1)
        record = self.store.sync_canonical(SCOPE, reverted)
        self.assertIsNone(record["e_high"])
        self.assertIsNone(record["current_epoch"])
        self.assertEqual(record["migration_nonce"], 1)

    def test_same_anchor_keeps_only_verified_current(self):
        current = proof_state(2, 1)
        key = scan_current_key(SCOPE, current, commitment).current_key
        self.store.sync_canonical(SCOPE, current, key)
        self.assertEqual(self.store.sync_canonical(SCOPE, current)["current_epoch"], 1)
        changed = replace(current, block_hash="44" * 32)
        self.assertIsNone(self.store.sync_canonical(SCOPE, changed)["current_epoch"])
        with self.assertRaises(ValueError):
            self.store.sync_canonical(SCOPE, changed, key)

    def test_compromise_survives_reorg_restart_crosschain_and_algorithm(self):
        self.store.mark_compromised(SCOPE, 1, "orphan key was exposed")
        self.store.sync_canonical(SCOPE, proof_state(2, 1))
        before = self.store.security_path.read_bytes()
        self.store.sync_canonical(SCOPE, proof_state(1, 0))
        self.assertEqual(before, self.store.security_path.read_bytes())
        restarted = WalletEpochStore(self.temporary.name)
        for chain in (1, 13376, 999):
            foreign = proof_state(1, 0, chain_id=chain, genesis_hash="55" * 32,
                                  legacy_address="66" * 20)
            result = select_new_key_epoch(SCOPE, foreign, restarted)
            self.assertEqual(result.status, "BLOCKED")
            self.assertEqual(result.reason, "EPOCH_COMPROMISED")
        # The ledger has no algorithm dimension: a different registered
        # algorithm still cannot use the same banned epoch in this policy.
        self.assertIn(1, restarted.security(SCOPE).compromised_epochs)

    def test_path_and_seed_identity_are_distinct_scopes(self):
        other_path = DerivationScope(SCOPE.seed_identity, PATH[:-1] + (1,))
        other_seed = DerivationScope("different-local-seed-identity", PATH)
        self.store.mark_compromised(SCOPE, 0, "leaked")
        for other in (other_path, other_seed):
            self.assertEqual(select_new_key_epoch(other, state(), self.store).status, "SELECTED")
        self.assertEqual(select_new_key_epoch(SCOPE, state(), self.store).reason, "EPOCH_COMPROMISED")

    def test_mnemonic_only_restore_allows_scan_selection_and_key_use(self):
        current = proof_state(2, 1)
        recovered = scan_current_key(SCOPE, current, commitment)
        self.assertEqual(recovered.status, "MATCH")
        selected = select_new_key_epoch(SCOPE, current, self.store,
                                        current_key=recovered.current_key)
        self.assertEqual((selected.status, selected.epoch), ("SELECTED", 2))
        self.assertTrue(revalidate_key_use(SCOPE, current, self.store,
                                           recovered.current_key).allowed)
        self.assertEqual(self.store.security(SCOPE), SecurityKnowledge(frozenset(), 0))
        self.assertFalse(self.store.security_path.exists())
        # A partial record learned later refines choices; it gates nothing else.
        self.store.mark_compromised(SCOPE, 7, "partial recovered metadata")
        self.assertEqual(select_new_key_epoch(SCOPE, current, self.store).epoch, 2)
        self.assertEqual(self.store.security(SCOPE).compromised_epochs, frozenset({7}))

    def test_backup_restore_never_erases_bans(self):
        # One of the nine completeness tests of 31.6 rule 2; only the union is kept.
        self.store.mark_compromised(SCOPE, 1, "leak")
        older_backup = self.store.export_security_backup(SCOPE)
        self.store.mark_compromised(SCOPE, 2, "later leak")
        result = self.store.import_security_backup(SCOPE, older_backup, authenticated=True)
        self.assertEqual(result.compromised_epochs, frozenset({1, 2}))
        self.assertEqual(self.store.security(SCOPE).compromised_epochs, frozenset({1, 2}))

    def test_missing_security_file_does_not_use_canonical_cache_as_knowledge(self):
        self.store.mark_compromised(SCOPE, 5, "unrelated record, then the file is lost")
        self.store.sync_canonical(SCOPE, proof_state(1, 0))
        self.store.security_path.unlink()
        selected = select_new_key_epoch(SCOPE, proof_state(1, 0), self.store)
        self.assertEqual((selected.status, selected.epoch), ("SELECTED", 1))
        self.assertEqual(self.store.security(SCOPE), SecurityKnowledge(frozenset(), 0))

    def test_union_only_recording_and_corruption_fail_closed(self):
        self.store.mark_compromised(SCOPE, 1, "first leak report")
        self.store.mark_compromised(SCOPE, 2, "second leak report")
        self.store.mark_compromised(SCOPE, 1, "replacement must not erase first")
        record = json.loads(self.store.security_path.read_text())["scopes"][SCOPE.key]
        self.assertEqual(record["compromises"]["1"], "first leak report")
        self.assertEqual(self.store.security(SCOPE).compromised_epochs, frozenset({1, 2}))
        self.store.security_path.write_text("{broken", encoding="utf-8")
        with self.assertRaises(MetadataError):
            select_new_key_epoch(SCOPE, state(), self.store)

    def test_safe_same_key_recommit_is_only_offer(self):
        current = proof_state(1, 0)
        key = scan_current_key(SCOPE, current, commitment).current_key
        self.store.mark_compromised(SCOPE, 1, "orphan new key leaked")
        result = select_new_key_epoch(SCOPE, current, self.store, current_key=key)
        self.assertEqual((result.status, result.epoch), ("OFFER_SAME_KEY_RECOMMIT", 0))
        self.assertTrue(result.requires_new_authorization)
        # This module never executes a recommit or increments the chain nonce.
        self.assertEqual(current.migration_nonce, 1)
        self.assertEqual(self.store.sync_canonical(SCOPE, current)["migration_nonce"], 1)

    def test_same_key_step_offered_by_mode_and_not_for_a_compromised_current_key(self):
        # was test_recommit_not_offered_for_compromised_current_activated_or_wrong_mode,
        # which 31.2 rule 10 (d) names as changing with the same-key step from PQ_BY_ENROLL and as
        # a rotate. 'PQ_ENROLLED' is replaced by the mode of l. 97 (rule 10 (b)).
        self.store.mark_compromised(SCOPE, 1, "candidate leaked")
        expected = [
            # binding-final and activated: a rotate to the current key (rule 8 (a); ROT-D2)
            (proof_state(1, 0, activated=True), "OFFER_SAME_KEY_ROTATE", (STEP_ROTATE,)),
            # the owner's own enrolled key, override gate open (T unscheduled, l. 61): the same 0x7e
            # through the override gate, the early finalisation of l. 327
            (state(1, 0, status="PQ_BY_ENROLL"), "OFFER_SAME_KEY_RECOMMIT", (STEP_0x7E_OVERRIDE,)),
            # PQ_BY_ENROLL past its window, not activated: an activating 0x7c carrying the rotate
            (state(1, 0, status="PQ_BY_ENROLL", timestamp=900 + 100, fork_time=900, override_window=100,
                   enrolled_at=800), "OFFER_SAME_KEY_ROTATE", (STEP_ACTIVATING_ROTATE,)),
            # the re-commit gate: the 0x7e, or an activating 0x7c carrying the rotate (rule 8 (a), fourth form)
            (proof_state(1, 0), "OFFER_SAME_KEY_RECOMMIT", (STEP_0x7E_RECOMMIT, STEP_ACTIVATING_ROTATE)),
        ]
        for current, status, steps in expected:
            key = scan_current_key(SCOPE, current, commitment).current_key
            selected = select_new_key_epoch(SCOPE, current, self.store, current_key=key)
            self.assertEqual((selected.status, selected.epoch, selected.steps), (status, 0, steps))
        # Within the window the rotate's frame would revert (NOT_FINAL, l. 328): no rotate form; and an
        # unevaluated gate offers nothing.
        within = state(1, 0, status="PQ_BY_ENROLL", timestamp=900, fork_time=900, override_window=100,
                       enrolled_at=800)
        self.assertEqual(same_key_step_forms(within), (STEP_0x7E_OVERRIDE,))
        self.assertEqual(same_key_step_forms(state(1, 0, status="PQ_BY_ENROLL", fork_time=900)), ())
        current = proof_state(1, 0)
        key = scan_current_key(SCOPE, current, commitment).current_key
        self.store.mark_compromised(SCOPE, 0, "current also leaked")
        self.assertEqual(select_new_key_epoch(SCOPE, current, self.store,
                                              current_key=key).status, "BLOCKED")

    def test_unknown_current_does_not_offer_recommit(self):
        self.store.mark_compromised(SCOPE, 1, "candidate leaked")
        self.assertEqual(select_new_key_epoch(SCOPE, proof_state(1, 0),
                                              self.store).status, "BLOCKED")

    def test_epoch_u32_and_nonce_u64_boundaries(self):
        self.assertEqual(select_new_key_epoch(SCOPE, proof_state(UINT32_MAX, 0), self.store).epoch, UINT32_MAX)
        for m in (UINT32_MAX + 1, UINT64_MAX):
            self.assertEqual(select_new_key_epoch(SCOPE, proof_state(m, 0), self.store).reason,
                             "EPOCH_EXHAUSTED")
        for bad in (-1, UINT64_MAX + 1, True):
            with self.assertRaises(ValueError):
                state(bad)

    def test_compromised_last_epoch_cannot_recommit_to_escape_u32(self):
        self.store.mark_compromised(SCOPE, UINT32_MAX, "last epoch leaked")
        current = proof_state(UINT32_MAX, 0)
        key = scan_current_key(SCOPE, current, commitment, max_attempts=1).current_key
        self.assertEqual(select_new_key_epoch(SCOPE, current, self.store,
                                              current_key=key).status, "BLOCKED")

    def test_scan_budget_is_not_non_seed_verdict_and_resumes(self):
        current = proof_state(3, 2)
        one = scan_current_key(SCOPE, current, commitment, max_attempts=1)
        self.assertEqual(one.status, "INCOMPLETE")
        self.assertEqual(one.attempts_total, 1)
        two = scan_current_key(SCOPE, current, commitment, max_attempts=1, cursor=one.next_cursor)
        self.assertEqual(two.status, "INCOMPLETE")
        three = scan_current_key(SCOPE, current, commitment, max_attempts=1, cursor=two.next_cursor)
        self.assertEqual(three.status, "MATCH")
        self.assertEqual(three.current_key.epoch, 2)
        self.assertEqual(three.attempts_total, 3)
        with self.assertRaises(ValueError):
            scan_current_key(SCOPE, replace(current, block_hash="44" * 32),
                             commitment, cursor=one.next_cursor)

    def test_complete_nonmatch_and_scan_u32_cap(self):
        external = state(2, status="PQ_BY_PROOF", commitment=b"\xff" * 32)
        result = scan_current_key(SCOPE, external, commitment)
        self.assertEqual((result.status, result.attempts_total), ("NO_MATCH_WITHIN_BOUND", 2))
        huge = scan_current_key(SCOPE, state(UINT64_MAX, status="PQ_BY_PROOF", commitment=b"\xff" * 32),
                                commitment, max_attempts=1)
        self.assertEqual((huge.status, huge.upper_epoch), ("INCOMPLETE", UINT32_MAX))

        self.assertEqual(scan_current_key(SCOPE, state(), commitment).status, "NO_COMMITMENT")

    def test_epoch_zero_compatibility_and_epoch_domain_encoding(self):
        seed = bytes(range(64))
        expected = b"PQ-MIGRATE-v1/ML-DSA-44/" + struct.pack(">5I", *PATH)
        self.assertEqual(key_derivation_message("ML-DSA-44", PATH, 0), expected)
        self.assertEqual(derive_epoch_seed(seed, "ML-DSA-44", PATH, 0),
                         hmac.new(seed, expected, hashlib.sha512).digest()[:32])
        for epoch in (1, UINT32_MAX):
            self.assertEqual(key_derivation_message("ML-DSA-44", PATH, epoch),
                             expected + b"/" + struct.pack(">I", epoch))
        self.assertNotEqual(derive_epoch_seed(seed, "ML-DSA-44", PATH, 0),
                            derive_epoch_seed(seed, "ML-DSA-44", PATH, 1))

    def test_derivation_rejects_bad_inputs(self):
        for name in ("", "ML/DSA", "非ASCII"):
            with self.assertRaises(ValueError):
                key_derivation_message(name, PATH, 1)
        for path in (PATH[:-1], (44, *PATH[1:]), (*PATH[:2], 0, 0, 0),
                     (*PATH[:3], 2, 0), (*PATH[:4], HARDENED)):
            with self.assertRaises(ValueError):
                key_derivation_message("ML-DSA-44", path, 1)
        with self.assertRaises(ValueError):
            derive_epoch_seed(bytes(32), "ML-DSA-44", PATH, 1)
        with self.assertRaises(ValueError):
            key_derivation_message("ML-DSA-44", PATH, UINT32_MAX + 1)

    def test_commitment_or_nonce_change_requires_new_authorization(self):
        self.assertFalse(requires_new_authorization(1, commitment(0), 1, commitment(0)))
        self.assertTrue(requires_new_authorization(1, commitment(0), 1, commitment(1)))
        self.assertTrue(requires_new_authorization(1, commitment(0), 2, commitment(0)))

    def test_key_use_rechecks_compromise_and_exact_state(self):
        # One of the nine completeness tests of 31.6 rule 2, without the status.
        current = proof_state(1, 0)
        key = scan_current_key(SCOPE, current, commitment).current_key
        self.assertTrue(revalidate_key_use(SCOPE, current, self.store, key).allowed)
        for changed in (replace(current, block_hash="44" * 32),
                        replace(current, alg_id=2, alg_name="ML-DSA-65"),
                        replace(current, commitment=commitment(1))):
            self.assertEqual(revalidate_key_use(SCOPE, changed, self.store, key).reason,
                             "STALE_OR_UNVERIFIED_CURRENT_KEY")
        # A second store instance reports a leak after successful recovery.
        second = WalletEpochStore(self.temporary.name)
        second.mark_compromised(SCOPE, 0, "leak learned after recovery")
        self.assertEqual(revalidate_key_use(SCOPE, current, self.store, key).reason,
                         "CURRENT_KEY_COMPROMISED")

    def test_two_store_instances_union_latest_disk_records(self):
        second = WalletEpochStore(self.temporary.name)
        self.assertEqual(second.security(SCOPE).compromised_epochs, frozenset())
        self.store.mark_compromised(SCOPE, 1, "first process")
        second.mark_compromised(SCOPE, 2, "second process")
        self.store.mark_compromised(SCOPE, 3, "first process again")
        self.assertEqual(second.security(SCOPE).compromised_epochs, frozenset({1, 2, 3}))

    def test_concurrent_processes_do_not_drop_compromise_reports(self):
        context = multiprocessing.get_context("spawn")
        processes = [context.Process(target=_record_from_process,
                                     args=(self.temporary.name, epoch)) for epoch in range(4)]
        for process in processes:
            process.start()
        try:
            for process in processes:
                process.join(15)
                self.assertEqual(process.exitcode, 0)
        finally:
            for process in processes:
                if process.is_alive():
                    process.terminate()
                    process.join()
        self.assertEqual(self.store.security(SCOPE).compromised_epochs, frozenset(range(4)))

    def test_failed_atomic_write_preserves_previous_security_state(self):
        self.store.mark_compromised(SCOPE, 1, "durable report")
        before = self.store.security_path.read_bytes()
        with patch("wallet_epochs.os.replace", side_effect=OSError("injected rename failure")):
            with self.assertRaises(OSError):
                self.store.mark_compromised(SCOPE, 2, "uncommitted report")
        self.assertEqual(self.store.security_path.read_bytes(), before)
        self.assertEqual(self.store.security(SCOPE).compromised_epochs, frozenset({1}))
        self.assertEqual(list(Path(self.temporary.name).glob("*.tmp")), [])

    def test_authenticated_backup_restores_union_only(self):
        # One of the nine completeness tests of 31.6 rule 2; only the union is kept.
        self.store.mark_compromised(SCOPE, 1, "known when backup made")
        backup = self.store.export_security_backup(SCOPE)
        self.assertNotIn("knowledge", backup)
        self.store.mark_compromised(SCOPE, 2, "later local leak")
        with self.assertRaises(MetadataError):
            self.store.import_security_backup(SCOPE, backup, authenticated=False)
        knowledge = self.store.import_security_backup(SCOPE, backup, authenticated=True)
        self.assertEqual(knowledge.compromised_epochs, frozenset({1, 2}))

    def test_backup_for_another_scope_is_rejected(self):
        # Formerly test_unknown_backup_cannot_upgrade_completeness; the scope check stays.
        backup = self.store.export_security_backup(SCOPE)
        wrong = {**backup, "scope_key": "ff" * 32}
        with self.assertRaises(MetadataError):
            self.store.import_security_backup(SCOPE, wrong, authenticated=True)
        self.assertFalse(self.store.security_path.exists())

    def test_stale_backup_import_cannot_erase_later_records(self):
        # Formerly test_stale_completeness_assessment_cannot_erase_later_unknown.
        self.store.mark_compromised(SCOPE, 1, "backup-known leak")
        backup = self.store.export_security_backup(SCOPE)
        second = WalletEpochStore(self.temporary.name)
        second.mark_compromised(SCOPE, 3, "learned by another process after the backup")
        result = self.store.import_security_backup(SCOPE, backup, authenticated=True)
        self.assertEqual(result.compromised_epochs, frozenset({1, 3}))
        self.assertEqual(select_new_key_epoch(SCOPE, state(), self.store).status, "SELECTED")
        self.assertEqual(select_new_key_epoch(SCOPE, proof_state(1, 0), self.store).reason,
                         "EPOCH_COMPROMISED")
        self.assertEqual(select_new_key_epoch(SCOPE, proof_state(3, 0), self.store).reason,
                         "EPOCH_COMPROMISED")

    def test_stale_import_unions_bans_and_duplicate_events_advance_revision(self):
        backup = self.store.export_security_backup(SCOPE)
        backup["compromises"]["7"] = "authenticated remote report"
        self.store.mark_compromised(SCOPE, 3, "local report")
        revision = self.store.security(SCOPE).revision
        self.store.mark_compromised(SCOPE, 3, "duplicate still counts as a mutation")
        self.assertEqual(self.store.security(SCOPE).revision, revision + 1)
        result = self.store.import_security_backup(SCOPE, backup, authenticated=True)
        self.assertEqual(result.compromised_epochs, frozenset({3, 7}))
        self.assertEqual(result.revision, revision + 2)
        self.assertEqual(self.store.export_security_backup(SCOPE)["revision"], result.revision)

    def test_legacy_knowledge_field_promotes_nothing(self):
        # Formerly test_complete_backup_requires_explicit_local_revision: the
        # promotion is not adopted, so a COMPLETE label changes nothing.
        backup = {"schema": 1, "scope_key": SCOPE.key, "knowledge": "COMPLETE",
                  "compromises": {"4": "remote report"}, "revision": 9}
        result = self.store.import_security_backup(SCOPE, backup, authenticated=True)
        self.assertEqual(result, SecurityKnowledge(frozenset({4}), 1))
        record = json.loads(self.store.security_path.read_text())["scopes"][SCOPE.key]
        self.assertNotIn("knowledge", record)

    def test_seed_identity_is_local_deterministic_and_not_chain_scoped(self):
        public_seed = bytes(range(64))
        identity = local_seed_identity(public_seed)
        self.assertEqual(identity, local_seed_identity(public_seed))
        self.assertNotEqual(identity, local_seed_identity(bytes(reversed(range(64)))))
        self.assertEqual(len(identity), 64)
        with self.assertRaises(ValueError):
            local_seed_identity(bytes(32))

    def test_unknown_history_preserves_known_exclusions_after_restart(self):
        self.store.mark_compromised(SCOPE, 1, "known exposed candidate")
        restarted = WalletEpochStore(self.temporary.name)
        self.assertEqual(select_new_key_epoch(SCOPE, proof_state(1, 0), restarted).reason,
                         "EPOCH_COMPROMISED")
        current = proof_state(2, 1)
        key = scan_current_key(SCOPE, current, commitment).current_key
        self.assertEqual(revalidate_key_use(SCOPE, current, restarted, key).reason,
                         "CURRENT_KEY_COMPROMISED")
        self.assertEqual(select_new_key_epoch(SCOPE, current, restarted).epoch, 2)
        self.assertEqual(restarted.security(SCOPE).compromised_epochs, frozenset({1}))

    def test_unknown_history_with_record_allows_unrecorded_current_key(self):
        self.store.mark_compromised(SCOPE, 3, "another exposed epoch")
        current = proof_state(1, 0)
        key = scan_current_key(SCOPE, current, commitment).current_key
        self.assertTrue(revalidate_key_use(SCOPE, current, self.store, key).allowed)
        self.assertEqual(select_new_key_epoch(SCOPE, current, self.store).epoch, 1)

    def test_unknown_history_may_offer_safe_recommit_without_erasing_record(self):
        self.store.mark_compromised(SCOPE, 1, "recorded candidate after restore")
        current = proof_state(1, 0)
        key = scan_current_key(SCOPE, current, commitment).current_key
        selected = select_new_key_epoch(SCOPE, current, self.store, current_key=key)
        self.assertEqual((selected.status, selected.epoch),
                         ("OFFER_SAME_KEY_RECOMMIT", 0))
        self.assertEqual(self.store.security(SCOPE).compromised_epochs, frozenset({1}))

    def test_corrupt_record_is_not_absent_record_for_d1(self):
        current = proof_state(1, 0)
        key = scan_current_key(SCOPE, current, commitment).current_key
        self.store.security_path.write_text("{invalid", encoding="utf-8")
        with self.assertRaises(MetadataError):
            select_new_key_epoch(SCOPE, current, self.store)
        with self.assertRaises(MetadataError):
            revalidate_key_use(SCOPE, current, self.store, key)


class Rule10aTests(unittest.TestCase):
    """31.2 rule 10 (a): no completeness status, no promotion, no first-use acknowledgement."""

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.store = WalletEpochStore(self.temporary.name)

    def test_rule10a_no_completeness_status_or_first_use_acknowledgement(self):
        for name in ("initialize_new_wallet", "mark_knowledge_unknown"):
            self.assertFalse(hasattr(WalletEpochStore, name), name)
        self.assertEqual([f.name for f in fields(SecurityKnowledge)], ["compromised_epochs", "revision"])
        # A first use selects epoch 0 with no call before it and leaves no record.
        self.assertEqual(select_new_key_epoch(SCOPE, state(), self.store).epoch, 0)
        self.assertEqual(self.store.security(SCOPE), SecurityKnowledge(frozenset(), 0))
        self.assertFalse(self.store.security_path.exists())

    def test_rule10a_record_of_2026_10_26_is_read_and_its_status_dropped(self):
        legacy = {"schema": 1, "scopes": {SCOPE.key: {"knowledge": "COMPLETE",
                                                      "compromises": {"2": "old report"}, "revision": 4}}}
        self.store.security_path.write_text(json.dumps(legacy), encoding="utf-8")
        self.assertEqual(self.store.security(SCOPE), SecurityKnowledge(frozenset({2}), 4))
        self.store.mark_compromised(SCOPE, 5, "new report")
        record = json.loads(self.store.security_path.read_text())["scopes"][SCOPE.key]
        self.assertEqual(record, {"compromises": {"2": "old report", "5": "new report"}, "revision": 5})
        broken = {"schema": 1, "scopes": {SCOPE.key: {"knowledge": "MAYBE", "compromises": {}, "revision": 0}}}
        self.store.security_path.write_text(json.dumps(broken), encoding="utf-8")
        with self.assertRaises(MetadataError):
            self.store.security(SCOPE)


class Rule10bTests(unittest.TestCase):
    """31.2 rule 10 (b): the four modes of l. 97 with activated and the frozen predicate."""

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.store = WalletEpochStore(self.temporary.name)

    def test_rule10b_mode_metadata_is_validated(self):
        for bad in ("PQ_ENROLLED", "", "pq_by_proof", "FROZEN", 2, None):
            with self.subTest(status=bad), self.assertRaises(ValueError):
                state(1, 0, status=bad)
        invalid = [
            dict(m=0, status="LEGACY", activated=True),
            dict(m=0, current=0, status="LEGACY"),
            dict(m=1, status="LEGACY"),
            dict(m=0, status="LEGACY", enrolled_at=5),
            dict(m=0, status="LEGACY", code_kind="PQ_MARKER"),
            dict(m=1, status="PQ_BY_PROOF"),
            dict(m=0, current=0, status="PQ_BY_PROOF"),
            dict(m=1, current=0, status="PQ_BY_PROOF", activated=True, code_kind="EMPTY"),
            dict(m=1, current=0, status="PQ_BY_ENROLL", code_kind="DELEGATION"),
            dict(m=1, current=0, status="PQ_NATIVE"),
            dict(m=1, current=0, status="PQ_NATIVE", activated=True, enrolled_at=7),
            dict(m=1, current=0, status="PQ_BY_PROOF", code_kind="CONTRACT"),
        ]
        for values in invalid:
            with self.subTest(**{k: str(v) for k, v in values.items()}), self.assertRaises(ValueError):
                state(**values)
        for values in (dict(m=0), dict(m=0, code_kind="DELEGATION"), dict(m=0, code_kind="OTHER"),
                       dict(m=1, current=0, status="PQ_BY_ENROLL", enrolled_at=80),
                       dict(m=1, current=0, status="PQ_BY_ENROLL", activated=True),
                       dict(m=2, current=1, status="PQ_BY_PROOF"),
                       dict(m=1, current=0, status="PQ_NATIVE", activated=True)):
            with self.subTest(**{k: str(v) for k, v in values.items()}):
                state(**values)

    def test_rule10b_frozen_predicate_is_derived_from_the_bound_state(self):
        frozen = state(timestamp=100, fork_time=100)
        self.assertIs(frozen.is_frozen, True)
        self.assertIs(state(timestamp=99, fork_time=100).is_frozen, False)
        self.assertIs(state(timestamp=100, fork_time=None).is_frozen, False)  # T unscheduled
        self.assertIs(state(timestamp=None, fork_time=100).is_frozen, None)   # not evaluable
        self.assertIs(state(timestamp=200, fork_time=100, code_kind="DELEGATION").is_frozen, True)
        self.assertIs(state(timestamp=200, fork_time=100, code_kind="OTHER").is_frozen, False)
        self.assertIs(proof_state(1, 0, timestamp=200, fork_time=100).is_frozen, False)

    def test_rule10b_pq_native_is_excluded_from_selection_and_scan(self):
        native = state(1, 0, status="PQ_NATIVE", activated=True)
        calls = []

        def derive(epoch):
            calls.append(epoch)
            return commitment(epoch)

        self.assertEqual(select_new_key_epoch(SCOPE, native, self.store).status, "NOT_APPLICABLE")
        self.assertEqual(select_new_key_epoch(SCOPE, native, self.store).reason, "PQ_NATIVE")
        self.assertFalse(self.store.cache_path.exists())
        self.assertEqual(scan_current_key(SCOPE, native, derive).status, "NOT_SCANNED_PQ_NATIVE")
        self.assertEqual(scan_above_bound(SCOPE, native, derive, owner_request=True).status,
                         "NOT_SCANNED_PQ_NATIVE")
        self.assertEqual(calls, [])

    def test_rule10b_legacy_scan_is_no_commitment_without_derivation(self):
        calls = []
        result = scan_current_key(SCOPE, state(), lambda e: calls.append(e) or commitment(e))
        self.assertEqual((result.status, result.attempts_total, result.current_key), ("NO_COMMITMENT", 0, None))
        self.assertEqual(calls, [])


class Rule10cTests(unittest.TestCase):
    """31.2 rule 10 (c): check 5 evaluated from the bound state, in the order of l. 1159-1161."""

    def test_rule10c_check5_gate_from_bound_state(self):
        T, W = 1000, 300
        cases = [
            (proof_state(1, 0), ("RECOMMIT", "RECOMMIT_GATE_OPEN")),
            (proof_state(1, 0, activated=True), (None, "ALREADY_MIGRATED")),
            (state(1, 0, status="PQ_NATIVE", activated=True), (None, "ALREADY_MIGRATED")),
            (state(1, 0, status="PQ_BY_ENROLL"), ("OVERRIDE", "OVERRIDE_GATE_OPEN")),  # T unscheduled
            (state(1, 0, status="PQ_BY_ENROLL", timestamp=T + W - 1, fork_time=T,
                   override_window=W, enrolled_at=900), ("OVERRIDE", "OVERRIDE_GATE_OPEN")),
            (state(1, 0, status="PQ_BY_ENROLL", timestamp=T + W, fork_time=T,
                   override_window=W, enrolled_at=900), (None, "OVERRIDE_WINDOW_CLOSED")),
            (state(1, 0, status="PQ_BY_ENROLL", activated=True, timestamp=T + 1, fork_time=T,
                   override_window=W, enrolled_at=900), ("OVERRIDE", "OVERRIDE_GATE_OPEN")),
            (state(1, 0, status="PQ_BY_ENROLL", timestamp=T + 1, fork_time=T, override_window=W,
                   enrolled_at=T + 50), ("OVERRIDE", "OVERRIDE_GATE_OPEN")),
            (state(1, 0, status="PQ_BY_ENROLL", fork_time=T, override_window=W, enrolled_at=900),
             (None, "STATE_GATE_UNEVALUATED")),
            (state(timestamp=T + 5, fork_time=T, code_kind="OTHER"), (None, "NOT_AN_EOA")),
            (state(timestamp=T - 1, fork_time=T), (None, "FORK_NOT_ACTIVE")),
            (state(timestamp=T + 5), (None, "FORK_NOT_ACTIVE")),  # T unscheduled
            (state(timestamp=T, fork_time=T), ("FROZEN", "FROZEN_GATE_OPEN")),
            (state(timestamp=T, fork_time=T, code_kind="DELEGATION"), ("FROZEN", "FROZEN_GATE_OPEN")),
            (state(fork_time=T), (None, "STATE_GATE_UNEVALUATED")),
            (state(1, 0, status="PQ_BY_ENROLL", timestamp=UINT64_MAX, fork_time=UINT64_MAX - 5,
                   override_window=10, enrolled_at=0), ("OVERRIDE", "OVERRIDE_GATE_OPEN")),
        ]
        for value, expected in cases:
            with self.subTest(status=value.status, timestamp=value.timestamp, fork_time=value.fork_time):
                self.assertEqual(check5_gate(value), expected)

    def test_rule10c_anchor_binds_the_check5_inputs(self):
        base = proof_state(2, 1, timestamp=500, fork_time=400, override_window=60, enrolled_at=0)
        key = scan_current_key(SCOPE, base, commitment).current_key
        self.assertTrue(key.matches(SCOPE, base))
        for changed in (replace(base, timestamp=501), replace(base, fork_time=None),
                        replace(base, override_window=61), replace(base, enrolled_at=None)):
            with self.subTest(changed=changed):
                self.assertNotEqual(changed.anchor, base.anchor)
                self.assertFalse(key.matches(SCOPE, changed))


class Rule10gTests(unittest.TestCase):
    """31.2 rule 10 (g): vector WE-2 with the v1.18 selection run, not a constant."""

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.store = WalletEpochStore(self.temporary.name)

    def test_rule10g_we2_v118_selection_with_retained_e_high(self):
        derived = []

        def derive(epoch):
            derived.append(epoch)
            return commitment(epoch)

        b1 = proof_state(1, 0, block_hash="b1" * 32)
        self.assertEqual(select_new_key_epoch(SCOPE, b1, self.store).epoch, 1)
        b2 = proof_state(2, 1, block_hash="b2" * 32)          # the re-commit to C_1 included
        cached = scan_current_key(SCOPE, b2, derive).current_key
        self.store.sync_canonical(SCOPE, b2, cached)           # W caches epoch 1 bound to B2
        b2_prime = proof_state(1, 0, block_hash="c2" * 32)    # a child of B1 without it
        # (i) The cached epoch is discarded and rule 2 gives e = 1, never 2.
        self.assertIsNone(self.store.sync_canonical(SCOPE, b2_prime)["current_epoch"])
        self.assertEqual(select_new_key_epoch(SCOPE, b2_prime, self.store).epoch, 1)
        # (ii) The v1.18 selection with the retained e_high = 1 selects 2.
        e = v118_selection_epoch(b2_prime, e_high=cached.epoch)
        self.assertEqual(e, 2)
        included = proof_state(2, e, block_hash="c3" * 32)    # its 0x7e at nonce 1 included
        derived.clear()
        within = scan_current_key(SCOPE, included, derive)
        self.assertEqual((within.status, within.upper_epoch, within.attempts_total),
                         ("NO_MATCH_WITHIN_BOUND", 1, 2))
        self.assertEqual(derived, [0, 1])
        above = scan_above_bound(SCOPE, included, derive, owner_request=True)
        self.assertEqual((above.status, above.current_key.epoch, above.attempts_total),
                         ("MATCH_ABOVE_BOUND", 2, 3))   # MATCH_ABOVE_BOUND e = 2 at the third
        self.assertEqual(derived, [0, 1, 2])
        self.assertFalse(above.current_key.matches(SCOPE, included))  # U is unchanged
        # The other branches of the historical rule, for completeness.
        self.assertEqual(v118_selection_epoch(b2_prime, e_high=None), 1)
        self.assertEqual(v118_selection_epoch(b2_prime, e_high=None, knows_no_seed_key_committed=True), 0)

    def test_above_bound_aid_needs_the_owner_and_never_reuses_an_in_bound_cursor(self):
        current = proof_state(2, 1)
        with self.assertRaises(ValueError):
            scan_above_bound(SCOPE, current, commitment, owner_request=False)
        inbound = scan_current_key(SCOPE, proof_state(3, 2), commitment, max_attempts=1)
        with self.assertRaises(ValueError):
            scan_above_bound(SCOPE, proof_state(3, 2), commitment, owner_request=True,
                             cursor=inbound.next_cursor)
        external = proof_state(UINT32_MAX - 1, 0, commitment=b"\xff" * 32)
        step = scan_above_bound(SCOPE, external, commitment, owner_request=True, max_attempts=1)
        self.assertEqual((step.status, step.next_cursor.next_epoch), ("INCOMPLETE", UINT32_MAX))
        last = scan_above_bound(SCOPE, external, commitment, owner_request=True, cursor=step.next_cursor)
        self.assertEqual((last.status, last.attempts_total), ("NO_MATCH_ABOVE_BOUND", UINT32_MAX + 1))
        exhausted = proof_state(UINT32_MAX + 1, 0, commitment=b"\xff" * 32)
        self.assertEqual(scan_above_bound(SCOPE, exhausted, commitment, owner_request=True).status,
                         "NO_MATCH_ABOVE_BOUND")


if __name__ == "__main__":
    unittest.main(verbosity=2)
