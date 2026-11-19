"""Wallet model regressions for key exposure, revocation, payload planning and export.

Covers reorganization, retained authorizations, finality, sponsored carriers,
payload ordering, canonical-head changes, epoch selection and same-key steps.
Keys, carriers and states are synthetic. ModelCrypto signs with SHA-256 rather
than ML-DSA so signing decisions are observable. The independent test codec
checks canonical RLP and PI construction. No proof, node or network runs here.
"""
from dataclasses import fields, replace
import hashlib
import importlib.util
import inspect
from pathlib import Path
import sys
import tempfile
import unittest

import authorization_tracking as at
import wallet
import wallet_epochs
from authorization_tracking import (
    Account, AccountState, Authorization, AuthorizationTracker, FinalizedView, binding_conditions_allow,
)
from wallet_epochs import (
    CanonicalState, DerivationScope, HARDENED, WalletEpochStore, local_seed_identity,
    revalidate_key_use, scan_current_key,
)

SEED = bytes(range(64))  # Public synthetic fixture, never a user's seed.
PATH = (44 | HARDENED, 60 | HARDENED, HARDENED, 0, 0)
SCOPE = DerivationScope(local_seed_identity(SEED), PATH)
ACCOUNT = Account(13376, "11" * 32, "22" * 20)
W = 365 * 24 * 3600
DOMAIN = bytes.fromhex("44" * 32)
VERSION = 0x80000005
EXPIRY = 5000
FEE = 20000000
CONFIG = {"chain_id": 13376, "domain_tag": "44" * 32, "verifier_version": VERSION,
          "max_priority_fee_per_gas": 2, "max_fee_per_gas": 3, "migration_gas_limit": 6000000}
ACTIVATION_CONFIG = dict(chain_id=13376, recipient="77" * 20, max_priority_fee_per_gas=10**8,
                         max_fee_per_gas=2 * 10**9, pq_transaction_gas_limit=1_000_000)
ACTIVATION_LABEL = "OFFER_CURRENT_KEY_ACTIVATION_DO_NOT_ADVANCE_MIGRATION_NONCE"
COMBINED_LABEL = "OFFER_FINALIZING_ACTIVATION_OR_ADVANCE_PAST_PI_NONCE"
BUNDLE_LABEL = "OFFER_ONE_PAYLOAD_BUNDLE"
_CANONICAL_FIELDS = {f.name for f in fields(CanonicalState)}


def canonical_state(*args, **kwargs):
    """A CanonicalState; keyword fields that the loaded class does not define are left out."""
    return CanonicalState(*args, **{k: v for k, v in kwargs.items() if k in _CANONICAL_FIELDS})


class ModelCrypto:
    """Deterministic SHA model of the helper's pk/hash/sign/verify operations; not ML-DSA."""

    def __init__(self):
        self.seeds = {}

    @staticmethod
    def _signature(seed, message, ctx):
        return hashlib.sha256(b"model-signature" + seed + message + ctx).digest()

    def __call__(self, op, *args):
        if op == "pk":
            pk = (hashlib.sha512(args[0]).digest() * 21)[:1312]
            self.seeds[pk] = args[0]
            return pk
        if op == "hash":
            return hashlib.sha256(args[0]).digest()
        if op == "sign":
            return self._signature(*args)
        raise AssertionError(op)

    def text(self, op, *args):
        if op != "verify":
            raise AssertionError(op)
        pk, message, ctx, signature = args
        seed = self.seeds.get(pk)
        return "true" if seed is not None and signature == self._signature(seed, message, ctx) else "false"


def key_commitment(label):
    return hashlib.sha256(b"regression-key:" + label.encode()).digest()


def pi_auth(nonce, commitment, *, epoch=None, expiry=EXPIRY):
    """A complete-length synthetic layout-2 PI of ACCOUNT; not a valid migration proof."""
    pi = bytearray(198)
    pi[:32] = ACCOUNT.chain_id.to_bytes(32, "big")
    pi[32:64] = DOMAIN
    pi[64:84] = bytes.fromhex(ACCOUNT.address)
    pi[84:92] = nonce.to_bytes(8, "big")
    pi[92] = 1
    pi[93:125] = commitment
    pi[125:129] = VERSION.to_bytes(4, "big")
    pi[129:137] = expiry.to_bytes(8, "big")
    return Authorization.from_pi(ACCOUNT, bytes(pi), epoch=epoch)


def sponsored(auth):
    """The same PI with fee_mode 2 (zero-reimbursement third-party submission,
    section 19.2): only a sponsored carrier or a 0x7f entry carries it, and a's balance pays nothing."""
    pi = bytearray(auth.pi)
    pi[169] = 2
    return Authorization.from_pi(auth.account, bytes(pi), epoch=auth.epoch)


# (34.2 rule 1 (g)): a write that left the device and was included on an earlier
# branch is in a block, so A holds it; recording alone no longer says so. A before side drops the keyword.
IN_BLOCK = {"custody": "IN_BLOCK"}
# (34.2 rule 1 (f)): the caller's statement that a's balance pays the act after the precursor has
# taken all that its carrier allows (the adapter's 0x7e has fee mode 0). A before side drops the keyword.
BALANCE = {"balance_covers_acts": True}


def own_kw():
    """(spec 38.3 rule 1, S-12): an override that a pays, in the override of an enrollment whose key another
    party holds, needs the caller's statement that the wallet has no sponsored path to offer and the owner's
    confirmation of the displayed warning (own_funds_warning, for ACCOUNT, FEE and VERSION). A side without them gets
    no keyword."""
    if not hasattr(wallet, "own_funds_warning"):
        return {}
    token = wallet.own_funds_warning(legacy_address=ACCOUNT.address, max_account_fee=FEE, verifier_version=VERSION)
    return {"no_sponsored_path": True, "confirm_own_funds": token["token"]}


def own_funds():
    """(31.2 rule 10 (e); l. 252, l. 417): the owner's explicit own-funds choice (fee mode 0, layout 2). In the
    override case of an enrolled key that another party holds the wallet no longer chooses own ETH by itself
    (FEE_CHOICE_REQUIRED); a test of that case that means W's self-paid override says so. A side without FeeChoice
    gets no keyword (its prepare_recovery fixed mode 0). With own_kw(), the statement that no sponsored path
    exists and the owner's confirmation of the warning (spec 38.3 rule 1)."""
    return {"fee": wallet.FeeChoice(), **own_kw()} if hasattr(wallet, "FeeChoice") else {}


def head(**kwargs):
    values = dict(account=ACCOUNT, block_hash="b1" * 32, number=20, timestamp=2000,
                  migration_nonce=1, account_nonce=5, mode="PQ_BY_PROOF", activated=False,
                  commitment=key_commitment("k0"), fork_time=900, override_window=W, enrolled_at=0)
    values.update(kwargs)
    return AccountState(**values)


def frozen_head(**kwargs):
    return head(mode="LEGACY", migration_nonce=0, commitment=None, **kwargs)


def override_head(**kwargs):
    # A stealth enrollment of another key (C_ext) with the override window open.
    values = dict(mode="PQ_BY_ENROLL", migration_nonce=1, commitment=key_commitment("ext"), enrolled_at=950)
    values.update(kwargs)
    return head(**values)


def offer_for(notice, auth):
    return next(o for o in notice["offers"] if o.get("variant") == auth.variant_id)


def actions_for(notice, auth):
    return [o["action"] for o in notice["offers"] if o.get("variant") == auth.variant_id]


class Base(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.store = WalletEpochStore(self.tmp.name)
        self.tracker = AuthorizationTracker(self.tmp.name)
        self.crypto = ModelCrypto()
        self.keys = {e: wallet.derive_key(SCOPE, SEED, e, self.crypto) for e in range(6)}
        self.sent = []

    def ledger(self):
        # A fresh instance: the epoch must be on disk, not only in memory.
        return sorted(WalletEpochStore(self.tmp.name).security(SCOPE).compromised_epochs)

    def canonical(self, nonce, epoch, block):
        return CanonicalState(13376, "11" * 32, "22" * 20, block * 32, nonce,
                              status="PQ_BY_PROOF", commitment=self.keys[epoch].commitment)

    def frozen_state(self, block="f1"):
        return canonical_state(13376, "11" * 32, "22" * 20, block * 32, 0,
                               timestamp=2000, fork_time=900, override_window=W)

    def head_for(self, state, *, account_nonce=0, number=20, timestamp=2000):
        """The tracker's AccountState of the bound block of `state`."""
        return AccountState(ACCOUNT, state.block_hash, number, getattr(state, "timestamp", None) or timestamp,
                            state.migration_nonce, account_nonce, state.status, state.activated,
                            state.commitment, getattr(state, "fork_time", None),
                            getattr(state, "override_window", None) or W, getattr(state, "enrolled_at", None) or 0)

    def learned_pi(self, nonce, epoch, *, expiry=EXPIRY, with_epoch=False):
        """Another device's PI at `nonce` committing C_epoch, as learned on chain (no epoch)."""
        at_nonce = self.canonical(nonce, 0, "e0") if nonce else self.frozen_state("e0")
        pi = wallet._pi(at_nonce, self.keys[epoch], DOMAIN, VERSION, expiry, FEE)
        return Authorization.from_pi(ACCOUNT, pi, epoch=epoch if with_epoch else None)

    def plan(self, state, **extra):
        return wallet.prepare_recovery(SCOPE, state, self.store, SEED, self.crypto, tracker=self.tracker,
                                       domain_tag=DOMAIN, verifier_version=VERSION, expiry=EXPIRY,
                                       max_account_fee=FEE, **extra)

    def export_kwargs(self, plan, h, **extra):
        return dict(head=h, proof=b"MODEL-PROOF-NOT-REAL", journal=plan.pi, config=CONFIG,
                    verify_proof=lambda proof, pi: True, deliver=self.sent.append,
                    seed64=SEED, crypto=self.crypto, **extra)

    def signed(self, epoch, nonce, reveal):
        """The 0x7c that the adapter signs with K_epoch at `nonce`; signed_pq verifies it itself."""
        key = self.keys[epoch]
        record = {"public_test_seed": key.xi.hex(), "public_key": key.public_key.hex()}
        raw, row = wallet.wire.signed_pq(self.crypto, ACTIVATION_CONFIG, bytes.fromhex(ACCOUNT.address),
                                         record, nonce, 0, reveal)
        self.assertTrue(row["signature_verified"])
        return raw

    def probe_a_setup(self):
        """The review's probe A: C_1's key is exposed by commitment only, through an
        epoch-less PI learned on chain; the head is nonce 2 with C_1, not activated."""
        at_nonce1 = self.canonical(1, 0, "a1")
        learned = Authorization.from_pi(ACCOUNT, wallet._pi(at_nonce1, self.keys[1], DOMAIN, VERSION, EXPIRY, FEE))
        self.tracker.record(SCOPE, learned, b"learned-on-chain-carrier")
        self.tracker.mark_exposed(SCOPE, ACCOUNT, self.keys[1].commitment, "device 2 compromised; held the key of C_1")
        state = self.canonical(2, 1, "a2")
        scan = scan_current_key(SCOPE, state, lambda e: self.keys[e].commitment)
        self.assertEqual((scan.status, scan.current_key.epoch), ("MATCH", 1))
        self.assertEqual(self.ledger(), [])  # mark_exposed alone cannot link: no epoch was known
        return state, scan.current_key


class D1Tests(Base):
    """U2 D-1: a commitment-level exposure must reach the epoch ledger and the signers."""

    def test_d1_observe_head_links_commitment_exposure_to_the_scanned_epoch(self):
        state, key = self.probe_a_setup()
        h = head(block_hash="a2" * 32, number=12, timestamp=1000, migration_nonce=2, account_nonce=0,
                 commitment=self.keys[1].commitment)
        notice = self.tracker.observe_head(SCOPE, h, current_epoch=key.epoch)
        self.assertTrue(notice["current_key_exposed"])
        self.assertEqual(self.ledger(), [1])
        self.assertEqual(revalidate_key_use(SCOPE, state, self.store, key).reason, "CURRENT_KEY_COMPROMISED")

    def test_d1_sign_activation_refuses_commitment_exposed_current_key(self):
        state, key = self.probe_a_setup()
        with self.assertRaisesRegex(ValueError, "CURRENT_KEY_COMPROMISED"):
            wallet.sign_activation(SCOPE, state, self.store, key, SEED, self.crypto, ACTIVATION_CONFIG,
                                   tracker=self.tracker, head=self.head_for(state), transaction_nonce=0)
        self.assertEqual(self.ledger(), [1])  # persisted before the refusal

    def test_d1_prepare_recommit_refuses_commitment_exposed_current_key(self):
        state, key = self.probe_a_setup()
        self.store.mark_compromised(SCOPE, 2, "the next epoch is recorded, so a same-key step is offered")
        with self.assertRaisesRegex(ValueError, "CURRENT_KEY_COMPROMISED"):
            wallet.prepare_recommit(SCOPE, state, self.store, key, SEED, self.crypto, tracker=self.tracker,
                                    domain_tag=DOMAIN, verifier_version=VERSION, expiry=EXPIRY,
                                    max_account_fee=FEE, confirm_extra_proof_and_fee=True)
        self.assertEqual(self.ledger(), [1, 2])

    def test_d1_signers_require_the_tracker_of_the_epoch_store(self):
        # Guards the new interface: the old signer, with tracker= dropped, signs correctly here.
        state = self.canonical(1, 0, "a1")
        key = scan_current_key(SCOPE, state, lambda e: self.keys[e].commitment).current_key
        other = AuthorizationTracker(Path(self.tmp.name) / "other")
        for tracker, reason in ((other, "TRACKER_SECURITY_STORE_MISMATCH"), (None, "AUTHORIZATION_TRACKER_REQUIRED")):
            with self.subTest(reason=reason), self.assertRaisesRegex(ValueError, reason):
                wallet.sign_activation(SCOPE, state, self.store, key, SEED, self.crypto, ACTIVATION_CONFIG,
                                       tracker=tracker, head=self.head_for(state), transaction_nonce=0)

    def test_d1_unexposed_current_key_still_signs_control(self):
        state = self.canonical(1, 0, "a1")
        key = scan_current_key(SCOPE, state, lambda e: self.keys[e].commitment).current_key
        h = self.head_for(state)
        self.tracker.observe_head(SCOPE, h)
        raw, row = wallet.sign_activation(SCOPE, state, self.store, key, SEED, self.crypto, ACTIVATION_CONFIG,
                                          tracker=self.tracker, head=h, transaction_nonce=0)
        self.assertEqual(raw[0], 0x7C)
        self.assertTrue(row["signature_verified"])
        self.assertEqual(self.ledger(), [])


class D2Tests(Base):
    """U2 D-2: offers depend on the PI's nonce position; new exports apply the revival check."""

    def track_exposed_leaf(self, nonce=2, epoch=2):
        leaf = Authorization.from_pi(ACCOUNT, wallet._pi(self.canonical(nonce, 0, "b0"), self.keys[epoch],
                                                         DOMAIN, VERSION, EXPIRY, FEE), epoch=epoch)
        self.tracker.record(SCOPE, leaf, b"leaf-P-carried-in-a-0x7f")
        self.store.mark_compromised(SCOPE, epoch, "leaf key exposed")
        return leaf

    def test_d2_future_nonce_pi_offers_only_the_activation_in_the_recommit_gate(self):
        leaf = self.track_exposed_leaf()
        offer = offer_for(self.tracker.observe_head(SCOPE, head(commitment=self.keys[0].commitment)), leaf)
        self.assertEqual(offer["action"], ACTIVATION_LABEL)
        self.assertIs(offer["advance_migration_nonce"], False)
        self.assertEqual(offer["pi_nonce_position"], "ABOVE_HEAD")

    def test_d2_future_nonce_pi_with_exposed_current_key_follows_rule_7b_8b(self):
        leaf = self.track_exposed_leaf()
        self.tracker.mark_exposed(SCOPE, ACCOUNT, self.keys[0].commitment, "current key exposed too")
        notice = self.tracker.observe_head(SCOPE, head(commitment=self.keys[0].commitment))
        offer = offer_for(notice, leaf)
        self.assertEqual(offer["action"], "FOLLOW_RULE_7B_8B_PATH_WITH_WARNING")
        self.assertEqual(offer["reason"], "CURRENT_KEY_EXPOSED")
        self.assertIs(offer["advance_migration_nonce"], False)
        self.assertTrue(notice["current_key_exposed"])

    def test_d2_pi_consumed_at_the_head_waits_for_finality(self):
        leaf = self.track_exposed_leaf()
        # The leaf applied on this branch: nonce 3 with its exposed key C_2 current.
        notice = self.tracker.observe_head(SCOPE, head(migration_nonce=3, commitment=self.keys[2].commitment))
        offer = offer_for(notice, leaf)
        self.assertEqual(offer["action"], "WAIT_FINALITY_WATCH_REORG")
        self.assertEqual(offer["pi_nonce_position"], "BELOW_HEAD")
        self.assertEqual(notice["offers"][0]["action"], "REPLACE_EXPOSED_CURRENT_KEY_WITH_CONFIRMATION")
        self.assertNotIn(COMBINED_LABEL, {o["action"] for o in notice["offers"]})

    def test_d2_pi_at_the_head_nonce_keeps_the_combined_offer_control(self):
        leaf = self.track_exposed_leaf()
        offer = offer_for(self.tracker.observe_head(SCOPE, head(migration_nonce=2)), leaf)
        self.assertEqual(offer["action"], COMBINED_LABEL)

    def test_d2_new_export_is_refused_when_it_revives_an_exposed_pi(self):
        # WE-16 shape: head at nonce 1 in the re-commit gate, exposed leaf P at nonce 2.
        leaf = self.track_exposed_leaf()
        s1 = self.canonical(1, 0, "b1")
        h1 = head(fork_time=None, commitment=self.keys[0].commitment)   # s1 reads T as unscheduled
        self.tracker.observe_head(SCOPE, h1)
        plan = self.plan(s1)
        self.assertEqual(plan.key.epoch, 1)
        export = self.export_kwargs(plan, h1)
        with self.assertRaisesRegex(ValueError, "REVIVES_EXPOSED_AUTHORIZATION") as caught:
            wallet.export_recovery(plan, SCOPE, s1, self.store, self.tracker, **export)
        self.assertEqual(self.sent, [])
        new_write = Authorization.from_pi(ACCOUNT, plan.pi)
        self.assertNotIn(new_write.group_id, self.tracker.records(SCOPE))
        warning = caught.exception
        self.assertIsInstance(warning, at.RevivalWarning)
        self.assertEqual(warning.revived, [[leaf.group_id, leaf.variant_id]])
        self.assertEqual(warning.remedy, "ACTIVATE_CURRENT_KEY_FIRST")
        # Only the owner's explicit confirmation of this warning delivers it alone.
        with self.assertRaises(at.RevivalWarning):
            wallet.export_recovery(plan, SCOPE, s1, self.store, self.tracker, confirm_revival="00" * 32, **export)
        wallet.export_recovery(plan, SCOPE, s1, self.store, self.tracker, confirm_revival=warning.token, **export)
        self.assertEqual(len(self.sent), 1)

    def test_d2_tracker_export_applies_the_revival_check(self):
        leaf = self.track_exposed_leaf()
        h1 = head(commitment=self.keys[0].commitment)
        self.tracker.observe_head(SCOPE, h1)
        same_key = pi_auth(1, self.keys[0].commitment, epoch=0)   # a same-key step at nonce 1
        with self.assertRaisesRegex(ValueError, "REVIVES_EXPOSED_AUTHORIZATION") as caught:
            self.tracker.export(SCOPE, same_key, b"same-key-step", self.sent.append, head=h1)
        self.assertEqual(self.sent, [])
        self.assertNotIn(same_key.group_id, self.tracker.records(SCOPE))
        self.tracker.export(SCOPE, same_key, b"same-key-step", self.sent.append, head=h1,
                            confirm_revival=caught.exception.token)
        self.assertEqual(self.sent, [b"same-key-step"])
        self.assertTrue(binding_conditions_allow(leaf, replace(h1, migration_nonce=2)))

    def test_d2_export_without_revival_is_delivered_control(self):
        h1 = head(commitment=self.keys[0].commitment)
        self.tracker.observe_head(SCOPE, h1)
        write = pi_auth(1, self.keys[1].commitment, epoch=1)
        self.tracker.export(SCOPE, write, b"ordinary-write", self.sent.append, head=h1)
        self.assertEqual(self.sent, [b"ordinary-write"])


class GuardTests(Base):
    """U2 guard gaps: (a) an unscheduled T, (b) the preview of a write alone."""

    def test_guard_a_unscheduled_T_is_an_open_override_gate(self):
        h = frozen_head(fork_time=None, timestamp=1000, account_nonce=0)    # LEGACY before an unscheduled T
        enrollment = Authorization(ACCOUNT, "ENROLL", 0, key_commitment("k0"), epoch=0)
        override_pi = pi_auth(1, key_commitment("k1"), epoch=1)
        self.tracker.record(SCOPE, enrollment, b"own-0x7d-E")
        self.tracker.record(SCOPE, override_pi, b"exposed-override-PI")
        self.tracker.mark_exposed(SCOPE, ACCOUNT, override_pi.commitment, "override key exposed")
        after_e = replace(h, mode="PQ_BY_ENROLL", migration_nonce=1, account_nonce=1,
                          commitment=enrollment.commitment, enrolled_at=h.timestamp)
        self.assertTrue(binding_conditions_allow(override_pi, after_e))   # l. 61: no finite deadline(a)
        self.tracker.observe_head(SCOPE, h)
        self.assertFalse(self.tracker.resubmission_allowed(SCOPE, enrollment, h, after_e))

    def test_guard_b_preview_must_be_the_candidate_alone(self):
        h = frozen_head()
        s = pi_auth(0, key_commitment("k0"), epoch=0)
        leaf = pi_auth(1, key_commitment("k2"), epoch=2)
        self.tracker.record(SCOPE, s, b"frozen-recovery-S")
        self.tracker.record(SCOPE, leaf, b"tracked-leaf-P")
        self.tracker.epochs.mark_compromised(SCOPE, 2, "leaf key exposed")
        self.tracker.observe_head(SCOPE, h)
        after_s = replace(h, mode="PQ_BY_PROOF", migration_nonce=1, commitment=s.commitment)
        self.assertFalse(self.tracker.resubmission_allowed(SCOPE, s, h, after_s))
        after_s_and_activation = replace(after_s, activated=True, account_nonce=h.account_nonce + 1)
        with self.assertRaisesRegex(ValueError, "PREVIEW_NOT_CANDIDATE_ALONE"):
            self.tracker.resubmission_allowed(SCOPE, s, h, after_s_and_activation)


class OnePayloadTests(Base):
    """Review item 3.1: the write at the current nonce goes with the act that follows it."""

    def setup_gate(self, h, leaf_nonce):
        # S is the owner's write that left the device on an earlier branch and can still be
        # included at the head, so A may hold it (spec 34.2 rule 1 (b)); without a tracked
        # carrier S would be a fresh precursor, which rule 1 (g) holds back.
        s = pi_auth(h.migration_nonce, key_commitment("k-own"), epoch=h.migration_nonce)
        leaf = pi_auth(leaf_nonce, key_commitment("k-leaf"), epoch=7)
        self.tracker.record(SCOPE, s, b"write-S", **IN_BLOCK)
        self.tracker.record(SCOPE, leaf, b"tracked-leaf-P")
        self.tracker.epochs.mark_compromised(SCOPE, 7, "leaf key exposed")
        return s, leaf

    def bundle(self, h, *elements):
        return at.OnePayloadBundle(h, elements)

    def write(self, auth, carrier):
        return at.PayloadElement("WRITE", carrier, authorization=auth)

    def activation(self, commitment, account_nonce):
        return at.PayloadElement("ACTIVATION", b"activation-0x7c", commitment=commitment, account_nonce=account_nonce)

    def check_gate_bundle(self, h, label):
        s, leaf = self.setup_gate(h, h.migration_nonce + 1)
        offer = offer_for(self.tracker.observe_head(SCOPE, h), leaf)
        self.assertEqual(offer["action"], "OFFER_ONE_PAYLOAD_BUNDLE", label)
        self.assertIs(offer["advance_migration_nonce_alone"], False)
        self.assertTrue(offer["payload"]["one_payload"] and offer["payload"]["race"])
        # The write alone revives the leaf; it is not withheld but offered as one payload.
        with self.assertRaises(at.RevivalWarning) as caught:
            self.tracker.export(SCOPE, s, b"write-S", self.sent.append, head=h)
        self.assertEqual(caught.exception.remedy, "ONE_PAYLOAD_BUNDLE")
        revived = [[leaf.group_id, leaf.variant_id]]
        # The act past the PI's nonce is a sponsored write (fee mode 2, section 19.2; 34.2 rule 1 (f)).
        past_nonce = sponsored(pi_auth(h.migration_nonce + 1, s.commitment, epoch=h.migration_nonce))
        with_write = self.bundle(h, self.write(s, b"write-S"), self.write(past_nonce, b"write-past-P"))
        preview = self.tracker.bundle_preview(SCOPE, with_write)
        self.assertEqual(preview["revived_between_elements"], revived)
        self.assertEqual(preview["end_state"]["migration_nonce"], h.migration_nonce + 2)
        self.assertTrue(preview["race"])
        if h.mode == "LEGACY":
            # The frozen gate: the activation of the key the write commits is the act.
            act = self.bundle(h, self.write(s, b"write-S"), self.activation(s.commitment, h.account_nonce))
            preview = self.tracker.bundle_preview(SCOPE, act, **BALANCE)
            self.assertEqual(preview["revived_between_elements"], revived)
            self.assertTrue(preview["end_state"]["activated"])
            expected = (b"write-S", b"activation-0x7c")
        else:
            # (spec 34.2 rule 1 (f)): in the override gate of A's enrollment the act
            # is the sponsored write past the PI's nonce; test_r3_v22w2_iii_... covers the refusal
            # of the activation there.
            act, expected = with_write, (b"write-S", b"write-past-P")
        payloads = []
        self.tracker.export_bundle(SCOPE, act, payloads.append, **BALANCE)
        self.assertEqual(payloads, [expected])
        self.assertIn(s.variant_id, self.tracker.records(SCOPE)[s.group_id])
        self.assertEqual(self.sent, [])

    def test_item31_frozen_gate_write_goes_with_the_following_act_as_one_payload(self):
        self.check_gate_bundle(frozen_head(), "frozen gate")

    def test_item31_override_gate_write_goes_with_the_following_act_as_one_payload(self):
        self.check_gate_bundle(override_head(), "override gate")

    def test_item31_unscheduled_T_override_gate_is_bundled(self):
        self.check_gate_bundle(override_head(fork_time=None), "override gate, T unscheduled")

    def test_item31_split_delivery_is_refused(self):
        h = frozen_head()
        s, leaf = self.setup_gate(h, 1)
        self.tracker.observe_head(SCOPE, h)
        # Before any bundle exists. ValueError, which RevivalWarning subclasses.
        with self.assertRaises(ValueError) as caught:
            self.tracker.export(SCOPE, s, b"write-S", self.sent.append, head=h)
        self.assertEqual(self.sent, [])
        token = getattr(caught.exception, "token", None)
        bundle = self.bundle(h, self.write(s, b"write-S"), self.activation(s.commitment, h.account_nonce))
        payloads = []
        self.tracker.export_bundle(SCOPE, bundle, payloads.append, **BALANCE)
        self.assertEqual(len(payloads), 1)
        # After bundling, the write does not leave alone without the stated gap, whatever token.
        for confirm in (None, token, "00" * 32):
            with self.subTest(confirm=confirm), self.assertRaises(ValueError):
                self.tracker.export(SCOPE, s, b"write-S", self.sent.append, head=h, confirm_revival=confirm)
        after_s = replace(h, mode="PQ_BY_PROOF", migration_nonce=1, commitment=s.commitment)
        self.assertFalse(self.tracker.resubmission_allowed(SCOPE, s, h, after_s))
        end = replace(after_s, activated=True, account_nonce=h.account_nonce + 1)
        with self.assertRaisesRegex(ValueError, "PREVIEW_NOT_CANDIDATE_ALONE"):
            self.tracker.resubmission_allowed(SCOPE, s, h, end)
        # A bundle is one payload through a private relay, and starts with its write.
        with self.assertRaisesRegex(ValueError, "SPLIT_ROUTE_REFUSED"):
            at.OnePayloadBundle(h, bundle.elements, route="PUBLIC_MEMPOOL")
        for elements in (bundle.elements[:1], bundle.elements[::-1]):
            with self.assertRaises(ValueError):
                at.OnePayloadBundle(h, elements)
        self.assertEqual(self.sent, [])
        # A bundle is prepared again after every change of the head.
        self.tracker.observe_head(SCOPE, replace(h, block_hash="c1" * 32, number=21))
        with self.assertRaisesRegex(ValueError, "stale or unobserved bundle head"):
            self.tracker.export_bundle(SCOPE, bundle, payloads.append, **BALANCE)
        self.assertEqual(len(payloads), 1)

    def test_item31_bundle_refuses_exposed_keys_inapplicable_order_and_a_live_end_state(self):
        h = frozen_head()
        s, leaf = self.setup_gate(h, 2)          # the leaf needs nonce 2
        self.tracker.observe_head(SCOPE, h)
        same_key = pi_auth(1, s.commitment, epoch=0)
        # S then a same-key write at 1 ends at nonce 2 in the re-commit gate: P stays live.
        with self.assertRaisesRegex(ValueError, "BUNDLE_REVIVES_EXPOSED_AUTHORIZATION"):
            self.tracker.bundle_preview(SCOPE, self.bundle(h, self.write(s, b"write-S"), self.write(same_key, b"w1")))
        # Elements apply in payload order only.
        with self.assertRaisesRegex(ValueError, "BUNDLE_ELEMENT_NOT_APPLICABLE"):
            self.tracker.bundle_preview(SCOPE, self.bundle(h, self.write(same_key, b"w1"), self.write(s, b"write-S")))
        with self.assertRaisesRegex(ValueError, "BUNDLE_ELEMENT_NOT_APPLICABLE"):
            self.tracker.bundle_preview(SCOPE, self.bundle(h, self.write(s, b"write-S"),
                                                           self.activation(s.commitment, h.account_nonce + 1)))
        # No write of an exposed key is bundled, whichever record shows the exposure:
        # its own recorded epoch, another tracked authorization's recorded epoch for
        # the same commitment, or a commitment-level exposure.
        exposed_write = pi_auth(0, key_commitment("k-exposed"), epoch=9)
        self.tracker.epochs.mark_compromised(SCOPE, 9, "exposed")
        epochless = pi_auth(0, key_commitment("k-shared"))
        self.tracker.record(SCOPE, pi_auth(5, key_commitment("k-shared"), epoch=8), b"same key, epoch known")
        self.tracker.epochs.mark_compromised(SCOPE, 8, "exposed")
        self.tracker.mark_exposed(SCOPE, ACCOUNT, s.commitment, "own key exposed meanwhile")
        self.tracker.observe_head(SCOPE, h)
        for write in (exposed_write, epochless, s):
            with self.subTest(commitment=write.commitment.hex()[:8]), \
                    self.assertRaisesRegex(ValueError, "BUNDLE_ELEMENT_KEY_EXPOSED: element 0"):
                self.tracker.bundle_preview(SCOPE, self.bundle(h, self.write(write, b"w"),
                                                               self.activation(write.commitment, h.account_nonce)))

    def test_r2_split_delivery_needs_the_stated_gap_and_a_token_bound_to_bundle_and_head(self):
        """The split depends on spec 34.2 rule 1 (c), not on bundle history."""
        h = frozen_head()
        s, leaf = self.setup_gate(h, 1)
        self.tracker.observe_head(SCOPE, h)
        bundle = self.bundle(h, self.write(s, b"write-S"), self.activation(s.commitment, h.account_nonce))
        payloads = []
        self.tracker.export_bundle(SCOPE, bundle, payloads.append, **BALANCE)     # the automatic path
        self.assertEqual(payloads, [(b"write-S", b"activation-0x7c")])
        # The relay did not include it. The caller states that no path gives one payload: the wallet
        # states the gap, and only the owner's confirmation of that gap sends it alone.
        h2 = replace(h, block_hash="c2" * 32, number=21)
        self.tracker.observe_head(SCOPE, h2)
        with self.assertRaisesRegex(ValueError, "NO_ONE_PAYLOAD_PATH") as stated:
            self.tracker.export(SCOPE, s, b"write-S", self.sent.append, head=h2, no_one_payload_path=True)
        self.assertEqual(self.sent, [])
        with self.assertRaises(ValueError) as plain:        # without the statement, no token is offered
            self.tracker.export(SCOPE, s, b"write-S", self.sent.append, head=h2)
        self.assertIsNone(plain.exception.token)
        self.tracker.export(SCOPE, s, b"write-S", self.sent.append, head=h2, no_one_payload_path=True,
                            confirm_revival=stated.exception.token)
        self.assertEqual(self.sent, [b"write-S"])
        # The pair split: the stated gap, then a token bound to the bundle and the head.
        moved = self.bundle(h2, *bundle.elements)
        with self.assertRaisesRegex(ValueError, "NO_ONE_PAYLOAD_PATH") as caught:
            self.tracker.export_bundle(SCOPE, moved, payloads.append, no_one_payload_path=True, **BALANCE)
        warning = caught.exception
        self.assertEqual(warning.revived_between, [[leaf.group_id, leaf.variant_id]])
        with self.assertRaises(ValueError):
            self.tracker.export_bundle(SCOPE, moved, payloads.append, no_one_payload_path=True,
                                       confirm_split="00" * 32, **BALANCE)
        self.tracker.export_bundle(SCOPE, moved, payloads.append, no_one_payload_path=True,
                                   confirm_split=warning.token, **BALANCE)
        self.assertEqual(payloads[1:], [(b"write-S",), (b"activation-0x7c",)])
        # At a new head the same bundle needs a new confirmation.
        h3 = replace(h, block_hash="c3" * 32, number=22)
        self.tracker.observe_head(SCOPE, h3)
        with self.assertRaisesRegex(ValueError, "NO_ONE_PAYLOAD_PATH"):
            self.tracker.export_bundle(SCOPE, self.bundle(h3, *bundle.elements), payloads.append,
                                       no_one_payload_path=True, confirm_split=warning.token, **BALANCE)
        self.assertEqual(len(payloads), 3)


class ExposureEpochRecordTests(Base):
    """A record by epoch reaches an authorization learned without one."""

    def test_r2_v22w1_epoch_record_reaches_a_learned_pi_in_the_frozen_gate(self):
        # V22-W-1: P, another device's re-commit at nonce 1 committing C_1, learned on chain; W records epoch 1.
        p = self.learned_pi(1, 1)
        self.tracker.record(SCOPE, p, b"P-of-another-device-learned-on-chain")
        self.store.mark_compromised(SCOPE, 1, "W records epoch 1")
        state = self.frozen_state()
        h = self.head_for(state, account_nonce=7)
        self.tracker.observe_head(SCOPE, h)
        plan = self.plan(state)   # the adapter links every recorded epoch to its commitment first
        self.assertEqual(plan.key.epoch, 0)
        # S, W's frozen recovery of branch 1, left the device and can still be included
        # (V22-W-1); without it, the recovery would be a fresh precursor (draft 34.2 rule 1 (g)).
        self.tracker.record(SCOPE, Authorization.from_pi(ACCOUNT, plan.pi, epoch=0), b"S-of-branch-1", **IN_BLOCK)
        self.assertEqual(actions_for(self.tracker.observe_head(SCOPE, h), p), [BUNDLE_LABEL])
        with self.assertRaises(ValueError) as caught:
            wallet.export_recovery(plan, SCOPE, state, self.store, self.tracker, **self.export_kwargs(plan, h))
        self.assertEqual(self.sent, [])
        self.assertEqual(getattr(caught.exception, "remedy", None), "ONE_PAYLOAD_BUNDLE")
        self.assertEqual(getattr(caught.exception, "revived", None), [[p.group_id, p.variant_id]])

    def test_r2_v22w2_epoch_record_reaches_a_learned_pi_in_the_override_gate(self):
        # V22-W-2: A's stealth enrollment C_ext at nonce 1; P, another device's re-commit at nonce 2
        # committing C_2, learned on chain; W records epoch 2; W's override S commits C_1.
        c_ext = key_commitment("ext")
        state = canonical_state(13376, "11" * 32, "22" * 20, "f2" * 32, 1, status="PQ_BY_ENROLL",
                                commitment=c_ext, timestamp=2000, fork_time=900, override_window=W,
                                enrolled_at=850)
        h = AccountState(ACCOUNT, "f2" * 32, 31, 2000, 1, 7, "PQ_BY_ENROLL", False, c_ext, 900, W, 850)
        p = self.learned_pi(2, 2)
        self.tracker.record(SCOPE, p, b"P-of-another-device-learned-on-chain")
        self.store.mark_compromised(SCOPE, 2, "W records epoch 2")
        self.tracker.observe_head(SCOPE, h)
        plan = self.plan(state, **own_funds())
        self.assertEqual(plan.key.epoch, 1)
        # S, W's override of branch 1, left the device and can still be included (V22-W-2).
        self.tracker.record(SCOPE, Authorization.from_pi(ACCOUNT, plan.pi, epoch=1), b"S-of-branch-1", **IN_BLOCK)
        self.assertEqual(actions_for(self.tracker.observe_head(SCOPE, h), p), [BUNDLE_LABEL])
        with self.assertRaises(ValueError) as caught:
            wallet.export_recovery(plan, SCOPE, state, self.store, self.tracker, **self.export_kwargs(plan, h))
        self.assertEqual(self.sent, [])
        self.assertEqual(getattr(caught.exception, "remedy", None), "ONE_PAYLOAD_BUNDLE")

    def test_r2_we16_epoch_record_reaches_a_learned_leaf(self):
        # WE-16 with the leaf learned from a 0x7f entry (no epoch); W records epoch 2.
        p = self.learned_pi(2, 2)
        self.tracker.record(SCOPE, p, b"leaf-P-learned-from-a-0x7f-entry")
        self.store.mark_compromised(SCOPE, 2, "W records epoch 2")
        s1 = self.canonical(1, 0, "b1")
        h1 = head(fork_time=None, commitment=self.keys[0].commitment)
        self.tracker.observe_head(SCOPE, h1)
        plan = self.plan(s1)
        self.assertEqual(actions_for(self.tracker.observe_head(SCOPE, h1), p), [ACTIVATION_LABEL])
        with self.assertRaises(ValueError) as caught:
            wallet.export_recovery(plan, SCOPE, s1, self.store, self.tracker, **self.export_kwargs(plan, h1))
        self.assertEqual(self.sent, [])
        self.assertEqual(getattr(caught.exception, "remedy", None), "ACTIVATE_CURRENT_KEY_FIRST")
        # The exposed write itself is never resubmitted (31.2 rule 9 (a)).
        self.assertFalse(self.tracker.resubmission_allowed(SCOPE, p, h1))

    def test_r2_remedy_follows_an_epoch_recorded_current_key(self):
        # probe_remedy_epoch_only: the current key K_0 is recorded by epoch only.
        leaf = pi_auth(2, key_commitment("k2"), epoch=2)
        self.tracker.record(SCOPE, leaf, b"tracked-leaf-P")
        self.store.mark_compromised(SCOPE, 2, "leaf key exposed")
        self.store.mark_compromised(SCOPE, 0, "current key K_0 exposed (record by epoch)")
        h = head(commitment=key_commitment("k0"))
        notice = self.tracker.observe_head(SCOPE, h, current_epoch=0)   # a scan found K_0 at epoch 0
        self.assertTrue(notice["current_key_exposed"])
        self.assertEqual(offer_for(notice, leaf)["reason"], "CURRENT_KEY_EXPOSED")
        with self.assertRaises(ValueError) as caught:
            self.tracker.export(SCOPE, pi_auth(1, key_commitment("k1"), epoch=1), b"N", self.sent.append, head=h)
        self.assertEqual(self.sent, [])
        self.assertEqual(getattr(caught.exception, "remedy", None), "FOLLOW_RULE_7B_8B_PATH")

    def test_r2_a_same_key_variant_with_its_epoch_exposes_an_epochless_variant(self):
        # Two devices select epoch 1 at nonce 1 (31.2 rule 2): W's own O (expired at the head)
        # carries the epoch, the other device's O' (live) does not; epoch 1 is recorded.
        h = frozen_head()
        own = pi_auth(1, key_commitment("k1"), epoch=1, expiry=1500)
        other = pi_auth(1, key_commitment("k1"), expiry=5000)
        s = pi_auth(0, key_commitment("k0"), epoch=0)
        self.tracker.record(SCOPE, own, b"O")
        self.tracker.record(SCOPE, other, b"O-prime")
        self.store.mark_compromised(SCOPE, 1, "K_1 exposed")
        notice = self.tracker.observe_head(SCOPE, h)
        self.assertIn((other.group_id, other.variant_id), notice["exposed_pending"])
        with self.assertRaises(ValueError):
            self.tracker.export(SCOPE, s, b"S", self.sent.append, head=h)
        self.assertEqual(self.sent, [])

    def test_r2_the_bundle_end_state_sees_the_epoch_record_of_a_learned_pi(self):
        # probe_bundle_epochless: P (nonce 2, C_2) learned without its epoch; W records epoch 2.
        p = self.learned_pi(2, 2)
        self.tracker.record(SCOPE, p, b"P-learned")
        self.store.mark_compromised(SCOPE, 2, "W records epoch 2")
        state = self.frozen_state()
        h = self.head_for(state, account_nonce=7)
        self.tracker.observe_head(SCOPE, h)
        plan = self.plan(state)
        s = Authorization.from_pi(ACCOUNT, plan.pi, epoch=0)
        # S of branch 1 is in a block; a fresh S would wait (34.2 rule 1 (g)).
        self.tracker.record(SCOPE, s, b"S-of-branch-1", **IN_BLOCK)
        step = {m: Authorization.from_pi(ACCOUNT, wallet._pi(self.canonical(m, 0, "e1"), self.keys[0], DOMAIN,
                                                             VERSION, EXPIRY, FEE), epoch=0) for m in (1, 2)}
        write = lambda auth: at.PayloadElement("WRITE", b"carrier-%d" % auth.nonce, authorization=auth)
        with self.assertRaisesRegex(ValueError, "BUNDLE_REVIVES_EXPOSED_AUTHORIZATION"):
            self.tracker.bundle_preview(SCOPE, at.OnePayloadBundle(h, (write(s), write(step[1]))))
        end = self.tracker.bundle_preview(SCOPE, at.OnePayloadBundle(h, (write(s), write(step[1]), write(step[2]))),
                                          **BALANCE)
        self.assertEqual(end["end_state"]["migration_nonce"], 3)

    def test_r2_the_adapter_links_recorded_epochs_and_learned_authorizations(self):
        h = frozen_head(account_nonce=7)
        # The owner's frozen recovery at nonce 0 left the device and can still be included,
        # so the offer for P is the one payload at once (draft 34.2 rule 1 (b), not the wait of (g)).
        self.tracker.record(SCOPE, self.learned_pi(0, 0, with_epoch=True), b"S-of-branch-1", **IN_BLOCK)
        # A new-key PI learned at migration nonce 1 was selected at e = 1 (31.2 rule 2).
        p = self.learned_pi(1, 1)
        wallet.learn_authorization(SCOPE, SEED, self.crypto, self.store, self.tracker, p, b"P-learned")
        self.assertEqual(self.tracker.records(SCOPE)[p.group_id][p.variant_id]["authorization"]["epoch"], 1)
        self.store.mark_compromised(SCOPE, 1, "recorded after P was learned")
        self.assertEqual(actions_for(self.tracker.observe_head(SCOPE, h), p), [BUNDLE_LABEL])
        # A record made before any link reaches an epoch-less authorization once the adapter observes the head.
        q = self.learned_pi(2, 2)
        self.tracker.record(SCOPE, q, b"Q-recorded-without-the-adapter")
        self.store.mark_compromised(SCOPE, 2, "recorded by epoch")
        self.assertEqual(actions_for(self.tracker.observe_head(SCOPE, h), q), [])
        notice = wallet.observe_head(SCOPE, SEED, self.crypto, self.store, self.tracker, h)
        self.assertIn((q.group_id, q.variant_id), notice["exposed_pending"])
        self.assertEqual(wallet.link_recorded_epochs(SCOPE, SEED, self.crypto, self.store, self.tracker), [])


class ExposureActivationTests(Base):
    """An activation can revive a tracked non-activating rotate at the next account nonce."""

    def rotate_setup(self, with_pi=False):
        n = 5
        state = self.canonical(1, 0, "c1")
        h = head(block_hash="c1" * 32, number=30, timestamp=3000, account_nonce=n,
                 commitment=self.keys[0].commitment, fork_time=None)
        r = Authorization(ACCOUNT, "ROTATE", n + 1, self.keys[3].commitment, activating=False,
                          signer_commitment=self.keys[0].commitment, epoch=3)
        self.tracker.record(SCOPE, r, b"orphaned-0x7c-at-n+1-signed-by-K0-rotating-to-K3")
        self.store.mark_compromised(SCOPE, 3, "xi_3 reported leaked")
        p = None
        if with_pi:
            p = Authorization.from_pi(ACCOUNT, wallet._pi(self.canonical(2, 0, "c0"), self.keys[2], DOMAIN,
                                                          VERSION, EXPIRY, FEE), epoch=2)
            self.tracker.record(SCOPE, p, b"leaf-P-nonce-2")
            self.store.mark_compromised(SCOPE, 2, "xi_2 reported leaked")
        key = scan_current_key(SCOPE, state, lambda e: self.keys[e].commitment).current_key
        self.tracker.observe_head(SCOPE, h)
        return state, h, r, key, p

    def test_r2_an_activation_that_revives_a_tracked_rotate_is_refused(self):
        state, h, r, key, _ = self.rotate_setup()
        with self.assertRaises(ValueError) as caught:
            wallet.sign_activation(SCOPE, state, self.store, key, SEED, self.crypto, ACTIVATION_CONFIG,
                                   tracker=self.tracker, head=h, transaction_nonce=5)
        warning = caught.exception
        self.assertEqual(getattr(warning, "remedy", None), "ONE_PAYLOAD_BUNDLE")
        self.assertEqual(warning.revived, [[r.group_id, r.variant_id]])
        self.assertIsNone(warning.token)   # no lone activation without the stated gap
        self.assertEqual(warning.payload["first"], "ACTIVATION_OR_ACTIVATING_ROTATE_AT_ACCOUNT_NONCE")
        self.assertEqual(warning.payload["through_account_nonce"], 6)
        offer = offer_for(self.tracker.observe_head(SCOPE, h), r)
        self.assertEqual((offer["action"], offer["account_nonce_position"]), (BUNDLE_LABEL, "ABOVE_HEAD"))
        # Rule 1 (c) for the activation: stated gap, then the owner's confirmation of it.
        with self.assertRaisesRegex(ValueError, "NO_ONE_PAYLOAD_PATH") as stated:
            wallet.sign_activation(SCOPE, state, self.store, key, SEED, self.crypto, ACTIVATION_CONFIG,
                                   tracker=self.tracker, head=h, transaction_nonce=5, no_one_payload_path=True)
        raw, row = wallet.sign_activation(SCOPE, state, self.store, key, SEED, self.crypto, ACTIVATION_CONFIG,
                                          tracker=self.tracker, head=h, transaction_nonce=5,
                                          no_one_payload_path=True, confirm_revival=stated.exception.token)
        self.assertEqual(raw, self.signed(0, 5, True))

    def test_r2_the_activation_first_bundle_makes_the_rotate_stale(self):
        state, h, r, key, _ = self.rotate_setup()
        # The bundle API carries the activation first, then a transaction at R's account nonce.
        try:
            manual = at.OnePayloadBundle(h, (at.PayloadElement("ACTIVATION", b"activation-5", account_nonce=5,
                                                               commitment=self.keys[0].commitment),
                                             at.PayloadElement("TRANSACTION", b"tx-6", account_nonce=6)))
        except ValueError as exc:
            self.fail(f"the bundle API refuses an activation-first payload: {exc}")
        self.assertEqual(self.tracker.bundle_preview(SCOPE, manual)["end_state"]["account_nonce"], 7)
        bundle = wallet.prepare_activation_bundle(SCOPE, state, self.store, key, SEED, self.crypto,
                                                  ACTIVATION_CONFIG, tracker=self.tracker, head=h)
        self.assertEqual([(e.kind, e.account_nonce) for e in bundle.elements], [("ACTIVATION", 5), ("TRANSACTION", 6)])
        self.assertEqual([e.carrier for e in bundle.elements], [self.signed(0, 5, True), self.signed(0, 6, False)])
        self.assertEqual(bundle.fee_path, "OWN_FUNDS")
        preview = self.tracker.bundle_preview(SCOPE, bundle)
        self.assertEqual(preview["revived_between_elements"], [[r.group_id, r.variant_id]])
        self.assertEqual((preview["end_state"]["account_nonce"], preview["end_state"]["activated"]), (7, True))
        payloads = []
        self.tracker.export_bundle(SCOPE, bundle, payloads.append)
        self.assertEqual(payloads, [tuple(e.carrier for e in bundle.elements)])
        # An activating rotate (31.2 rule 7 (b)'s path where it applies) may lead instead of the activation.
        rotate = Authorization(ACCOUNT, "ROTATE", 5, self.keys[1].commitment, activating=True,
                               signer_commitment=self.keys[0].commitment, epoch=1)
        led = at.OnePayloadBundle(h, (at.PayloadElement("WRITE", b"activating-rotate", authorization=rotate),
                                      at.PayloadElement("TRANSACTION", b"tx-6", account_nonce=6)))
        self.assertEqual(self.tracker.bundle_preview(SCOPE, led)["end_state"]["account_nonce"], 7)
        # A transaction cannot lead, and an activation is followed by 0x7c transactions only.
        for elements in ((at.PayloadElement("TRANSACTION", b"tx-5", account_nonce=5),
                          at.PayloadElement("TRANSACTION", b"tx-6", account_nonce=6)),
                         (bundle.elements[0], at.PayloadElement("WRITE", b"0x7e", authorization=pi_auth(1, key_commitment("k9"), epoch=1)))):
            with self.assertRaises(ValueError):
                at.OnePayloadBundle(h, elements)

    def test_r2_the_activation_only_offer_names_the_transaction_that_goes_with_it(self):
        state, h, r, key, p = self.rotate_setup(with_pi=True)
        notice = self.tracker.observe_head(SCOPE, h)
        offer = offer_for(notice, p)
        self.assertEqual(offer["action"], ACTIVATION_LABEL)
        self.assertTrue(offer.get("one_payload"))
        self.assertEqual(offer["payload"]["through_account_nonce"], 6)
        self.assertEqual(notice["activation_revives"], [[r.group_id, r.variant_id]])


class ExposureClosureTests(Base):
    """The revival check follows tracked carriers past the first step (WE-20 structure)."""

    def closure_setup(self):
        n = 5
        pi_at = lambda m, epoch, expiry: Authorization.from_pi(
            ACCOUNT, wallet._pi(self.canonical(m, 0, "d0"), self.keys[epoch], DOMAIN, VERSION, expiry, FEE), epoch=epoch)
        s2, s3 = pi_at(2, 0, 2500), pi_at(3, 0, 9000)   # own same-key writes; S2 expired at the head
        r = Authorization(ACCOUNT, "ROTATE", n, self.keys[4].commitment, activating=True,
                          signer_commitment=self.keys[0].commitment, epoch=4)
        for auth, carrier in ((s2, b"own-same-key-S2"), (s3, b"own-same-key-S3"), (r, b"own-activating-rotate-R")):
            self.tracker.record(SCOPE, auth, carrier)
        self.store.mark_compromised(SCOPE, 4, "xi_4 reported leaked")
        # Canonical branch: another device's re-commit V (nonce 1 -> C_1).
        state = self.canonical(2, 1, "d1")
        h = head(block_hash="d1" * 32, number=40, timestamp=3000, migration_nonce=2, account_nonce=n,
                 commitment=self.keys[1].commitment, fork_time=None)
        self.tracker.observe_head(SCOPE, h)
        return pi_at, s3, r, state, h

    def test_r2_a_write_that_revives_an_exposed_rotate_through_an_unexposed_carrier_is_refused(self):
        _, s3, r, state, h = self.closure_setup()
        self.assertFalse(any(binding_conditions_allow(a, h) for a in (s3, r)))
        plan = self.plan(state)
        self.assertEqual(plan.key.epoch, 2)
        with self.assertRaises(ValueError) as caught:
            wallet.export_recovery(plan, SCOPE, state, self.store, self.tracker, **self.export_kwargs(plan, h))
        self.assertEqual(self.sent, [])
        self.assertEqual(getattr(caught.exception, "revived", None), [[r.group_id, r.variant_id]])

    def test_r2_retries_and_bundle_end_states_use_the_same_closure(self):
        pi_at, s3, r, state, h = self.closure_setup()
        w0 = pi_at(2, 2, 9000)     # an own re-commit at nonce 2 to K_2, tracked
        self.tracker.record(SCOPE, w0, b"W0")
        self.assertFalse(self.tracker.resubmission_allowed(SCOPE, w0, h))
        # [W0, a same-key write at 3] ends at nonce 4 with C_2; the tracked S4 restores C_0 there.
        self.tracker.record(SCOPE, pi_at(4, 0, 9000), b"own-same-key-S4")
        write = lambda auth: at.PayloadElement("WRITE", b"carrier-%d" % auth.nonce, authorization=auth)
        with self.assertRaisesRegex(ValueError, "BUNDLE_REVIVES_EXPOSED_AUTHORIZATION"):
            self.tracker.bundle_preview(SCOPE, at.OnePayloadBundle(h, (write(w0), write(pi_at(3, 2, 9000)))))
        # With the activation of K_2 instead, the re-commit gate closes and nothing revives at the end.
        activation = at.PayloadElement("ACTIVATION", b"activation-K2", commitment=self.keys[2].commitment, account_nonce=5)
        preview = self.tracker.bundle_preview(SCOPE, at.OnePayloadBundle(h, (write(w0), activation)))
        self.assertEqual(preview["revived_between_elements"], [[r.group_id, r.variant_id]])


class ExposureAdapterBundleTests(Base):
    """The one-payload remedy is reachable through the adapter, and the lone route is closed."""

    def test_r2_the_adapter_builds_the_recovery_bundle_and_the_plain_lone_route_is_closed(self):
        p = self.learned_pi(1, 1, with_epoch=True)     # V22-W-1 with P's epoch known (the probes' control)
        self.tracker.record(SCOPE, p, b"P-of-another-device")
        self.store.mark_compromised(SCOPE, 1, "W records epoch 1")
        state = self.frozen_state()
        h = self.head_for(state, account_nonce=7)
        self.tracker.observe_head(SCOPE, h)
        plan = self.plan(state)
        # S of branch 1 is tracked and can still be included (V22-W-1; draft 34.2 rule 1 (b)).
        self.tracker.record(SCOPE, Authorization.from_pi(ACCOUNT, plan.pi, epoch=0), b"S-of-branch-1", **IN_BLOCK)
        kwargs = self.export_kwargs(plan, h)
        with self.assertRaises(ValueError) as caught:
            wallet.export_recovery(plan, SCOPE, state, self.store, self.tracker, **kwargs)
        self.assertEqual(getattr(caught.exception, "remedy", None), "ONE_PAYLOAD_BUNDLE")
        token = getattr(caught.exception, "token", None)
        with self.assertRaises(ValueError):   # the confirm-revival route is closed for a one-payload remedy
            wallet.export_recovery(plan, SCOPE, state, self.store, self.tracker,
                                   confirm_revival=token or "00" * 32, **kwargs)
        self.assertEqual(self.sent, [])
        bundle = wallet.prepare_recovery_bundle(plan, SCOPE, state, self.store, self.tracker, head=h,
                                                proof=b"MODEL-PROOF-NOT-REAL", journal=plan.pi, config=CONFIG,
                                                verify_proof=lambda proof, pi: True, seed64=SEED,
                                                crypto=self.crypto, activation_config=ACTIVATION_CONFIG, **BALANCE)
        write, activation = bundle.elements
        self.assertEqual((write.kind, write.carrier[0], write.authorization.pi), ("WRITE", 0x7E, plan.pi))
        self.assertEqual((activation.kind, activation.account_nonce), ("ACTIVATION", 7))
        self.assertEqual(activation.carrier, self.signed(0, 7, True))
        self.assertEqual(self.tracker.bundle_preview(SCOPE, bundle, **BALANCE)["revived_between_elements"],
                         [[p.group_id, p.variant_id]])
        payloads = []
        self.tracker.export_bundle(SCOPE, bundle, payloads.append, **BALANCE)
        self.assertEqual(payloads, [(write.carrier, activation.carrier)])
        self.assertEqual(self.sent, [])
        # Rule 1 (c): where no path gives one payload, the stated gap and its confirmation.
        with self.assertRaisesRegex(ValueError, "NO_ONE_PAYLOAD_PATH") as stated:
            wallet.export_recovery(plan, SCOPE, state, self.store, self.tracker, no_one_payload_path=True, **kwargs)
        wallet.export_recovery(plan, SCOPE, state, self.store, self.tracker, no_one_payload_path=True,
                               confirm_revival=stated.exception.token, **kwargs)
        self.assertEqual(self.sent, [write.carrier])


class ExposureLegacyBeforeTTests(Base):
    """At a LEGACY head before T the pair is a 0x7d, then a 0x7e past the PI's nonce."""

    def test_r2_a_legacy_head_before_T_offers_the_enrollment_pair(self):
        for fork_time in (None, 9_000_000):
            with self.subTest(fork_time=fork_time):
                tracker = AuthorizationTracker(Path(self.tmp.name) / f"t{fork_time}")
                h = frozen_head(fork_time=fork_time, timestamp=1000, account_nonce=0)
                e = Authorization(ACCOUNT, "ENROLL", 0, key_commitment("k0"), epoch=0)
                p = pi_auth(1, key_commitment("k1"), epoch=1)
                tracker.record(SCOPE, e, b"E")
                tracker.record(SCOPE, p, b"P")
                tracker.epochs.mark_compromised(SCOPE, 1, "K_1 exposed")
                offer = offer_for(tracker.observe_head(SCOPE, h), p)
                self.assertEqual(offer["action"], BUNDLE_LABEL)
                self.assertEqual(offer["payload"]["first"], "ENROLLMENT_0x7D_AT_ACCOUNT_NONCE")
                self.assertIs(offer["payload"]["activation_discharges"], False)
                with self.assertRaises(ValueError) as caught:
                    tracker.export(SCOPE, e, b"E", self.sent.append, head=h)
                self.assertEqual(self.sent, [])
                self.assertEqual(getattr(caught.exception, "remedy", None), "ONE_PAYLOAD_BUNDLE")
                element = lambda auth, raw: at.PayloadElement("WRITE", raw, authorization=auth)
                pair = at.OnePayloadBundle(h, (element(e, b"E"),
                                               element(sponsored(pi_auth(1, key_commitment("k0"), epoch=0)), b"F")))
                self.assertEqual(tracker.bundle_preview(SCOPE, pair)["end_state"]["migration_nonce"], 2)
                # An activation does not discharge P: the override gate has no code condition (l. 1160).
                with_activation = at.OnePayloadBundle(h, (element(e, b"E"), at.PayloadElement(
                    "ACTIVATION", b"A", commitment=key_commitment("k0"), account_nonce=1)))
                with self.assertRaisesRegex(ValueError, "BUNDLE_REVIVES_EXPOSED_AUTHORIZATION"):
                    tracker.bundle_preview(SCOPE, with_activation)
                # A tracked exposed rotate above a LEGACY head's account nonce: its precursors
                # start with a transaction of the LEGACY account, not with an activation.
                r = Authorization(ACCOUNT, "ROTATE", 2, key_commitment("k9"), activating=False,
                                  signer_commitment=key_commitment("k8"), epoch=9)
                tracker.record(SCOPE, r, b"R")
                tracker.epochs.mark_compromised(SCOPE, 9, "K_9 exposed")
                offer = offer_for(tracker.observe_head(SCOPE, h), r)
                self.assertEqual((offer["action"], offer["payload"]["first"]),
                                 (BUNDLE_LABEL, "TRANSACTION_OF_THE_LEGACY_ACCOUNT_AT_ITS_NONCE"))


class ExposureOwnKeyTests(Base):
    """No plan or write of a key known exposed; a move away needs explicit confirmation."""

    def test_r2_prepare_recovery_refuses_a_selected_key_known_exposed(self):
        # Probe D: another device's O (nonce 1 -> C_1) learned without its epoch; C_1 exposed by commitment.
        o = self.learned_pi(1, 1)
        self.tracker.record(SCOPE, o, b"orphaned-0x7e-of-device-2")
        self.tracker.mark_exposed(SCOPE, ACCOUNT, self.keys[1].commitment, "device 2 compromised")
        state = self.canonical(1, 0, "f1")
        self.tracker.observe_head(SCOPE, self.head_for(state))
        with self.assertRaisesRegex(ValueError, "EPOCH_COMPROMISED"):
            self.plan(state)
        self.assertEqual(self.ledger(), [1])

    def test_r2_tracker_export_refuses_a_write_of_a_key_known_exposed(self):
        h = head(commitment=key_commitment("k0"))
        self.tracker.observe_head(SCOPE, h)
        self.tracker.mark_exposed(SCOPE, ACCOUNT, key_commitment("k1"), "K_1 known exposed")
        write = pi_auth(1, key_commitment("k1"), epoch=1)
        with self.assertRaisesRegex(ValueError, "WRITE_KEY_EXPOSED"):
            self.tracker.export(SCOPE, write, b"w", self.sent.append, head=h)
        self.assertEqual(self.sent, [])
        self.assertEqual(self.ledger(), [1])   # the write's epoch is persisted before the refusal
        self.assertNotIn(write.group_id, self.tracker.records(SCOPE))

    def test_r2_a_rotate_signed_by_an_exposed_key_moves_away_only_on_confirmation(self):
        h = head(activated=True, commitment=key_commitment("k0"))    # binding-final under K_0
        self.tracker.observe_head(SCOPE, h)
        self.tracker.mark_exposed(SCOPE, ACCOUNT, key_commitment("k0"), "current key exposed")
        move = Authorization(ACCOUNT, "ROTATE", 5, key_commitment("k2"), activating=False,
                             signer_commitment=key_commitment("k0"), epoch=2)
        with self.assertRaisesRegex(ValueError, "SIGNER_KEY_EXPOSED") as caught:
            self.tracker.export(SCOPE, move, b"move-away", self.sent.append, head=h)
        self.assertEqual(self.sent, [])
        self.tracker.export(SCOPE, move, b"move-away", self.sent.append, head=h,
                            confirm_move_away=caught.exception.token)
        self.assertEqual(self.sent, [b"move-away"])


class ExposureStealthEnrollmentTests(Base):
    """Spec 34.2 rule 2, the wallet part of V22-W-3."""

    def test_r2_v22w3_a_stealth_enrollment_revealed_at_a_finalized_block_is_reported(self):
        e = Authorization(ACCOUNT, "ENROLL", 0, self.keys[0].commitment, epoch=0)
        self.tracker.record(SCOPE, e, b"own-0x7d-E-at-account-nonce-0")
        c_ext = key_commitment("ext")
        f = AccountState(ACCOUNT, "a7" * 32, 70, 1000, 1, 1, "PQ_BY_ENROLL", False, c_ext, 5000, W, 990)
        ended = self.tracker.observe_finalized(SCOPE, FinalizedView(f))
        self.assertEqual(list(ended), [(e.group_id, e.variant_id, "ACCOUNT_NONCE_CONSUMED")])
        notices = getattr(ended, "notices", [])
        self.assertEqual([n["action"] for n in notices], ["REPORT_STEALTH_ENROLLMENT_OFFER_OVERRIDE"])
        self.assertEqual((notices[0]["commitment"], notices[0]["override_deadline"]), (c_ext.hex(), f.deadline))
        offers = self.tracker.observe_head(SCOPE, f)["offers"]
        self.assertEqual(offers[0]["action"], "REPORT_STEALTH_ENROLLMENT_OFFER_OVERRIDE")
        # override_deadline is read again at each head: a fork that extends W.
        extended = replace(f, block_hash="a8" * 32, number=71, timestamp=1012, override_window=2 * W)
        notice = self.tracker.observe_head(SCOPE, extended)["stealth_enrollment"]
        self.assertEqual(notice["override_deadline"], 5000 + 2 * W)
        self.assertTrue(notice["override_open"])

    def test_v22w3_another_devices_binding_and_the_own_enrollment_are_not_reported_control(self):
        cases = {
            # V22-W-3 (iv): a PQ_BY_PROOF binding of another device of the owner (after T).
            "pq_by_proof": AccountState(ACCOUNT, "b7" * 32, 70, 6000, 1, 0, "PQ_BY_PROOF", False,
                                        self.keys[1].commitment, 5000, W, 0),
            # The device's own enrollment key: its 0x7d E took the nonce itself.
            "own_enrollment": AccountState(ACCOUNT, "c7" * 32, 70, 1000, 1, 1, "PQ_BY_ENROLL", False,
                                           self.keys[0].commitment, 5000, W, 990),
        }
        for label, f in cases.items():
            with self.subTest(label):
                tracker = AuthorizationTracker(Path(self.tmp.name) / label)
                e = Authorization(ACCOUNT, "ENROLL", 0, self.keys[0].commitment, epoch=0)
                tracker.record(SCOPE, e, b"own-0x7d-E")
                ended = tracker.observe_finalized(SCOPE, FinalizedView(f))
                self.assertEqual(len(ended), 1)
                self.assertEqual(getattr(ended, "notices", []), [])
                self.assertIsNone(tracker.observe_head(SCOPE, f).get("stealth_enrollment"))


class CoverageTests(Base):
    """Guards that had no test."""

    def track_exposed_leaf(self):
        leaf = Authorization.from_pi(ACCOUNT, wallet._pi(self.canonical(2, 0, "b0"), self.keys[2], DOMAIN,
                                                         VERSION, EXPIRY, FEE), epoch=2)
        self.tracker.record(SCOPE, leaf, b"leaf-P")
        self.store.mark_compromised(SCOPE, 2, "leaf key exposed")
        return leaf

    def test_cov_validate_plan_with_the_tracker_refuses_a_same_key_plan_whose_key_became_exposed(self):
        state = self.canonical(2, 1, "a2")
        key = scan_current_key(SCOPE, state, lambda e: self.keys[e].commitment).current_key
        self.store.mark_compromised(SCOPE, 2, "next epoch recorded, so a same-key step is offered")
        plan = wallet.prepare_recommit(SCOPE, state, self.store, key, SEED, self.crypto, tracker=self.tracker,
                                       domain_tag=DOMAIN, verifier_version=VERSION, expiry=EXPIRY,
                                       max_account_fee=FEE, confirm_extra_proof_and_fee=True)
        self.assertTrue(plan.same_key_recommit)
        self.tracker.mark_exposed(SCOPE, ACCOUNT, self.keys[1].commitment, "C_1 exposed after the plan")
        h = self.head_for(state, number=12, timestamp=1000)
        self.tracker.observe_head(SCOPE, h)   # no current_epoch: the caller ran no scan here
        with self.assertRaisesRegex(ValueError, "CURRENT_KEY_COMPROMISED"):
            wallet.validate_plan(plan, SCOPE, state, self.store, tracker=self.tracker)
        self.assertEqual(self.ledger(), [1, 2])
        with self.assertRaisesRegex(ValueError, "CURRENT_KEY_COMPROMISED"):
            wallet.export_recovery(plan, SCOPE, state, self.store, self.tracker, **self.export_kwargs(plan, h))
        self.assertEqual(self.sent, [])
        self.assertNotIn(Authorization.from_pi(ACCOUNT, plan.pi).group_id, self.tracker.records(SCOPE))

    def test_cov_a_confirmation_token_is_bound_to_the_head_and_the_write(self):
        self.track_exposed_leaf()
        h1 = head(commitment=self.keys[0].commitment)
        self.tracker.observe_head(SCOPE, h1)
        w1 = pi_auth(1, self.keys[1].commitment, epoch=1)
        w2 = pi_auth(1, self.keys[0].commitment, epoch=0)
        with self.assertRaises(ValueError) as first:
            self.tracker.export(SCOPE, w1, b"w1", self.sent.append, head=h1)
        token = getattr(first.exception, "token", None)
        self.assertIsNotNone(token)
        with self.assertRaises(ValueError):    # the token of another write
            self.tracker.export(SCOPE, w2, b"w2", self.sent.append, head=h1, confirm_revival=token)
        h2 = replace(h1, block_hash="c2" * 32, number=21)
        self.tracker.observe_head(SCOPE, h2)
        with self.assertRaises(ValueError):    # the token of another head
            self.tracker.export(SCOPE, w1, b"w1", self.sent.append, head=h2, confirm_revival=token)
        self.assertEqual(self.sent, [])
        with self.assertRaises(ValueError) as again:
            self.tracker.export(SCOPE, w1, b"w1", self.sent.append, head=h2)
        self.tracker.export(SCOPE, w1, b"w1", self.sent.append, head=h2, confirm_revival=again.exception.token)
        self.assertEqual(self.sent, [b"w1"])

    def test_cov_export_accepts_only_the_lone_preview_and_a_known_fee_path(self):
        self.track_exposed_leaf()
        h1 = head(commitment=self.keys[0].commitment)
        self.tracker.observe_head(SCOPE, h1)
        w1 = pi_auth(1, self.keys[1].commitment, epoch=1)
        lone = replace(h1, migration_nonce=2, commitment=w1.commitment)
        with_activation = replace(lone, activated=True, account_nonce=h1.account_nonce + 1)
        with self.assertRaisesRegex(ValueError, "PREVIEW_NOT_CANDIDATE_ALONE"):
            self.tracker.export(SCOPE, w1, b"w1", self.sent.append, head=h1, after=with_activation)
        self.assertEqual(self.sent, [])
        self.assertNotIn(w1.group_id, self.tracker.records(SCOPE))
        elements = (at.PayloadElement("WRITE", b"w1", authorization=w1),
                    at.PayloadElement("ACTIVATION", b"act", commitment=w1.commitment, account_nonce=5))
        with self.assertRaisesRegex(ValueError, "unknown fee path"):
            at.OnePayloadBundle(h1, elements, fee_path="CARD")


# ------------------------------------------------------------------------------------------------
# Spec section 34.2 rule 1 as redrafted (cases (a) (i)-(iii), (b)-(g)) and rule 6.

HOLD_LABEL = "WAIT_FRESH_PRECURSOR_HELD_UNTIL_RULE_2"
HOLD_REMEDY = "HOLD_FRESH_PRECURSOR_UNTIL_RULE_2"


class PrecursorBase(Base):
    """Fixtures of vectors V22-W-1, V22-W-2, V22-W-5 to V22-W-7 at component tier (model proofs, ModelCrypto)."""

    def fresh_wallet(self, label):
        directory = Path(self.tmp.name) / label
        self.store, self.tracker, self.sent = WalletEpochStore(directory), AuthorizationTracker(directory), []

    def write(self, auth, carrier):
        return at.PayloadElement("WRITE", carrier, authorization=auth)

    def activation_element(self, epoch, nonce):
        """W's activating 0x7c of K_epoch at account nonce `nonce`, signed through the adapter's encoder."""
        return at.PayloadElement("ACTIVATION", self.signed(epoch, nonce, True),
                                 commitment=self.keys[epoch].commitment, account_nonce=nonce)

    def pi_of(self, nonce, epoch, *, expiry=EXPIRY):
        """W's own write at `nonce` committing C_epoch, with its epoch (a same-key step where epoch < nonce)."""
        return self.learned_pi(nonce, epoch, expiry=expiry, with_epoch=True)

    def bundle_kwargs(self, plan, h):
        return dict(head=h, proof=b"MODEL-PROOF-NOT-REAL", journal=plan.pi, config=CONFIG,
                    verify_proof=lambda proof, pi: True, seed64=SEED, crypto=self.crypto)

    def v22w1(self, *, s_expiry=EXPIRY, timestamp=2000, block="f1"):
        """V22-W-1 after the reorganization: a frozen at migration_nonce 0 (account nonce 7). S, W's frozen
        recovery of branch 1 (C_0, expiry X0), and P, another device's re-commit at nonce 1 (C_1, X = 6000)
        learned on chain, are tracked; W records epoch 1."""
        state = canonical_state(13376, "11" * 32, "22" * 20, block * 32, 0, timestamp=timestamp,
                                fork_time=900, override_window=W)
        h = self.head_for(state, account_nonce=7)
        s, p = self.pi_of(0, 0, expiry=s_expiry), self.learned_pi(1, 1, expiry=6000)
        self.tracker.record(SCOPE, s, b"S-of-branch-1", **IN_BLOCK)
        wallet.learn_authorization(SCOPE, SEED, self.crypto, self.store, self.tracker, p, b"P-of-another-device")
        self.store.mark_compromised(SCOPE, 1, "W records epoch 1")
        self.tracker.observe_head(SCOPE, h)
        return state, h, s, p

    def v22w2(self, *, s_expiry=EXPIRY, p_expiry=EXPIRY):
        """V22-W-2 after the reorganization: A's stealth enrollment C_ext (migration_nonce 1, account nonce 7),
        chain-finalized and reported (rule 2); S, W's override at nonce 1 (C_1, X1), and P, another device's
        re-commit at nonce 2 (C_2, X) learned on chain, are tracked; W records epoch 2."""
        c_ext = key_commitment("ext")
        f = AccountState(ACCOUNT, "e1" * 32, 30, 1990, 1, 7, "PQ_BY_ENROLL", False, c_ext, 900, W, 850)
        self.tracker.observe_finalized(SCOPE, FinalizedView(f))
        state = canonical_state(13376, "11" * 32, "22" * 20, "f2" * 32, 1, status="PQ_BY_ENROLL",
                                commitment=c_ext, timestamp=2000, fork_time=900, override_window=W,
                                enrolled_at=850)
        h = AccountState(ACCOUNT, "f2" * 32, 31, 2000, 1, 7, "PQ_BY_ENROLL", False, c_ext, 900, W, 850)
        s, p = self.pi_of(1, 1, expiry=s_expiry), self.learned_pi(2, 2, expiry=p_expiry)
        self.tracker.record(SCOPE, s, b"S-override-of-branch-1", **IN_BLOCK)
        wallet.learn_authorization(SCOPE, SEED, self.crypto, self.store, self.tracker, p, b"P-of-another-device")
        self.store.mark_compromised(SCOPE, 2, "W records epoch 2")
        self.tracker.observe_head(SCOPE, h)
        return state, h, s, p


class PrecursorFreshPrecursorTests(PrecursorBase):
    """Spec 34.2 rule 1 (g): a fresh precursor waits (V22-W-1 (iv), V22-W-2 (v)); rule 2's last sentences."""

    def test_r3_v22w1_iv_a_fresh_frozen_recovery_waits_until_rule_2(self):
        # X0 = 1500 has passed at the head (3000): S can no longer be included, and only a new frozen
        # recovery, which needs the seed (l. 46), can make P (X = 6000) includable.
        state, h, s, p = self.v22w1(s_expiry=1500, timestamp=3000, block="f3")
        fresh = at.OnePayloadBundle(h, (self.write(self.pi_of(0, 0), b"S-prime"), self.activation_element(0, 7)))
        with self.assertRaisesRegex(ValueError, "BUNDLE_FRESH_PRECURSOR_HELD"):    # delivered
            self.tracker.export_bundle(SCOPE, fresh, self.sent.append)
        self.assertEqual(self.sent, [])
        offer = offer_for(self.tracker.observe_head(SCOPE, h), p)
        self.assertEqual(offer["action"], HOLD_LABEL)          # OFFER_ONE_PAYLOAD_BUNDLE at once
        self.assertEqual(offer["time_left"], {"pi_expiry": 6000})
        plan = self.plan(state)                                 # the fresh frozen recovery S' (C_0, expiry 5000)
        for extra in ({}, {"no_one_payload_path": True}):
            with self.subTest(**extra), self.assertRaises(ValueError) as caught:
                wallet.export_recovery(plan, SCOPE, state, self.store, self.tracker,
                                       **self.export_kwargs(plan, h), **extra)
            self.assertEqual((caught.exception.remedy, caught.exception.token), (HOLD_REMEDY, None))
        with self.assertRaisesRegex(ValueError, "BUNDLE_FRESH_PRECURSOR_HELD"):
            wallet.prepare_recovery_bundle(plan, SCOPE, state, self.store, self.tracker,
                                           activation_config=ACTIVATION_CONFIG, **self.bundle_kwargs(plan, h))
        self.assertEqual(self.sent, [])
        # A reorganization makes canonical a branch whose head can still include S: offered at once.
        earlier = replace(h, block_hash="f5" * 32, number=19, timestamp=1400)
        offer = offer_for(self.tracker.observe_head(SCOPE, earlier), p)
        self.assertEqual((offer["action"], offer["payload"]["precursor_carriers"]),
                         (BUNDLE_LABEL, [[s.group_id, s.variant_id]]))
        # A chain-finalized block after X ends P's tracking (32.2 rule 2); then the fresh recovery goes
        # with the activation of K_0.
        f = AccountState(ACCOUNT, "f6" * 32, 40, 6001, 0, 7, "LEGACY", False, None, 900, W, 0)
        self.assertIn((p.group_id, p.variant_id, "PI_EXPIRED"),
                      list(self.tracker.observe_finalized(SCOPE, FinalizedView(f))))
        later = canonical_state(13376, "11" * 32, "22" * 20, "f6" * 32, 0, timestamp=6001, fork_time=900,
                                override_window=W)
        h2 = self.head_for(later, account_nonce=7, number=40)
        self.assertEqual(offer_for_all(self.tracker.observe_head(SCOPE, h2), p), [])
        plan2 = wallet.prepare_recovery(SCOPE, later, self.store, SEED, self.crypto, tracker=self.tracker,
                                        domain_tag=DOMAIN, verifier_version=VERSION, expiry=9000, max_account_fee=FEE)
        bundle = wallet.prepare_recovery_bundle(plan2, SCOPE, later, self.store, self.tracker,
                                                activation_config=ACTIVATION_CONFIG, **self.bundle_kwargs(plan2, h2),
                                                **BALANCE)
        payloads = []
        self.tracker.export_bundle(SCOPE, bundle, payloads.append, **BALANCE)
        self.assertEqual(payloads, [(bundle.elements[0].carrier, self.signed(0, 7, True))])

    def test_r3_v22w2_v_a_fresh_override_waits_where_the_deadline_allows(self):
        # X1 = 1500 has passed at the head (2000): S can no longer be included. deadline(a) = T + W.
        wide = {"override_margin": W} if "override_margin" in inspect.signature(AuthorizationTracker).parameters else {}
        cases = (("X and the margin fit before deadline(a)", EXPIRY, {}, True),
                 ("deadline(a) would come first", 31_000_000, {}, False),
                 ("a margin wider than deadline(a) - X", EXPIRY, wide, False))
        for label, p_expiry, margin, hold in cases:
            with self.subTest(label):
                self.fresh_wallet(label.replace(" ", "-").replace("(", "").replace(")", ""))
                if margin:
                    self.tracker = AuthorizationTracker(self.tracker.directory, **margin)
                state, h, s, p = self.v22w2(s_expiry=1500, p_expiry=p_expiry)
                notice = self.tracker.observe_head(SCOPE, h)
                offer, stealth = offer_for(notice, p), notice["stealth_enrollment"]
                self.assertEqual(stealth["override_deadline"], 900 + W)     # the report stands meanwhile
                fresh = self.pi_of(1, 1)                                      # a fresh override S' (C_1)
                pair = at.OnePayloadBundle(h, (self.write(fresh, b"S-prime"),
                                               self.write(sponsored(self.pi_of(2, 1)), b"sponsored-same-key-recommit")),
                                           fee_path="SPONSOR")
                payloads = []
                if hold:
                    with self.assertRaisesRegex(ValueError, "BUNDLE_FRESH_PRECURSOR_HELD"):   # delivered
                        self.tracker.export_bundle(SCOPE, pair, payloads.append)
                    self.assertEqual(offer["action"], HOLD_LABEL)            # OFFER_ONE_PAYLOAD_BUNDLE
                    self.assertEqual(stealth.get("override_as"), "AFTER_THE_WAIT_OF_34_2_RULE_1_G")
                    self.assertEqual(offer["time_left"], {"pi_expiry": EXPIRY, "override_deadline": 900 + W})
                    with self.assertRaises(ValueError) as caught:
                        self.tracker.export(SCOPE, fresh, b"S-prime", self.sent.append, head=h)
                    self.assertEqual((caught.exception.remedy, caught.exception.token), (HOLD_REMEDY, None))
                    self.assertEqual((payloads, self.sent), ([], []))
                else:
                    self.assertEqual(offer["action"], BUNDLE_LABEL)
                    self.assertIs(offer["payload"].get("fresh_precursor"), True)
                    self.assertEqual(stealth.get("override_as"), "WITH_ITS_ACTS_AS_ONE_PAYLOAD_34_2_RULE_1")
                    self.tracker.export_bundle(SCOPE, pair, payloads.append)
                    self.assertEqual(payloads, [(b"S-prime", b"sponsored-same-key-recommit")])


class PrecursorWhichActTests(PrecursorBase):
    """Spec 34.2 rule 1 (f) and (d): the act after the precursor (V22-W-2 (iii)-(iv), V22-W-7)."""

    def test_r3_v22w2_iii_the_act_after_an_override_is_the_sponsored_write_not_the_activation(self):
        state, h, s, p = self.v22w2()                # S can still be included (X1 = 5000 at 2000)
        s_el, payloads = self.write(s, b"S-override-of-branch-1"), []
        with self.assertRaisesRegex(ValueError, "BUNDLE_ACT_PREEMPTIBLE"):      # never the activation as the act
            self.tracker.export_bundle(SCOPE, at.OnePayloadBundle(h, (s_el, self.activation_element(1, 7))),
                                       payloads.append)                       # delivered
        self.assertEqual(payloads, [])
        notice = self.tracker.observe_head(SCOPE, h)
        offer = offer_for(notice, p)
        self.assertEqual(offer["action"], BUNDLE_LABEL)
        payload = offer["payload"]
        self.assertEqual(payload.get("act"), "SPONSORED_WRITES_PAST_PI_MIGRATION_NONCE")   # none named
        self.assertIs(payload.get("activation_as_act"), False)
        self.assertEqual(payload.get("then_once_in_a_block"), "ACTIVATION_OF_THE_KEY_THE_WRITES_COMMIT")
        self.assertEqual(payload.get("precursor_carriers"), [[s.group_id, s.variant_id]])
        self.assertEqual(offer["time_left"], {"pi_expiry": EXPIRY, "precursor_expiry": EXPIRY,
                                              "override_deadline": 900 + W})
        self.assertEqual(notice["stealth_enrollment"]["override_as"], "WITH_ITS_ACTS_AS_ONE_PAYLOAD_34_2_RULE_1")
        with self.assertRaises(ValueError) as caught:            # never S without its act (rule 1 (c))
            self.tracker.export(SCOPE, s, b"S-override-of-branch-1", self.sent.append, head=h)
        self.assertEqual((caught.exception.remedy, caught.exception.token), ("ONE_PAYLOAD_BUNDLE", None))
        plan = self.plan(state, **own_funds())
        self.assertEqual(plan.pi, s.pi)
        with self.assertRaisesRegex(ValueError, "BUNDLE_ACT_PREEMPTIBLE"):      # the adapter's bundle neither
            wallet.prepare_recovery_bundle(plan, SCOPE, state, self.store, self.tracker,
                                           activation_config=ACTIVATION_CONFIG, **self.bundle_kwargs(plan, h))
        own = self.write(self.pi_of(2, 1), b"own-funds-same-key-recommit")       # 31.2 rule 8 (a), fee mode 0
        r_el = self.write(sponsored(self.pi_of(2, 1)), b"sponsored-same-key-recommit")  # fee mode 2
        with self.assertRaisesRegex(ValueError, "BUNDLE_ACT_PREEMPTIBLE"):      # a write paid by a is pre-emptible
            self.tracker.export_bundle(SCOPE, at.OnePayloadBundle(h, (s_el, own), fee_path="OWN_FUNDS"),
                                       payloads.append)
        self.tracker.export_bundle(SCOPE, at.OnePayloadBundle(h, (s_el, r_el), fee_path="SPONSOR"), payloads.append)
        self.assertEqual((payloads, self.sent), ([(b"S-override-of-branch-1", b"sponsored-same-key-recommit")], []))
        # P's tracking ends at a chain-finalized block that shows migration_nonce > 2, and not before.
        f = AccountState(ACCOUNT, "e3" * 32, 32, 2012, 3, 7, "PQ_BY_PROOF", False, self.keys[1].commitment, 900, W, 850)
        self.assertIn((p.group_id, p.variant_id, "MIGRATION_NONCE_CONSUMED"),
                      list(self.tracker.observe_finalized(SCOPE, FinalizedView(f, "e1" * 32))))

    def test_r3_v22w2_iv_a_transaction_of_the_enrolled_key_preempts_an_activation(self):
        state, h, s, p = self.v22w2()
        s_el = self.write(s, b"S-override-of-branch-1")
        # The behavioural assertion first, so that a side without the analysis fails on
        # the accepted payload, not on a missing report field.
        with self.assertRaisesRegex(ValueError, "BUNDLE_ACT_PREEMPTIBLE: ENROLLED_KEY_0x7C_AT_THE_ACCOUNT_NONCE"):
            self.tracker.bundle_preview(SCOPE, at.OnePayloadBundle(h, (s_el, self.activation_element(1, 7))))
        r_el = self.write(sponsored(self.pi_of(2, 1)), b"sponsored-same-key-recommit")    # fee mode 2
        preview = self.tracker.bundle_preview(SCOPE, at.OnePayloadBundle(h, (s_el, r_el), fee_path="SPONSOR"))
        preemptions = preview.get("preemptions") or []           # no pre-emption is examined
        self.assertEqual([x["by"] for x in preemptions], ["ENROLLED_KEY_0x7C_AT_THE_ACCOUNT_NONCE"])
        end = preemptions[0]["end_state"]
        self.assertEqual((end["migration_nonce"], end["account_nonce"], preemptions[0]["left_includable"]), (3, 8, []))
        # The consensus outcomes the model follows: A's 0x7c at n is valid before S and S after it (the
        # override gate has no code condition, l. 1160); W's activation signed for n then fails its nonce
        # (l. 318) and a builder pops it (l. 1232); P is valid after S (l. 263).
        after_a = replace(h, activated=True, account_nonce=8)
        self.assertTrue(binding_conditions_allow(s, after_a))
        after_s = at.single_write_preview(s, after_a)
        self.assertEqual((after_s.account_nonce, after_s.activated), (8, False))
        self.assertTrue(binding_conditions_allow(p, after_s))

    def test_r3_v22w7_the_act_after_a_0x7d_is_a_sponsored_write_past_the_pis_nonce(self):
        for fork_time in (None, 9_000_000):                    # T unscheduled (l. 61), or later than the head
            with self.subTest(fork_time=fork_time):
                self.fresh_wallet(f"legacy-{fork_time}")
                h = frozen_head(fork_time=fork_time, timestamp=1000, account_nonce=0)
                e = Authorization(ACCOUNT, "ENROLL", 0, self.keys[0].commitment, epoch=0)
                p = self.learned_pi(1, 1)                       # another device's 0x7e through the override gate
                self.tracker.record(SCOPE, e, b"E", **IN_BLOCK)
                wallet.learn_authorization(SCOPE, SEED, self.crypto, self.store, self.tracker, p, b"P")
                self.store.mark_compromised(SCOPE, 1, "W records epoch 1")
                offer = offer_for(self.tracker.observe_head(SCOPE, h), p)
                own = (self.write(e, b"E"), self.write(self.pi_of(1, 0), b"S1"))    # S1: l. 327's early finalisation
                pair = (self.write(e, b"E"), self.write(sponsored(self.pi_of(1, 0)), b"S1"))   # fee mode 2
                with self.assertRaisesRegex(ValueError, "BUNDLE_ACT_PREEMPTIBLE"):  # accepted
                    self.tracker.bundle_preview(SCOPE, at.OnePayloadBundle(h, own, fee_path="OWN_FUNDS"))
                payload = offer["payload"]
                self.assertEqual((payload.get("act"), payload.get("act_starts_with"), payload.get("past_pi_migration_nonce")),
                                 ("SPONSORED_WRITES_PAST_PI_MIGRATION_NONCE",
                                  "0x7E_AT_MIGRATION_NONCE_1_THROUGH_THE_OVERRIDE_GATE", 1))
                self.assertEqual((payload["first"], payload.get("precursor_carriers")),
                                 ("ENROLLMENT_0x7D_AT_ACCOUNT_NONCE", [[e.group_id, e.variant_id]]))
                self.assertEqual(offer.get("time_left"), {"pi_expiry": EXPIRY, "fork_time": fork_time})
                preview = self.tracker.bundle_preview(SCOPE, at.OnePayloadBundle(h, pair, fee_path="SPONSOR"))
                # E_A, A's own 0x7d at account nonce n, before the payload: E is popped (l. 185, l. 1232), S1 is
                # valid through the override gate that E_A opened, and P fails check 6.
                by = {x["by"]: x for x in preview["preemptions"]}
                end = by["0x7D_OF_A_AT_THE_ACCOUNT_NONCE"]["end_state"]
                self.assertEqual((end["mode"], end["migration_nonce"], end["commitment"]),
                                 ("PQ_BY_PROOF", 2, self.keys[0].commitment.hex()))
                with self.assertRaisesRegex(ValueError, "BUNDLE_REVIVES_EXPOSED_AUTHORIZATION"):
                    self.tracker.bundle_preview(SCOPE, at.OnePayloadBundle(h, (pair[0], self.activation_element(0, 1))))
                payloads = []
                self.tracker.export_bundle(SCOPE, at.OnePayloadBundle(h, pair), payloads.append)
                self.assertEqual(payloads, [(b"E", b"S1")])


class PrecursorPrecursorCaseTests(PrecursorBase):
    """Spec 34.2 rule 1 (a) (i) for a rotate, and (b): the acts that a precursor's payload carries."""

    def test_r3_a_tracked_rotate_in_the_frozen_or_override_gate_gets_the_write_first(self):
        # The fresh case is test_r4_v22w5_vii_a_fresh_precursor_of_a_rotate_takes_the_write_of_c_ind (the
        # act there is the write of C_ind, 34.2 rule 1 (f)).
        cases = (("frozen", frozen_head(account_nonce=5), 0, EXPIRY),
                 ("override", override_head(account_nonce=5), 1, EXPIRY))
        for label, h, epoch, s_expiry in cases:
            with self.subTest(label):
                self.fresh_wallet(label.replace(", ", "-").replace(" ", "-"))
                s = self.pi_of(h.migration_nonce, epoch, expiry=s_expiry)
                r = Authorization(ACCOUNT, "ROTATE", 5, self.keys[4].commitment, activating=True,
                                  signer_commitment=self.keys[epoch].commitment, epoch=4)
                self.tracker.record(SCOPE, s, b"S", **IN_BLOCK)
                self.tracker.record(SCOPE, r, b"R-activating-rotate-at-5")
                self.store.mark_compromised(SCOPE, 4, "K_4 exposed")
                offer = offer_for(self.tracker.observe_head(SCOPE, h), r)
                self.assertEqual(offer["action"], BUNDLE_LABEL)   # a transaction the owner cannot send
                payload = offer["payload"]
                self.assertEqual((payload["first"], payload.get("act")),
                                 ("WRITE_AT_CURRENT_MIGRATION_NONCE",
                                  "ACTIVATION_OF_THE_KEY_THE_WRITE_COMMITS_AT_THE_ACCOUNT_NONCE"))
                self.assertIs(payload.get("fresh_precursor"), s_expiry < h.timestamp)
                write = s if s_expiry >= h.timestamp else self.pi_of(h.migration_nonce, epoch)
                with self.assertRaises(ValueError) as caught:
                    self.tracker.export(SCOPE, write, b"S-or-fresh", self.sent.append, head=h)
                self.assertEqual(caught.exception.remedy, "ONE_PAYLOAD_BUNDLE")
                payloads = []
                self.tracker.export_bundle(SCOPE, at.OnePayloadBundle(h, (self.write(write, b"S-or-fresh"),
                                                                         self.activation_element(epoch, 5))),
                                           payloads.append, **BALANCE)
                self.assertEqual((len(payloads), self.sent), (1, []))

    def test_r3_an_act_that_is_itself_a_precursor_carries_the_next_act(self):
        state, h, s, p = self.v22w1()
        # R: a non-activating rotate at account nonce 8 signed by K_0, rotating to the recorded K_3. The
        # activation of K_0 at 7, the act after S, makes R includable (l. 328), so its act follows it.
        r = Authorization(ACCOUNT, "ROTATE", 8, self.keys[3].commitment, activating=False,
                          signer_commitment=self.keys[0].commitment, epoch=3)
        self.tracker.record(SCOPE, r, b"R-non-activating-at-8")
        self.store.mark_compromised(SCOPE, 3, "K_3 exposed")
        self.tracker.observe_head(SCOPE, h)
        plan = self.plan(state)
        bundle = wallet.prepare_recovery_bundle(plan, SCOPE, state, self.store, self.tracker,
                                                activation_config=ACTIVATION_CONFIG, **self.bundle_kwargs(plan, h),
                                                **BALANCE)
        self.assertEqual([(e.kind, e.account_nonce) for e in bundle.elements],
                         [("WRITE", None), ("ACTIVATION", 7), ("TRANSACTION", 8)])     # no transaction
        self.assertEqual([e.carrier for e in bundle.elements[1:]], [self.signed(0, 7, True), self.signed(0, 8, False)])
        payloads = []
        self.tracker.export_bundle(SCOPE, bundle, payloads.append, **BALANCE)
        self.assertEqual(payloads, [tuple(e.carrier for e in bundle.elements)])

    def test_r3_a_bundle_discharges_what_its_precursor_made_includable(self):
        h = frozen_head(account_nonce=5)
        s = self.pi_of(0, 0)
        r = Authorization(ACCOUNT, "ROTATE", 5, self.keys[4].commitment, activating=True,
                          signer_commitment=self.keys[0].commitment, epoch=4)
        self.tracker.record(SCOPE, s, b"S", **IN_BLOCK)
        self.tracker.record(SCOPE, r, b"R")
        self.store.mark_compromised(SCOPE, 4, "K_4 exposed")
        self.tracker.observe_head(SCOPE, h)
        # After S, R is includable; a re-commit to K_1 then makes R fail at the payload's end without
        # consuming its account nonce, and a later write can restore C_0 (32.2 rule 3 (a)).
        other = at.OnePayloadBundle(h, (self.write(s, b"S"), self.write(self.pi_of(1, 1), b"W1")), fee_path="SPONSOR")
        with self.assertRaisesRegex(ValueError, "BUNDLE_LEAVES_AUTHORIZATION_UNDISCHARGED"):
            self.tracker.bundle_preview(SCOPE, other)               # accepted
        restored = at.single_write_preview(self.pi_of(2, 0), replace(
            h, mode="PQ_BY_PROOF", migration_nonce=2, commitment=self.keys[1].commitment))
        self.assertTrue(binding_conditions_allow(r, restored))
        end = self.tracker.bundle_preview(SCOPE, at.OnePayloadBundle(h, (self.write(s, b"S"),
                                                                       self.activation_element(0, 5))),
                                          **BALANCE)["end_state"]
        self.assertEqual(end["account_nonce"], 6)


class PrecursorVectorMirrorTests(PrecursorBase):
    """Vectors V22-W-1 (iii), V22-W-5 (iii)-(iv) and V22-W-6, read against the redrafted text."""

    def test_mirror_v22w1_iii_s_goes_with_the_activation_as_one_payload(self):
        state, h, s, p = self.v22w1()
        self.assertEqual(actions_for(self.tracker.observe_head(SCOPE, h), p), [BUNDLE_LABEL])
        with self.assertRaises(ValueError) as caught:            # never S without the activation
            self.tracker.export(SCOPE, s, b"S-of-branch-1", self.sent.append, head=h)
        self.assertEqual((caught.exception.remedy, caught.exception.token), ("ONE_PAYLOAD_BUNDLE", None))
        pair = at.OnePayloadBundle(h, (self.write(s, b"S-of-branch-1"), self.activation_element(0, 7)))
        self.assertTrue(self.tracker.bundle_preview(SCOPE, pair, **BALANCE)["end_state"]["activated"])
        h2 = replace(h, block_hash="f7" * 32, number=21)          # prepared again after a change of the head
        self.tracker.observe_head(SCOPE, h2)
        with self.assertRaisesRegex(ValueError, "stale or unobserved bundle head"):
            self.tracker.export_bundle(SCOPE, pair, self.sent.append, **BALANCE)
        payloads = []
        self.tracker.export_bundle(SCOPE, at.OnePayloadBundle(h2, pair.elements), payloads.append, **BALANCE)
        self.assertEqual(payloads, [(b"S-of-branch-1", self.signed(0, 7, True))])
        # P's tracking ends at a chain-finalized block that shows final(a), and not before.
        f1 = AccountState(ACCOUNT, "f8" * 32, 30, 2100, 1, 7, "PQ_BY_PROOF", False, self.keys[0].commitment, 900, W, 0)
        self.assertNotIn(p.variant_id, [v for _, v, _ in self.tracker.observe_finalized(SCOPE, FinalizedView(f1))])
        f2 = replace(f1, block_hash="f9" * 32, number=31, timestamp=2112, activated=True, account_nonce=8)
        self.assertIn((p.group_id, p.variant_id, "BINDING_FINAL"),
                      list(self.tracker.observe_finalized(SCOPE, FinalizedView(f2, f1.block_hash))))

    def v22w5(self, *, with_pi=False):
        n = 5
        state = self.canonical(1, 0, "c5")
        h = head(block_hash="c5" * 32, number=30, timestamp=3000, account_nonce=n,
                 commitment=self.keys[0].commitment, fork_time=None)
        r = Authorization(ACCOUNT, "ROTATE", n + 1, self.keys[1].commitment, activating=False,
                          signer_commitment=self.keys[0].commitment, epoch=1)
        self.tracker.record(SCOPE, r, b"R-at-n+1")
        self.store.mark_compromised(SCOPE, 1, "W records epoch 1")
        p = None
        if with_pi:
            p = self.pi_of(2, 2)
            self.tracker.record(SCOPE, p, b"P-leaf-at-nonce-2")
            self.store.mark_compromised(SCOPE, 2, "K_2 exposed")
        key = scan_current_key(SCOPE, state, lambda e: self.keys[e].commitment).current_key
        self.tracker.observe_head(SCOPE, h)
        return n, state, h, r, key, p

    def test_mirror_v22w5_iii_the_activation_goes_with_the_transaction_at_the_rotates_nonce(self):
        n, state, h, r, key, _ = self.v22w5()
        with self.assertRaises(ValueError) as caught:            # never the activation alone
            wallet.sign_activation(SCOPE, state, self.store, key, SEED, self.crypto, ACTIVATION_CONFIG,
                                   tracker=self.tracker, head=h, transaction_nonce=n)
        self.assertEqual((caught.exception.remedy, caught.exception.token), ("ONE_PAYLOAD_BUNDLE", None))
        bundle = wallet.prepare_activation_bundle(SCOPE, state, self.store, key, SEED, self.crypto,
                                                  ACTIVATION_CONFIG, tracker=self.tracker, head=h)
        payloads = []
        self.tracker.export_bundle(SCOPE, bundle, payloads.append)
        self.assertEqual(payloads, [(self.signed(0, n, True), self.signed(0, n + 1, False))])
        # R's tracking ends at a chain-finalized block that shows nonce(a) > n + 1, and not before.
        f = replace(h, block_hash="c6" * 32, number=31, timestamp=3012, activated=True, account_nonce=n + 1)
        self.assertEqual(list(self.tracker.observe_finalized(SCOPE, FinalizedView(f))), [])
        f2 = replace(f, block_hash="c7" * 32, number=32, timestamp=3024, account_nonce=n + 2)
        self.assertEqual(list(self.tracker.observe_finalized(SCOPE, FinalizedView(f2, f.block_hash))),
                         [(r.group_id, r.variant_id, "ACCOUNT_NONCE_CONSUMED")])

    def test_mirror_v22w5_iv_the_same_payload_answers_a_tracked_pi(self):
        n, state, h, r, key, p = self.v22w5(with_pi=True)
        notice = self.tracker.observe_head(SCOPE, h)
        offer = offer_for(notice, p)
        self.assertEqual((offer["action"], offer.get("one_payload")), (ACTIVATION_LABEL, True))
        self.assertEqual(offer["payload"]["through_account_nonce"], n + 1)
        bundle = wallet.prepare_activation_bundle(SCOPE, state, self.store, key, SEED, self.crypto,
                                                  ACTIVATION_CONFIG, tracker=self.tracker, head=h)
        end = self.tracker.bundle_preview(SCOPE, bundle)["end_state"]
        self.assertFalse(binding_conditions_allow(p, AccountState.from_dict(end)))   # check 5 fails (0x0103)

    def test_mirror_v22w6_w2_waits_and_the_activation_of_k1_comes_first(self):
        n = 5
        pi_at = lambda m, expiry: self.pi_of(m, 0, expiry=expiry)
        s2, s3 = pi_at(2, 2500), pi_at(3, 9000)                 # X2 < 3000 < X3
        r = Authorization(ACCOUNT, "ROTATE", n, self.keys[4].commitment, activating=True,
                          signer_commitment=self.keys[0].commitment, epoch=4)
        for auth, raw in ((s2, b"S2"), (s3, b"S3"), (r, b"R")):
            self.tracker.record(SCOPE, auth, raw)
        self.store.mark_compromised(SCOPE, 4, "W records epoch 4")
        state = self.canonical(2, 1, "d1")                       # branch 2: V (nonce 1 -> C_1) chain-finalized
        h = head(block_hash="d1" * 32, number=40, timestamp=3000, migration_nonce=2, account_nonce=n,
                 commitment=self.keys[1].commitment, fork_time=None)
        self.tracker.observe_head(SCOPE, h)
        self.assertFalse(any(binding_conditions_allow(a, h) for a in (s2, s3, r)))
        plan = self.plan(state)                                  # W2 at nonce 2 committing C_2
        with self.assertRaises(ValueError) as caught:
            wallet.export_recovery(plan, SCOPE, state, self.store, self.tracker, **self.export_kwargs(plan, h))
        self.assertEqual((caught.exception.revived, caught.exception.remedy),
                         ([[r.group_id, r.variant_id]], "ACTIVATE_CURRENT_KEY_FIRST"))
        offer = offer_for(self.tracker.observe_head(SCOPE, h), r)
        self.assertEqual((offer["action"], offer["first"]),
                         ("OFFER_ACCOUNT_NONCE_CONSUMPTION", "ACTIVATION_OF_THE_CURRENT_KEY"))
        key = scan_current_key(SCOPE, state, lambda e: self.keys[e].commitment).current_key
        raw, _ = wallet.sign_activation(SCOPE, state, self.store, key, SEED, self.crypto, ACTIVATION_CONFIG,
                                        tracker=self.tracker, head=h, transaction_nonce=n)
        self.assertEqual(raw, self.signed(1, n, True))
        f = replace(h, block_hash="d2" * 32, number=41, timestamp=3012, activated=True, account_nonce=n + 1)
        ended = list(self.tracker.observe_finalized(SCOPE, FinalizedView(f)))
        self.assertIn((r.group_id, r.variant_id, "ACCOUNT_NONCE_CONSUMED"), ended)
        self.assertIn((s3.group_id, s3.variant_id, "BINDING_FINAL"), ended)
        self.assertEqual(self.sent, [])


# ------------------------------------------------------------------------------------------------
# Section 34.2 rule 1 (a) as one general condition, and the 16 findings of the verification. A
# test_v22_ test mirrors a part of a vector V22-W-1 to V22-W-9 that the component can express and is
# required to pass here only.

def known_transaction(tracker, kind, nonce, commitment, carrier, custody="IN_BLOCK"):
    """Record a transaction of a that is no binding authorization, where the component can."""
    if not hasattr(tracker, "record_transaction"):
        return None
    return tracker.record_transaction(SCOPE, at.Transaction(ACCOUNT, kind, nonce, commitment), carrier,
                                      custody=custody)


class PayloadSafetyBase(PrecursorBase):
    def rotate(self, nonce, signer_epoch, target_epoch, *, activating):
        return Authorization(ACCOUNT, "ROTATE", nonce, self.keys[target_epoch].commitment, activating=activating,
                             signer_commitment=self.keys[signer_epoch].commitment, epoch=target_epoch)

    def stealth(self, n=7):
        """A's stealth enrollment C_ext at migration_nonce 1, account nonce n, chain-finalized and reported."""
        c_ext = key_commitment("ext")
        f = AccountState(ACCOUNT, "e1" * 32, 30, 1990, 1, n, "PQ_BY_ENROLL", False, c_ext, 900, W, 850)
        wallet.observe_finalized(SCOPE, SEED, self.crypto, self.store, self.tracker, FinalizedView(f))
        state = canonical_state(13376, "11" * 32, "22" * 20, "f2" * 32, 1, status="PQ_BY_ENROLL",
                                commitment=c_ext, timestamp=2000, fork_time=900, override_window=W, enrolled_at=850)
        h = AccountState(ACCOUNT, "f2" * 32, 31, 2000, 1, n, "PQ_BY_ENROLL", False, c_ext, 900, W, 850)
        return c_ext, f, state, h

    def tx_element(self, epoch, nonce):
        return at.PayloadElement("TRANSACTION", self.signed(epoch, nonce, False), account_nonce=nonce)


class PayloadSafetyConditionTests(PayloadSafetyBase):
    """34.2 rule 1 (a): K holds the owner's transactions that have left a device; O the transactions of other
    parties; the starts are the head, F and every seen block (V22-W-5 (vi), V22-W-8)."""

    def test_r4_red01_v22w5_vi_a_rotate_two_nonces_above_is_reached_through_the_owners_transaction(self):
        n, k0 = 5, self.keys[0].commitment
        state1 = self.canonical(1, 0, "c5")
        h1 = head(block_hash="c5" * 32, number=30, timestamp=3000, account_nonce=n, commitment=k0, fork_time=None)
        self.tracker.observe_head(SCOPE, h1)
        key1 = scan_current_key(SCOPE, state1, lambda e: self.keys[e].commitment).current_key
        # Branch 1: W's activation A0 at n and its ordinary 0x7c T1 at n + 1 leave as one payload, then W sends
        # R at n + 2, signed by K_0, rotating to K_1 (V22-W-5 (vi)).
        pair = wallet.prepare_activation_bundle(SCOPE, state1, self.store, key1, SEED, self.crypto, ACTIVATION_CONFIG,
                                                tracker=self.tracker, head=h1, through_account_nonce=n + 1)
        self.tracker.export_bundle(SCOPE, pair, lambda payload: "relay-1")
        h1b = replace(h1, block_hash="c6" * 32, number=32, timestamp=3024, account_nonce=n + 2, activated=True)
        self.tracker.observe_head(SCOPE, h1b)
        r = self.rotate(n + 2, 0, 1, activating=False)
        self.tracker.export(SCOPE, r, b"R-at-n+2-signed-by-K0", lambda raw: "relay-2", head=h1b)
        # A natural reorganization: branch 2 from F holds none of them. W records epoch 1.
        h2 = replace(h1, block_hash="c7" * 32, number=31, timestamp=3036)
        state2 = replace(state1, block_hash="c7" * 32)
        self.store.mark_compromised(SCOPE, 1, "W records epoch 1")
        self.tracker.observe_head(SCOPE, h2)
        key2 = scan_current_key(SCOPE, state2, lambda e: self.keys[e].commitment).current_key
        with self.assertRaises(ValueError) as caught:            # the lone activation is signed
            wallet.sign_activation(SCOPE, state2, self.store, key2, SEED, self.crypto, ACTIVATION_CONFIG,
                                   tracker=self.tracker, head=h2, transaction_nonce=n)
        self.assertEqual((getattr(caught.exception, "remedy", None), getattr(caught.exception, "token", "x")),
                         ("ONE_PAYLOAD_BUNDLE", None))
        try:
            bundle = wallet.prepare_activation_bundle(SCOPE, state2, self.store, key2, SEED, self.crypto,
                                                      ACTIVATION_CONFIG, tracker=self.tracker, head=h2)
        except ValueError as exc:                                # NO_TRACKED_ROTATE_NEEDS_A_BUNDLE
            self.fail(f"no payload for the rotate two account nonces above: {exc}")
        self.assertEqual([(e.kind, e.account_nonce) for e in bundle.elements],
                         [("ACTIVATION", n), ("TRANSACTION", n + 1), ("TRANSACTION", n + 2)])
        with self.assertRaisesRegex(ValueError, "BUNDLE_REVIVES_EXPOSED_AUTHORIZATION"):   # the pair of (iii)
            self.tracker.bundle_preview(SCOPE, at.OnePayloadBundle(h2, bundle.elements[:2]))
        payloads = []
        self.tracker.export_bundle(SCOPE, bundle, payloads.append)
        self.assertEqual(payloads, [tuple(e.carrier for e in bundle.elements)])

    def test_r4_red01_a_frozen_recovery_bundle_runs_through_the_rotates_account_nonce(self):
        state, h, s, p = self.v22w1()                            # frozen, account nonce 7; epoch 1 recorded
        # Branch 1 after S: W's A0 at 7 and T1 at 8 (one payload), then R at 9 signed by K_0, rotating to K_3.
        s1 = self.canonical(1, 0, "ab")
        h_s = self.head_for(s1, account_nonce=7, number=21, timestamp=2012)
        self.tracker.observe_head(SCOPE, h_s)
        key = scan_current_key(SCOPE, s1, lambda e: self.keys[e].commitment).current_key
        pair = wallet.prepare_activation_bundle(SCOPE, s1, self.store, key, SEED, self.crypto, ACTIVATION_CONFIG,
                                                tracker=self.tracker, head=h_s, through_account_nonce=8)
        self.tracker.export_bundle(SCOPE, pair, lambda payload: "relay")
        h_s2 = replace(h_s, block_hash="ac" * 32, number=23, timestamp=2036, account_nonce=9, activated=True)
        self.tracker.observe_head(SCOPE, h_s2)
        r = self.rotate(9, 0, 3, activating=False)
        self.tracker.export(SCOPE, r, b"R-at-9", lambda raw: "relay", head=h_s2)
        self.store.mark_compromised(SCOPE, 3, "K_3 exposed")
        self.tracker.observe_head(SCOPE, h)                      # the reorganization back to the frozen branch
        plan = self.plan(state)
        bundle = wallet.prepare_recovery_bundle(plan, SCOPE, state, self.store, self.tracker,
                                                activation_config=ACTIVATION_CONFIG, **self.bundle_kwargs(plan, h),
                                                **BALANCE)
        self.assertEqual([(e.kind, e.account_nonce) for e in bundle.elements],      # stops at 7
                         [("WRITE", None), ("ACTIVATION", 7), ("TRANSACTION", 8), ("TRANSACTION", 9)])
        payloads = []
        self.tracker.export_bundle(SCOPE, bundle, payloads.append, **BALANCE)
        self.assertEqual(len(payloads), 1)

    def test_r4_red02_v22w8_iii_an_override_that_the_enrolled_key_turns_into_a_rotates_precursor(self):
        n = 7
        c_ext, f, state, h = self.stealth(n)
        r = self.rotate(n + 1, 1, 2, activating=True)            # R at n + 1, signed by K_1, rotating to K_2
        self.tracker.record(SCOPE, r, b"R-of-branch-1", **IN_BLOCK)
        self.store.mark_compromised(SCOPE, 2, "W records epoch 2")
        notice = wallet.observe_head(SCOPE, SEED, self.crypto, self.store, self.tracker, h)
        plan = self.plan(state, **own_funds())                   # a fresh override at 1 committing C_1
        self.assertEqual(plan.key.commitment, self.keys[1].commitment)
        with self.assertRaises(ValueError) as caught:            # delivered alone
            wallet.export_recovery(plan, SCOPE, state, self.store, self.tracker, **self.export_kwargs(plan, h))
        self.assertEqual(self.sent, [])
        self.assertEqual(getattr(caught.exception, "revived", None), [[r.group_id, r.variant_id]])
        override = self.write(Authorization.from_pi(ACCOUNT, plan.pi, epoch=1), b"override-S-prime")
        bundle = at.OnePayloadBundle(h, (override, self.activation_element(1, n), self.tx_element(1, n + 1)))
        with self.assertRaisesRegex(ValueError, "BUNDLE_ACT_PREEMPTIBLE"):     # accepted
            self.tracker.bundle_preview(SCOPE, bundle, **BALANCE)
        payload = offer_for(notice, r).get("payload") or {}
        self.assertEqual(payload.get("first"),
                         "WRITE_COMMITTING_A_KEY_NOT_DERIVED_FROM_THE_SEED_AT_THE_CURRENT_MIGRATION_NONCE")

    def test_r4_red03_a_write_that_revives_a_rotate_through_the_owners_activation_is_held(self):
        n, k0 = 5, self.keys[0].commitment
        s2, s3 = self.pi_of(2, 0, expiry=2500), self.pi_of(3, 0, expiry=9000)
        for auth, raw in ((s2, b"S2"), (s3, b"S3")):
            self.tracker.record(SCOPE, auth, raw, **IN_BLOCK)
        # Branch 1 at migration_nonce 4 (C_0): W signs its activation A0 at n, then R at n + 1, which does not
        # activate, signed by K_0, rotating to K_4 (V22-W-6 with the owner's activation as the link).
        b1 = self.canonical(4, 0, "d4")
        h_b1 = head(block_hash="d4" * 32, number=38, timestamp=2400, migration_nonce=4, account_nonce=n,
                    commitment=k0, fork_time=None)
        self.tracker.observe_head(SCOPE, h_b1)
        key = scan_current_key(SCOPE, b1, lambda e: self.keys[e].commitment).current_key
        wallet.sign_activation(SCOPE, b1, self.store, key, SEED, self.crypto, ACTIVATION_CONFIG,
                               tracker=self.tracker, head=h_b1, transaction_nonce=n)
        h_b1b = replace(h_b1, block_hash="d5" * 32, number=39, timestamp=2412, account_nonce=n + 1, activated=True)
        self.tracker.observe_head(SCOPE, h_b1b)
        r = self.rotate(n + 1, 0, 4, activating=False)
        self.tracker.export(SCOPE, r, b"R-at-n+1", lambda raw: "relay", head=h_b1b)
        # Branch 2: V (nonce 1 -> C_1) chain-finalized; the head has X2 < 3000 < X3. W records epoch 4.
        self.store.mark_compromised(SCOPE, 4, "W records epoch 4")
        state = self.canonical(2, 1, "d1")
        h = head(block_hash="d1" * 32, number=40, timestamp=3000, migration_nonce=2, account_nonce=n,
                 commitment=self.keys[1].commitment, fork_time=None)
        self.tracker.observe_head(SCOPE, h)
        plan = self.plan(state)                                  # W2 at 2, committing C_2
        with self.assertRaises(ValueError) as caught:            # W2 delivered
            wallet.export_recovery(plan, SCOPE, state, self.store, self.tracker, **self.export_kwargs(plan, h))
        self.assertEqual(self.sent, [])
        self.assertEqual((caught.exception.revived, caught.exception.remedy),
                         ([[r.group_id, r.variant_id]], "ACTIVATE_CURRENT_KEY_FIRST"))
        # The retry guard reads the same condition: S3 at the head after W2 makes R includable through A0.
        after = replace(at.single_write_preview(Authorization.from_pi(ACCOUNT, plan.pi, epoch=2), h),
                        block_hash="d2" * 32, number=41, timestamp=3012)
        self.tracker.observe_head(SCOPE, after)
        self.assertFalse(self.tracker.resubmission_allowed(SCOPE, s3, after))

    def test_r4_v22w8_v_a_nonce_taken_in_a_block_that_is_not_chain_finalized(self):
        n = 7
        c_ext, f, state, h = self.stealth(n)
        r = self.rotate(n + 1, 1, 2, activating=True)
        self.tracker.record(SCOPE, r, b"R-of-branch-1", **IN_BLOCK)
        self.store.mark_compromised(SCOPE, 2, "W records epoch 2")
        # The canonical branch after F holds Z (n) and Z2 (n + 1) of the enrolled key, not chain-finalized.
        head_z = AccountState(ACCOUNT, "f3" * 32, 33, 2024, 1, n + 2, "PQ_BY_ENROLL", True, c_ext, 900, W, 850)
        state_z = canonical_state(13376, "11" * 32, "22" * 20, "f3" * 32, 1, status="PQ_BY_ENROLL", activated=True,
                                  commitment=c_ext, timestamp=2024, fork_time=900, override_window=W, enrolled_at=850)
        wallet.observe_head(SCOPE, SEED, self.crypto, self.store, self.tracker, head_z)
        self.assertFalse(binding_conditions_allow(r, at.single_write_preview(
            Authorization.from_pi(ACCOUNT, self.pi_of(1, 1).pi, epoch=1), head_z)))   # no block after H includes R
        plan = self.plan(state_z, **own_funds())
        with self.assertRaises(ValueError) as caught:            # judged at the head only, delivered
            wallet.export_recovery(plan, SCOPE, state_z, self.store, self.tracker,
                                   **self.export_kwargs(plan, head_z))
        self.assertEqual(self.sent, [])
        self.assertEqual(getattr(caught.exception, "revived", None), [[r.group_id, r.variant_id]])


class PayloadSafetyPrecursorTests(PayloadSafetyBase):
    """34.2 rule 1 (b), (f), (g): the act, the fee mode, the precursor that A holds
    (V22-W-2 (vii), V22-W-5 (vii), V22-W-9)."""

    def test_r4_red04_a_write_paid_by_a_is_no_sponsored_act_whatever_the_label(self):
        state, h, s, p = self.v22w2()
        recommit = self.pi_of(2, 1)                              # a fee-mode-0 PI, as the adapter prepares one
        self.assertEqual((s.pi[169], recommit.pi[169]), (0, 0))
        elements = (self.write(s, b"S-override-of-branch-1"), self.write(recommit, b"self-pay-recommit"))
        for label in (None, "SPONSOR"):
            with self.subTest(label=label), self.assertRaisesRegex(ValueError, "BUNDLE_ACT_PREEMPTIBLE"):
                self.tracker.bundle_preview(SCOPE, at.OnePayloadBundle(h, elements, fee_path=label))   # accepted
        sponsored_elements = (elements[0], self.write(sponsored(recommit), b"sponsored-recommit"))
        self.tracker.bundle_preview(SCOPE, at.OnePayloadBundle(h, sponsored_elements))

    def test_r4_red05_a_write_that_is_only_recorded_is_no_carrier_that_A_holds(self):
        state, h, s, p = self.v22w1(s_expiry=1500, timestamp=3000, block="f3")
        self.assertEqual(actions_for(self.tracker.observe_head(SCOPE, h), p), [HOLD_LABEL])
        plan = self.plan(state)
        self.tracker.record(SCOPE, Authorization.from_pi(ACCOUNT, plan.pi, epoch=0), b"S-prime-recorded-before-export")
        self.assertEqual(actions_for(self.tracker.observe_head(SCOPE, h), p), [HOLD_LABEL])   # the bundle
        with self.assertRaisesRegex(ValueError, "BUNDLE_FRESH_PRECURSOR_HELD"):
            wallet.prepare_recovery_bundle(plan, SCOPE, state, self.store, self.tracker,
                                           activation_config=ACTIVATION_CONFIG, **self.bundle_kwargs(plan, h), **BALANCE)

    def test_r4_red06_i_v22w9_a_carrier_is_judged_at_the_earliest_timestamp_after_the_head(self):
        state, h, s, p = self.v22w1(s_expiry=2005)               # X0 within one SLOT of the head (2000)
        self.assertEqual(actions_for(self.tracker.observe_head(SCOPE, h), p), [HOLD_LABEL])     # the bundle
        plan = self.plan(state)
        with self.assertRaisesRegex(ValueError, "BUNDLE_FRESH_PRECURSOR_HELD"):              # built
            wallet.prepare_recovery_bundle(plan, SCOPE, state, self.store, self.tracker,
                                           activation_config=ACTIVATION_CONFIG, **self.bundle_kwargs(plan, h), **BALANCE)
        # S itself, judged at head.timestamp + SLOT, is no element that a block after the head can include.
        with self.assertRaisesRegex(ValueError, "BUNDLE_ELEMENT_NOT_APPLICABLE"):
            self.tracker.bundle_preview(SCOPE, at.OnePayloadBundle(h, (self.write(s, b"S-of-branch-1"),
                                                                     self.activation_element(0, 7))), **BALANCE)

    def test_r4_red06_ii_v22w9_iii_a_fresh_carrier_never_outlives_what_A_holds(self):
        state, h, s, p = self.v22w1(s_expiry=2100)               # S can be included after the head until 2100
        plan = self.plan(state)                                  # a fresh recovery with expiry 5000 > X0
        payloads = []
        with self.assertRaisesRegex(ValueError, "BUNDLE_FRESH_PRECURSOR_OUTLIVES"):          # delivered
            bundle = wallet.prepare_recovery_bundle(plan, SCOPE, state, self.store, self.tracker,
                                                    activation_config=ACTIVATION_CONFIG,
                                                    **self.bundle_kwargs(plan, h), **BALANCE)
            self.tracker.export_bundle(SCOPE, bundle, payloads.append, **BALANCE)
        self.assertEqual(payloads, [])
        # The payload of V22-W-1 (iii) carries S itself.
        pair = at.OnePayloadBundle(h, (self.write(s, b"S-of-branch-1"), self.activation_element(0, 7)))
        self.tracker.export_bundle(SCOPE, pair, payloads.append, **BALANCE)
        self.assertEqual(len(payloads), 1)

    def test_r4_red07_the_remedy_for_a_revived_rotate_names_the_rotates_act(self):
        n = 7
        c_ext, f, state, h = self.stealth(n)
        r = self.rotate(n, 1, 2, activating=True)                # R at n, signed by K_1, rotating to K_2
        self.tracker.record(SCOPE, r, b"R-activating-at-n", **IN_BLOCK)
        self.store.mark_compromised(SCOPE, 2, "W records epoch 2")
        offer = offer_for(wallet.observe_head(SCOPE, SEED, self.crypto, self.store, self.tracker, h), r)
        plan = self.plan(state, **own_funds())
        with self.assertRaises(ValueError) as caught:
            wallet.export_recovery(plan, SCOPE, state, self.store, self.tracker, **self.export_kwargs(plan, h))
        remedy = getattr(caught.exception, "payload", None) or {}
        self.assertEqual([remedy.get(k) for k in ("kind", "first", "act")],      # kind PI, a sponsored act
                         [offer["payload"].get(k) for k in ("kind", "first", "act")])
        self.assertEqual(remedy.get("kind"), "ROTATE")
        self.assertEqual(self.sent, [])

    def own_enrollment_p7(self):
        """The override gate of the owner's own enrollment (C_0, linked), S expired, P exposed above,
        and R, an activating rotate at the account nonce signed by the key that the override commits."""
        c0, c1, c2, c4 = (key_commitment(x) for x in ("k0", "k1", "k2", "k4"))
        h = head(mode="PQ_BY_ENROLL", migration_nonce=1, commitment=c0, account_nonce=6, enrolled_at=950,
                 timestamp=2000, fork_time=10_000_000)
        s, p = pi_auth(1, c1, epoch=1, expiry=1500), pi_auth(2, c2, epoch=2, expiry=5000)
        r = Authorization(ACCOUNT, "ROTATE", 6, c4, activating=True, signer_commitment=c1, epoch=4)
        for auth, raw in ((s, b"S"), (p, b"P"), (r, b"R")):
            self.tracker.record(SCOPE, auth, raw, **IN_BLOCK)
        self.tracker.link_key(SCOPE, c0, 0)
        self.store.mark_compromised(SCOPE, 2, "K_2 exposed")
        self.store.mark_compromised(SCOPE, 4, "K_4 exposed")
        return h, s, p, r, pi_auth(1, c1, epoch=1, expiry=5000)

    def test_r4_test01_the_rotate_exception_needs_a_rotate_with_no_act_without_the_write(self):
        h, s, p, r, fresh = self.own_enrollment_p7()
        notice = self.tracker.observe_head(SCOPE, h)
        self.assertEqual(actions_for(notice, p), [HOLD_LABEL])
        self.assertEqual((offer_for(notice, r)["action"], offer_for(notice, r).get("first")),
                         ("OFFER_ACCOUNT_NONCE_CONSUMPTION", "ACTIVATION_OF_THE_CURRENT_KEY"))
        with self.assertRaises(ValueError) as caught:
            self.tracker.export(SCOPE, fresh, b"S-prime", self.sent.append, head=h)
        self.assertEqual(caught.exception.remedy, HOLD_REMEDY)    # ONE_PAYLOAD_BUNDLE
        payloads = []
        bundle = at.OnePayloadBundle(h, (self.write(fresh, b"S-prime"),
                                         at.PayloadElement("ACTIVATION", b"activation-K1-at-6",
                                                           commitment=fresh.commitment, account_nonce=6)))
        with self.assertRaisesRegex(ValueError, "BUNDLE_FRESH_PRECURSOR_HELD"):   # delivered
            self.tracker.export_bundle(SCOPE, bundle, payloads.append, **BALANCE)
        self.assertEqual((payloads, self.sent), ([], []))

    def test_r4_test02_a_rotate_that_no_write_makes_includable_lifts_no_wait(self):
        h = frozen_head(account_nonce=5)
        s, p = pi_auth(0, key_commitment("k0"), epoch=0, expiry=1500), pi_auth(1, key_commitment("k1"), epoch=1)
        r = Authorization(ACCOUNT, "ROTATE", 5, key_commitment("k4"), activating=True,
                          signer_commitment=key_commitment("k9"), epoch=4)       # no write commits k9
        for auth, raw in ((s, b"S"), (p, b"P"), (r, b"R")):
            self.tracker.record(SCOPE, auth, raw, **IN_BLOCK)
        self.store.mark_compromised(SCOPE, 1, "K_1 exposed")
        self.store.mark_compromised(SCOPE, 4, "K_4 exposed")
        notice = self.tracker.observe_head(SCOPE, h)
        self.assertEqual(actions_for(notice, p), [HOLD_LABEL])   # OFFER_ONE_PAYLOAD_BUNDLE
        self.assertEqual(actions_for(notice, r), ["WAIT_FINALITY_WATCH_REORG"])
        self.assertIs(offer_for(notice, r).get("no_write_at_the_head_makes_it_includable"), True)

    def test_r4_test06_v22w1_iv_the_wait_ends_at_a_chain_finalized_block_not_at_a_head_past_x(self):
        state, h, s, p = self.v22w1(s_expiry=1500, timestamp=6100, block="fa")   # the head is past X = 6000
        plan = wallet.prepare_recovery(SCOPE, state, self.store, SEED, self.crypto, tracker=self.tracker,
                                       domain_tag=DOMAIN, verifier_version=VERSION, expiry=9000, max_account_fee=FEE)
        with self.assertRaises(ValueError) as caught:            # delivered at the head past X
            wallet.export_recovery(plan, SCOPE, state, self.store, self.tracker, **self.export_kwargs(plan, h))
        self.assertEqual((getattr(caught.exception, "remedy", None), self.sent), (HOLD_REMEDY, []))
        f = AccountState(ACCOUNT, "fb" * 32, 50, 5990, 0, 7, "LEGACY", False, None, 900, W, 0)
        self.assertNotIn(p.variant_id, [v for _, v, _ in self.tracker.observe_finalized(SCOPE, FinalizedView(f))])
        later = canonical_state(13376, "11" * 32, "22" * 20, "fc" * 32, 0, timestamp=6200, fork_time=900,
                                override_window=W)
        h2 = self.head_for(later, account_nonce=7, number=52)
        self.tracker.observe_head(SCOPE, h2)
        plan2 = wallet.prepare_recovery(SCOPE, later, self.store, SEED, self.crypto, tracker=self.tracker,
                                        domain_tag=DOMAIN, verifier_version=VERSION, expiry=9000, max_account_fee=FEE)
        with self.assertRaises(ValueError):                      # F (5990) has not passed X: still held
            wallet.export_recovery(plan2, SCOPE, later, self.store, self.tracker, **self.export_kwargs(plan2, h2))
        f2 = replace(f, block_hash="fd" * 32, number=53, timestamp=6212)
        self.assertIn((p.group_id, p.variant_id, "PI_EXPIRED"),
                      list(self.tracker.observe_finalized(SCOPE, FinalizedView(f2, f.block_hash))))
        wallet.export_recovery(plan2, SCOPE, later, self.store, self.tracker, **self.export_kwargs(plan2, h2))
        self.assertEqual(len(self.sent), 1)

    def test_r4_test07_v22w7_after_the_0x7d_alone_the_act_is_the_advance_not_the_activation(self):
        c0, c1 = key_commitment("k0"), key_commitment("k1")
        h = head(mode="PQ_BY_ENROLL", migration_nonce=1, commitment=c0, account_nonce=1, enrolled_at=1000,
                 timestamp=1012, fork_time=None)
        e, p = Authorization(ACCOUNT, "ENROLL", 0, c0, epoch=0), pi_auth(1, c1, epoch=1)
        for auth, raw in ((e, b"E"), (p, b"P")):
            self.tracker.record(SCOPE, auth, raw, **IN_BLOCK)
        self.store.mark_compromised(SCOPE, 1, "K_1 exposed")
        offer = offer_for(self.tracker.observe_head(SCOPE, h), p)
        self.assertEqual(offer["action"], "OFFER_ADVANCE_PAST_PI_NONCE")   # the combined label
        self.assertIs(offer.get("activation_discharges"), False)

    def test_r4_v22w2_vii_the_owners_own_enrollment_waits_whether_x_falls_before_or_after_d(self):
        c0 = self.keys[0].commitment
        for label, x in (("X before d", EXPIRY), ("X after d", 40_000_000)):
            with self.subTest(label):
                self.fresh_wallet(label.replace(" ", "-"))
                h = AccountState(ACCOUNT, "f2" * 32, 31, 2000, 1, 7, "PQ_BY_ENROLL", False, c0, 900, W, 850)
                self.tracker.link_key(SCOPE, c0, 0)              # the owner's own enrollment (V22-W-2 (vi))
                s, p = self.pi_of(1, 1, expiry=1500), self.learned_pi(2, 2, expiry=x)
                self.tracker.record(SCOPE, s, b"S-of-branch-1", **IN_BLOCK)
                wallet.learn_authorization(SCOPE, SEED, self.crypto, self.store, self.tracker, p, b"P")
                self.store.mark_compromised(SCOPE, 2, "W records epoch 2")
                offer = offer_for(wallet.observe_head(SCOPE, SEED, self.crypto, self.store, self.tracker, h), p)
                self.assertEqual(offer["action"], HOLD_LABEL)
                with self.assertRaises(ValueError) as caught:
                    self.tracker.export(SCOPE, self.pi_of(1, 1), b"S-prime", self.sent.append, head=h)
                self.assertEqual((caught.exception.remedy, self.sent), (HOLD_REMEDY, []))

    def test_r4_v22w5_vii_a_fresh_precursor_of_a_rotate_takes_the_write_of_c_ind(self):
        n = 7
        for variant in ("A0 and R at n + 1", "R activating at n"):
            with self.subTest(variant):
                self.fresh_wallet(variant.replace(" ", "-").replace("+", "p"))
                state = canonical_state(13376, "11" * 32, "22" * 20, "a9" * 32, 0,
                                        timestamp=3000, fork_time=900, override_window=W)
                h = self.head_for(state, account_nonce=n)
                s = self.pi_of(0, 0, expiry=1500)                # S expired: a recovery at 0 is fresh
                self.tracker.record(SCOPE, s, b"S-of-branch-1", **IN_BLOCK)
                if variant.startswith("A0"):
                    r = self.rotate(n + 1, 0, 1, activating=False)
                    known_transaction(self.tracker, "ACTIVATION", n, self.keys[0].commitment, b"A0-of-branch-1")
                else:
                    r = self.rotate(n, 0, 1, activating=True)
                self.tracker.record(SCOPE, r, b"R-of-branch-1", **IN_BLOCK)
                self.store.mark_compromised(SCOPE, 1, "W records epoch 1")
                offer = offer_for(wallet.observe_head(SCOPE, SEED, self.crypto, self.store, self.tracker, h), r)
                self.assertEqual(offer["action"], BUNDLE_LABEL)  # no wait: a rotate has no time bound
                self.assertEqual(offer["payload"]["first"],      # the write of C_0 and the activation of K_0
                                 "WRITE_COMMITTING_A_KEY_NOT_DERIVED_FROM_THE_SEED_AT_THE_CURRENT_MIGRATION_NONCE")
                fresh = self.pi_of(0, 0)
                elements = [self.write(fresh, b"S-prime"), self.activation_element(0, n)]
                if variant.startswith("A0"):
                    elements.append(self.tx_element(0, n + 1))
                with self.assertRaisesRegex(ValueError, "BUNDLE_PRECURSOR_HANDS_A_A_ROTATE"):   # accepted
                    self.tracker.bundle_preview(SCOPE, at.OnePayloadBundle(h, elements), **BALANCE)
                c_ind = key_commitment("ind")
                s_ind = pi_auth(0, c_ind, expiry=5000)
                ind = [self.write(s_ind, b"S-ind"),
                       at.PayloadElement("ACTIVATION", b"activation-of-K-ind", commitment=c_ind, account_nonce=n)]
                if variant.startswith("A0"):
                    ind.append(at.PayloadElement("TRANSACTION", b"tx-of-K-ind", commitment=c_ind, account_nonce=n + 1))
                payloads = []
                self.tracker.export_bundle(SCOPE, at.OnePayloadBundle(h, ind), payloads.append, **BALANCE)
                self.assertEqual(len(payloads), 1)

    def test_r4_test05_a_transaction_of_the_owners_that_left_a_device_takes_the_activation_as_act(self):
        c0, c1, c2 = key_commitment("k0"), key_commitment("k1"), key_commitment("k2")
        h = head(mode="PQ_BY_ENROLL", migration_nonce=1, commitment=c0, account_nonce=6, enrolled_at=950,
                 timestamp=2000, fork_time=10_000_000)
        s, p = pi_auth(1, c1, epoch=1), pi_auth(2, c2, epoch=2)
        for auth, raw in ((s, b"S"), (p, b"P")):
            self.tracker.record(SCOPE, auth, raw, **IN_BLOCK)
        self.tracker.link_key(SCOPE, c0, 0)
        self.store.mark_compromised(SCOPE, 2, "K_2 exposed")
        # 34.2 rule 1 (f): '... unless a transaction of the owner's at that account nonce has left a device'.
        known_transaction(self.tracker, "ACTIVATION", 6, c0, b"own-activation-of-K0-at-6-sent-by-another-device")
        payload = offer_for(self.tracker.observe_head(SCOPE, h), p)["payload"]
        self.assertEqual(payload.get("act"), "SPONSORED_WRITES_PAST_PI_MIGRATION_NONCE")   # the activation
        with self.assertRaisesRegex(ValueError, "BUNDLE_ACT_PREEMPTIBLE"):
            self.tracker.bundle_preview(SCOPE, at.OnePayloadBundle(h, (self.write(s, b"S"), at.PayloadElement(
                "ACTIVATION", b"activation-K1-at-6", commitment=c1, account_nonce=6))), **BALANCE)


class PayloadSafetyCoverageTests(PayloadSafetyBase):
    """Behaviours that a surviving mutant changed."""

    def test_cov4_rule6_a_revival_through_two_carriers_in_turn(self):
        h = head(migration_nonce=2, commitment=key_commitment("k1"), account_nonce=5, timestamp=3000, fork_time=None)
        u1, u2 = pi_auth(3, key_commitment("k3"), epoch=3, expiry=9000), pi_auth(4, key_commitment("k0"), epoch=0, expiry=9000)
        r = Authorization(ACCOUNT, "ROTATE", 5, key_commitment("k4"), activating=True,
                          signer_commitment=key_commitment("k0"), epoch=4)
        for auth, raw in ((u1, b"U1"), (u2, b"U2"), (r, b"R")):
            self.tracker.record(SCOPE, auth, raw, **IN_BLOCK)
        self.store.mark_compromised(SCOPE, 4, "K_4 exposed")
        self.tracker.observe_head(SCOPE, h)
        w2 = pi_auth(2, key_commitment("k2"), epoch=2, expiry=9000)
        two = at.single_write_preview(u1, at.single_write_preview(w2, h))
        self.assertFalse(binding_conditions_allow(r, two))       # one carrier is not enough
        self.assertTrue(binding_conditions_allow(r, at.single_write_preview(u2, two)))
        with self.assertRaises(ValueError) as caught:
            self.tracker.export(SCOPE, w2, b"W2", self.sent.append, head=h)
        self.assertEqual((caught.exception.revived, self.sent), ([[r.group_id, r.variant_id]], []))

    def test_cov4_an_unscheduled_T_keeps_the_wait_in_the_override_gate(self):
        h = head(mode="PQ_BY_ENROLL", migration_nonce=1, commitment=key_commitment("ext"), account_nonce=6,
                 enrolled_at=950, timestamp=2000, fork_time=None)
        s, p = pi_auth(1, key_commitment("k1"), epoch=1, expiry=1500), pi_auth(2, key_commitment("k2"), epoch=2)
        for auth, raw in ((s, b"S"), (p, b"P")):
            self.tracker.record(SCOPE, auth, raw, **IN_BLOCK)
        self.store.mark_compromised(SCOPE, 2, "K_2 exposed")
        self.assertEqual(actions_for(self.tracker.observe_head(SCOPE, h), p), [HOLD_LABEL])

    def test_cov4_a_learned_carrier_counts_as_one_that_A_holds(self):
        h = frozen_head(account_nonce=5)
        other = pi_auth(0, key_commitment("kx"), expiry=5000)    # another device's write, learned without epoch
        p = pi_auth(1, key_commitment("k1"), epoch=1)
        # Learned on chain through the adapter: its carrier is in a block (custody IN_BLOCK by default).
        wallet.learn_authorization(SCOPE, SEED, self.crypto, self.store, self.tracker, other, b"S-of-another-device")
        self.tracker.record(SCOPE, p, b"P", **IN_BLOCK)
        self.store.mark_compromised(SCOPE, 1, "K_1 exposed")
        offer = offer_for(self.tracker.observe_head(SCOPE, h), p)
        self.assertEqual((offer["action"], offer["payload"].get("fresh_precursor")), (BUNDLE_LABEL, False))

    def test_cov4_the_owners_own_enrollment_takes_the_activation_as_the_act(self):
        c0, c1, c2 = key_commitment("k0"), key_commitment("k1"), key_commitment("k2")
        h = head(mode="PQ_BY_ENROLL", migration_nonce=1, commitment=c0, account_nonce=6, enrolled_at=950,
                 timestamp=2000, fork_time=10_000_000)
        s, p = pi_auth(1, c1, epoch=1), pi_auth(2, c2, epoch=2)
        for auth, raw in ((s, b"S"), (p, b"P")):
            self.tracker.record(SCOPE, auth, raw, **IN_BLOCK)
        self.tracker.link_key(SCOPE, c0, 0)
        self.store.mark_compromised(SCOPE, 2, "K_2 exposed")
        payload = offer_for(self.tracker.observe_head(SCOPE, h), p)["payload"]
        self.assertEqual(payload.get("act"), "ACTIVATION_OF_THE_KEY_THE_WRITE_COMMITS")
        preview = self.tracker.bundle_preview(SCOPE, at.OnePayloadBundle(h, (self.write(s, b"S"), at.PayloadElement(
            "ACTIVATION", b"activation-K1-at-6", commitment=c1, account_nonce=6))), **BALANCE)
        self.assertEqual(preview.get("preemptions") or [], [])

    def test_cov4_an_own_enrolled_key_known_exposed_lets_another_party_send(self):
        c0, c1, c2 = key_commitment("k0"), key_commitment("k1"), key_commitment("k2")
        h = head(mode="PQ_BY_ENROLL", migration_nonce=1, commitment=c0, account_nonce=6, enrolled_at=950,
                 timestamp=2000, fork_time=10_000_000)
        s, p = pi_auth(1, c1, epoch=1), pi_auth(2, c2, epoch=2)
        for auth, raw in ((s, b"S"), (p, b"P")):
            self.tracker.record(SCOPE, auth, raw, **IN_BLOCK)
        self.tracker.link_key(SCOPE, c0, 0)
        self.store.mark_compromised(SCOPE, 2, "K_2 exposed")
        self.tracker.mark_exposed(SCOPE, ACCOUNT, c0, "the owner's enrolled key exposed")
        payload = offer_for(self.tracker.observe_head(SCOPE, h), p)["payload"]
        self.assertEqual(payload.get("act"), "SPONSORED_WRITES_PAST_PI_MIGRATION_NONCE")
        with self.assertRaisesRegex(ValueError, "BUNDLE_ACT_PREEMPTIBLE"):
            self.tracker.bundle_preview(SCOPE, at.OnePayloadBundle(h, (self.write(s, b"S"), at.PayloadElement(
                "ACTIVATION", b"activation-K1-at-6", commitment=c1, account_nonce=6))), **BALANCE)

    def test_cov4_a_rotate_that_the_precursor_makes_includable_lifts_the_wait(self):
        h = frozen_head(account_nonce=5)
        s, p = pi_auth(0, key_commitment("k0"), epoch=0, expiry=1500), pi_auth(1, key_commitment("k1"), epoch=1)
        r = Authorization(ACCOUNT, "ROTATE", 5, key_commitment("k4"), activating=True,
                          signer_commitment=key_commitment("k0"), epoch=4)
        for auth, raw in ((s, b"S"), (p, b"P"), (r, b"R")):
            self.tracker.record(SCOPE, auth, raw, **IN_BLOCK)
        self.store.mark_compromised(SCOPE, 1, "K_1 exposed")
        self.store.mark_compromised(SCOPE, 4, "K_4 exposed")
        self.assertEqual(actions_for(self.tracker.observe_head(SCOPE, h), p), [BUNDLE_LABEL])
        with self.assertRaises(ValueError) as caught:
            self.tracker.export(SCOPE, pi_auth(0, key_commitment("k0"), epoch=0), b"S-prime", self.sent.append, head=h)
        self.assertEqual(caught.exception.remedy, "ONE_PAYLOAD_BUNDLE")


class PayloadSafetyVectorTests(PayloadSafetyBase):
    """Vector parts of V22-W-1 to V22-W-9 that the component can express (wallet parts, model consensus)."""

    def test_v22_w1_ii_the_activation_after_S_makes_P_fail_check_5(self):
        state, h, s, p = self.v22w1()
        end = self.tracker.bundle_preview(SCOPE, at.OnePayloadBundle(
            h, (self.write(s, b"S"), self.activation_element(0, 7))), **BALANCE)["end_state"]
        end = AccountState.from_dict(end)
        self.assertTrue(end.activated and end.binding_final)
        self.assertFalse(binding_conditions_allow(p, end))

    def test_v22_w1_iii_the_offer_shows_X0_and_X_and_never_S_alone(self):
        state, h, s, p = self.v22w1(s_expiry=4000)
        offer = offer_for(self.tracker.observe_head(SCOPE, h), p)
        self.assertEqual(offer["time_left"], {"pi_expiry": 6000, "precursor_expiry": 4000})
        self.assertEqual(offer["payload"]["route"], "PRIVATE_RELAY")
        with self.assertRaises(ValueError) as caught:
            self.tracker.export(SCOPE, s, b"S-of-branch-1", self.sent.append, head=h)
        self.assertEqual((caught.exception.remedy, caught.exception.token), ("ONE_PAYLOAD_BUNDLE", None))

    def test_v22_w2_vi_the_owners_own_enrollment_takes_the_activation(self):
        c0 = self.keys[0].commitment
        h = AccountState(ACCOUNT, "f2" * 32, 31, 2000, 1, 7, "PQ_BY_ENROLL", False, c0, 900, W, 850)
        self.tracker.link_key(SCOPE, c0, 0)
        s, p = self.pi_of(1, 1), self.learned_pi(2, 2)
        self.tracker.record(SCOPE, s, b"S", **IN_BLOCK)
        wallet.learn_authorization(SCOPE, SEED, self.crypto, self.store, self.tracker, p, b"P")
        self.store.mark_compromised(SCOPE, 2, "W records epoch 2")
        self.tracker.observe_head(SCOPE, h)
        payloads = []
        self.tracker.export_bundle(SCOPE, at.OnePayloadBundle(h, (self.write(s, b"S"), self.activation_element(1, 7))),
                                   payloads.append, **BALANCE)
        self.assertEqual(len(payloads), 1)

    def test_v22_w5_v_the_owners_activation_links_S_to_R_so_S_goes_with_its_acts(self):
        n = 7
        state, h, s, p = self.v22w1()
        r = self.rotate(n + 1, 0, 3, activating=False)
        known_transaction(self.tracker, "ACTIVATION", n, self.keys[0].commitment, b"A0-of-branch-1")
        self.tracker.record(SCOPE, r, b"R-of-branch-1", **IN_BLOCK)
        self.store.mark_compromised(SCOPE, 3, "W records epoch 3")
        self.tracker.observe_head(SCOPE, h)
        with self.assertRaises(ValueError) as caught:
            self.tracker.export(SCOPE, s, b"S-of-branch-1", self.sent.append, head=h)
        self.assertIn([r.group_id, r.variant_id], caught.exception.revived)
        plan = self.plan(state)
        bundle = wallet.prepare_recovery_bundle(plan, SCOPE, state, self.store, self.tracker,
                                                activation_config=ACTIVATION_CONFIG, **self.bundle_kwargs(plan, h),
                                                **BALANCE)
        self.assertEqual([(e.kind, e.account_nonce) for e in bundle.elements],
                         [("WRITE", None), ("ACTIVATION", n), ("TRANSACTION", n + 1)])

    def test_v22_w6_iv_a_batch_carrier_re_wrapped_whole_is_the_same_pi(self):
        n = 5
        s3 = self.pi_of(3, 0, expiry=9000)
        r = self.rotate(n, 0, 4, activating=True)
        self.tracker.record(SCOPE, s3, b"B3: a 0x7f of W carrying the entry of S3", **IN_BLOCK)
        self.tracker.record(SCOPE, r, b"R", **IN_BLOCK)
        self.store.mark_compromised(SCOPE, 4, "W records epoch 4")
        f = AccountState(ACCOUNT, "d1" * 32, 40, 3000, 2, n, "PQ_BY_PROOF", False, self.keys[1].commitment, None, W, 0)
        self.tracker.observe_finalized(SCOPE, FinalizedView(f))
        b3 = hashlib.sha256(b"B3: a 0x7f of W carrying the entry of S3").hexdigest()
        h = replace(f, block_hash="d3" * 32, number=41, timestamp=3012)
        self.tracker.observe_head(SCOPE, h, inclusions=[(s3.group_id, s3.variant_id, b3, "SKIPPED", 2)])
        self.assertIsNone(self.tracker.records(SCOPE)[s3.group_id][s3.variant_id]["ended"])
        plan = self.plan(self.canonical(2, 1, "d3"))
        with self.assertRaises(ValueError) as caught:
            wallet.export_recovery(plan, SCOPE, self.canonical(2, 1, "d3"), self.store, self.tracker,
                                   **self.export_kwargs(plan, h))
        self.assertEqual(caught.exception.revived, [[r.group_id, r.variant_id]])

    def test_v22_w7_ii_after_A_own_0x7d_the_sponsored_write_still_applies(self):
        h = frozen_head(fork_time=None, timestamp=1000, account_nonce=0)
        e, p = Authorization(ACCOUNT, "ENROLL", 0, self.keys[0].commitment, epoch=0), self.learned_pi(1, 1)
        self.tracker.record(SCOPE, e, b"E", **IN_BLOCK)
        wallet.learn_authorization(SCOPE, SEED, self.crypto, self.store, self.tracker, p, b"P")
        self.store.mark_compromised(SCOPE, 1, "W records epoch 1")
        self.tracker.observe_head(SCOPE, h)
        preview = self.tracker.bundle_preview(SCOPE, at.OnePayloadBundle(
            h, (self.write(e, b"E"), self.write(sponsored(self.pi_of(1, 0)), b"S1"))))
        by = {x["by"]: x for x in preview["preemptions"]}
        end = AccountState.from_dict(by["0x7D_OF_A_AT_THE_ACCOUNT_NONCE"]["end_state"])
        self.assertEqual((end.mode, end.migration_nonce), ("PQ_BY_PROOF", 2))
        self.assertFalse(binding_conditions_allow(p, end))

    def test_v22_w8_iv_the_override_with_a_sponsored_recommit_of_c_ind(self):
        n = 7
        c_ext, f, state, h = self.stealth(n)
        s = self.pi_of(1, 1)
        r = self.rotate(n + 1, 1, 2, activating=True)
        self.tracker.record(SCOPE, s, b"S-of-branch-1", **IN_BLOCK)
        self.tracker.record(SCOPE, r, b"R-of-branch-1", **IN_BLOCK)
        self.store.mark_compromised(SCOPE, 2, "W records epoch 2")
        wallet.observe_head(SCOPE, SEED, self.crypto, self.store, self.tracker, h)
        c_ind = key_commitment("ind")
        recommit = sponsored(Authorization.from_pi(ACCOUNT, wallet._pi(self.canonical(2, 0, "e0"), replace(
            self.keys[0], commitment=c_ind), DOMAIN, VERSION, EXPIRY, FEE)))
        payloads = []
        self.tracker.export_bundle(SCOPE, at.OnePayloadBundle(h, (
            self.write(s, b"S"), self.write(recommit, b"sponsored-recommit-of-C-ind"),
            at.PayloadElement("ACTIVATION", b"activation-of-K-ind", commitment=c_ind, account_nonce=n))),
            payloads.append, **BALANCE)
        self.assertEqual(len(payloads), 1)
        with self.assertRaisesRegex(ValueError, "BUNDLE_ACT_PREEMPTIBLE"):
            self.tracker.bundle_preview(SCOPE, at.OnePayloadBundle(h, (self.write(s, b"S"), self.activation_element(1, n))),
                                        **BALANCE)


class PayloadSafetyMutationTests(PayloadSafetyBase):
    """Behaviours that a mutation run found unpinned."""

    def test_r4_g_a_legacy_account_before_T_whose_key_is_unpublished_waits(self):
        h = frozen_head(fork_time=9_000_000, timestamp=1000, account_nonce=0)    # before T; a has never signed
        p = pi_auth(1, key_commitment("k1"), epoch=1)            # a leaf of another device, with an aggregator
        self.tracker.record(SCOPE, p, b"P-leaf-with-an-aggregator", custody="AGGREGATOR")
        self.store.mark_compromised(SCOPE, 1, "K_1 exposed")
        self.assertEqual(actions_for(self.tracker.observe_head(SCOPE, h), p), [HOLD_LABEL])   # the bundle
        e = Authorization(ACCOUNT, "ENROLL", 0, key_commitment("k0"), epoch=0)
        with self.assertRaises(ValueError) as caught:
            self.tracker.export(SCOPE, e, b"E-fresh", self.sent.append, head=h)
        self.assertEqual((caught.exception.remedy, self.sent), (HOLD_REMEDY, []))
        if hasattr(self.tracker, "mark_secp256k1_published"):
            # Once a's key is published (l. 45), A can write its own 0x7d: the payload goes at once (reading (h)).
            self.tracker.mark_secp256k1_published(SCOPE, ACCOUNT, "a permit signature in calldata")
            self.assertEqual(actions_for(self.tracker.observe_head(SCOPE, h), p), [BUNDLE_LABEL])

    def test_r4_a_an_owners_ecdsa_transaction_reveals_the_key_that_A_lacks(self):
        h = frozen_head(fork_time=9_000_000, timestamp=1000, account_nonce=0)    # before T; a has never signed
        p = pi_auth(1, key_commitment("k1"), epoch=1)            # a leaf of another device, with an aggregator
        r = Authorization(ACCOUNT, "ROTATE", 2, key_commitment("k9"), activating=False,
                          signer_commitment=key_commitment("k8"), epoch=9)
        self.tracker.record(SCOPE, p, b"P-leaf-with-an-aggregator", custody="AGGREGATOR")
        self.tracker.record(SCOPE, r, b"R-at-2", **IN_BLOCK)
        self.store.mark_compromised(SCOPE, 1, "K_1 exposed")
        self.store.mark_compromised(SCOPE, 9, "K_9 exposed")
        notice = self.tracker.observe_head(SCOPE, h)
        self.assertEqual(actions_for(notice, p), [HOLD_LABEL])
        # The owner's ECDSA transactions through R's account nonce reveal a's public key to whoever receives them
        # (l. 45): A then writes its own 0x7d and includes P, which A cannot do without them (34.2 rule 1 (a)).
        offer = offer_for(notice, r)
        self.assertIs(offer["payload"].get("meets_rule_1_a"), False)   # the ECDSA payload offered

    def test_cov4_a_frozen_recovery_that_A_holds_from_T_on_lifts_the_wait(self):
        h = frozen_head(fork_time=9_000_000, timestamp=1000, account_nonce=0)    # before T; a has never signed
        s = pi_auth(0, key_commitment("k0"), epoch=0, expiry=9_500_000)          # W's frozen recovery, for T
        p = pi_auth(1, key_commitment("k1"), epoch=1, expiry=9_600_000)
        self.tracker.record(SCOPE, s, b"S-handed-to-an-aggregator", custody="AGGREGATOR")
        self.tracker.record(SCOPE, p, b"P", **IN_BLOCK)
        self.store.mark_compromised(SCOPE, 1, "K_1 exposed")
        # A can include S from T on (the frozen gate, l. 261) and P after it: the 0x7d is no piece that A lacks.
        self.assertEqual(actions_for(self.tracker.observe_head(SCOPE, h), p), [BUNDLE_LABEL])

    def test_cov4_the_owners_ecdsa_transactions_answer_a_rotate_before_T(self):
        h = frozen_head(fork_time=None, timestamp=1000, account_nonce=0)
        e = Authorization(ACCOUNT, "ENROLL", 0, key_commitment("k0"), epoch=0)
        p = pi_auth(1, key_commitment("k1"), epoch=1)
        r = Authorization(ACCOUNT, "ROTATE", 2, key_commitment("k9"), activating=False,
                          signer_commitment=key_commitment("k8"), epoch=9)
        for auth, raw in ((e, b"E"), (p, b"P"), (r, b"R")):
            self.tracker.record(SCOPE, auth, raw, **IN_BLOCK)
        self.store.mark_compromised(SCOPE, 1, "K_1 exposed")
        self.store.mark_compromised(SCOPE, 9, "K_9 exposed")
        offer = offer_for(self.tracker.observe_head(SCOPE, h), r)
        payload = offer["payload"]
        self.assertEqual((offer["action"], payload["first"], payload["through_account_nonce"]),
                         (BUNDLE_LABEL, "TRANSACTION_OF_THE_LEGACY_ACCOUNT_AT_ITS_NONCE", 2))
        # A's own 0x7d after them is A's race (A signs it at any nonce), not something that the payload adds.
        self.assertNotIn("meets_rule_1_a", payload)
        self.assertNotIn("meets_rule_1_a", offer)

    def test_r4_f_the_activation_after_a_balance_taking_precursor_needs_the_balance_statement(self):
        state = canonical_state(13376, "11" * 32, "22" * 20, "f1" * 32, 0, timestamp=2000, fork_time=900,
                                override_window=W)
        h = self.head_for(state, account_nonce=7)
        s_o = sponsored(self.pi_of(0, 0))                        # W's sponsored frozen recovery, with an aggregator
        p = self.learned_pi(1, 1, expiry=6000)
        self.tracker.record(SCOPE, s_o, b"S-sponsored-with-an-aggregator", custody="AGGREGATOR")
        wallet.learn_authorization(SCOPE, SEED, self.crypto, self.store, self.tracker, p, b"P")
        self.store.mark_compromised(SCOPE, 1, "W records epoch 1")
        self.tracker.observe_head(SCOPE, h)
        fresh = self.pi_of(0, 0, expiry=EXPIRY - 1)               # self-pay (fee mode 0), bounded by S's expiry
        bundle = at.OnePayloadBundle(h, (self.write(fresh, b"S-prime"), self.activation_element(0, 7)))
        with self.assertRaises(ValueError) as caught:            # accepted (no balance condition)
            self.tracker.bundle_preview(SCOPE, bundle)
        self.assertIn("balance_covers_acts", str(caught.exception))   # 34.2 rule 1 (f), not (a)
        self.assertIn("BUNDLE_ACT_PREEMPTIBLE", str(caught.exception))
        self.tracker.bundle_preview(SCOPE, bundle, **BALANCE)

    def test_v22_w7_ii_a_rotate_signed_by_the_enrolled_key_reverts_while_final_does_not_hold(self):
        h = frozen_head(fork_time=None, timestamp=1000, account_nonce=0)    # T unscheduled: no finite deadline
        e = Authorization(ACCOUNT, "ENROLL", 0, key_commitment("k0"), epoch=0)
        r = Authorization(ACCOUNT, "ROTATE", 1, key_commitment("k5"), activating=True,
                          signer_commitment=key_commitment("k0"), epoch=5)
        self.tracker.record(SCOPE, r, b"R-activating-at-1", **IN_BLOCK)
        self.store.mark_compromised(SCOPE, 5, "K_5 exposed")
        self.tracker.observe_head(SCOPE, h)
        # After E the enrollment is not binding-final, so R's rotate frame reverts with NOT_FINAL (l. 328).
        self.tracker.export(SCOPE, e, b"E", self.sent.append, head=h)
        self.assertEqual(self.sent, [b"E"])

    def test_r4_red06_i_b_a_rotate_at_a_head_whose_next_block_closes_the_override_gate(self):
        n, d = 7, 900 + W
        c_ext = key_commitment("ext")
        h = AccountState(ACCOUNT, "f2" * 32, 31, d - 5, 1, n, "PQ_BY_ENROLL", False, c_ext, 900, W, 850)
        r = self.rotate(n, 1, 2, activating=True)                # signed by K_1, the key a write at 1 commits
        self.tracker.record(SCOPE, r, b"R-activating-at-n", **IN_BLOCK)
        self.store.mark_compromised(SCOPE, 2, "W records epoch 2")
        offer = offer_for(wallet.observe_head(SCOPE, SEED, self.crypto, self.store, self.tracker, h), r)
        # No block after the head can include a write at 1 (the gate closes at d, before head.timestamp + SLOT).
        self.assertEqual(offer["action"], "WAIT_FINALITY_WATCH_REORG")      # the write-first bundle

    def test_r4_v22w8_v_b_a_seen_block_is_a_start_without_F(self):
        n = 7
        c_ext = key_commitment("ext")
        h = AccountState(ACCOUNT, "f2" * 32, 31, 2000, 1, n, "PQ_BY_ENROLL", False, c_ext, 900, W, 850)
        r = self.rotate(n + 1, 1, 2, activating=True)
        self.tracker.record(SCOPE, r, b"R-of-branch-1", **IN_BLOCK)
        self.store.mark_compromised(SCOPE, 2, "W records epoch 2")
        wallet.observe_head(SCOPE, SEED, self.crypto, self.store, self.tracker, h)       # seen; no F is known
        head_z = AccountState(ACCOUNT, "f3" * 32, 33, 2024, 1, n + 2, "PQ_BY_ENROLL", True, c_ext, 900, W, 850)
        state_z = canonical_state(13376, "11" * 32, "22" * 20, "f3" * 32, 1, status="PQ_BY_ENROLL", activated=True,
                                  commitment=c_ext, timestamp=2024, fork_time=900, override_window=W, enrolled_at=850)
        wallet.observe_head(SCOPE, SEED, self.crypto, self.store, self.tracker, head_z)
        plan = self.plan(state_z, **own_funds())
        with self.assertRaises(ValueError):                      # judged at the head only, delivered
            wallet.export_recovery(plan, SCOPE, state_z, self.store, self.tracker, **self.export_kwargs(plan, head_z))
        self.assertEqual(self.sent, [])

    def test_r4_red01_the_activation_bundle_follows_the_offer_for_a_rotate_above(self):
        n, k0 = 5, self.keys[0].commitment
        state = self.canonical(1, 0, "c5")
        h = head(block_hash="c5" * 32, number=30, timestamp=3000, account_nonce=n, commitment=k0, fork_time=None)
        r = self.rotate(n + 2, 0, 1, activating=False)
        self.tracker.record(SCOPE, r, b"R-at-n+2", **IN_BLOCK)
        self.store.mark_compromised(SCOPE, 1, "W records epoch 1")
        offer = offer_for(self.tracker.observe_head(SCOPE, h), r)
        key = scan_current_key(SCOPE, state, lambda e: self.keys[e].commitment).current_key
        try:                                                     # 'sign the activation alone'
            bundle = wallet.prepare_activation_bundle(SCOPE, state, self.store, key, SEED, self.crypto,
                                                      ACTIVATION_CONFIG, tracker=self.tracker, head=h)
        except ValueError as exc:
            self.fail(f"no activation bundle for the offer {offer['payload']}: {exc}")
        self.assertEqual(bundle.elements[-1].account_nonce, offer["payload"]["through_account_nonce"])
        self.assertEqual([e.account_nonce for e in bundle.elements], [n, n + 1, n + 2])

    def test_cov4_custody_never_falls_once_a_carrier_is_out(self):
        state, h, s, p = self.v22w1()                            # S of branch 1 in a block
        self.tracker.record(SCOPE, s, b"S-of-branch-1")          # recorded again by a caller, custody unstated
        self.assertEqual(actions_for(self.tracker.observe_head(SCOPE, h), p), [BUNDLE_LABEL])

    def test_r4_f_the_write_of_c_ind_runs_past_a_same_key_step_that_A_holds(self):
        n = 7
        state = canonical_state(13376, "11" * 32, "22" * 20, "a9" * 32, 0, timestamp=3000, fork_time=900,
                                override_window=W)
        h = self.head_for(state, account_nonce=n)
        s, step = self.pi_of(0, 0, expiry=1500), self.pi_of(1, 0, expiry=9000)    # S expired; a same-key step at 1
        r = self.rotate(n, 0, 1, activating=True)
        for auth, raw in ((s, b"S-of-branch-1"), (step, b"same-key-step-of-branch-1"), (r, b"R-of-branch-1")):
            self.tracker.record(SCOPE, auth, raw, **IN_BLOCK)
        self.store.mark_compromised(SCOPE, 1, "W records epoch 1")
        payload = offer_for(wallet.observe_head(SCOPE, SEED, self.crypto, self.store, self.tracker, h), r)["payload"]
        # 34.2 rule 1 (f): the write of C_ind, then sponsored writes of it through migration_nonce 1, where the step
        # that commits K_0 again would otherwise restore the commitment that R needs (the activation of K_0).
        self.assertEqual((payload["first"], payload.get("sponsored_writes_of_c_ind_through_migration_nonce")),
                         ("WRITE_COMMITTING_A_KEY_NOT_DERIVED_FROM_THE_SEED_AT_THE_CURRENT_MIGRATION_NONCE", 1))
        self.assertNotIn("meets_rule_1_a", payload)

    def test_r4_f_a_member_of_k_that_takes_balance_can_preempt_the_transaction_after_an_activation(self):
        n, k0 = 5, self.keys[0].commitment
        state = self.canonical(1, 0, "c5")
        h = head(block_hash="c5" * 32, number=30, timestamp=3000, account_nonce=n, commitment=k0, fork_time=None)
        same_key = self.pi_of(1, 0)                              # W's unsponsored same-key step at 1, out in a block
        r = self.rotate(n + 1, 0, 1, activating=False)
        self.tracker.record(SCOPE, same_key, b"same-key-step-of-branch-1", **IN_BLOCK)
        self.tracker.record(SCOPE, r, b"R-at-n+1", **IN_BLOCK)
        self.store.mark_compromised(SCOPE, 1, "W records epoch 1")
        self.tracker.observe_head(SCOPE, h)
        key = scan_current_key(SCOPE, state, lambda e: self.keys[e].commitment).current_key
        bundle = wallet.prepare_activation_bundle(SCOPE, state, self.store, key, SEED, self.crypto, ACTIVATION_CONFIG,
                                                  tracker=self.tracker, head=h)
        # Anyone can re-price the same-key step and place it first, taking up to its max_account_fee from a's balance
        # (l. 285, l. 3070); the transaction at n + 1 can then fail while the activation applies (34.2 rule 1 (f)).
        with self.assertRaises(ValueError) as caught:            # accepted
            self.tracker.bundle_preview(SCOPE, bundle)
        self.assertIn("balance_covers_acts", str(caught.exception))
        self.tracker.bundle_preview(SCOPE, bundle, **BALANCE)

    def test_r4_red05_b_a_write_whose_delivery_failed_is_no_carrier_that_A_holds(self):
        state = canonical_state(13376, "11" * 32, "22" * 20, "f1" * 32, 0, timestamp=2000, fork_time=900,
                                override_window=W)
        h = self.head_for(state, account_nonce=7)
        self.tracker.observe_head(SCOPE, h)
        plan = self.plan(state)

        def failed(_):
            raise ConnectionError("the relay was unreachable")
        with self.assertRaises(ConnectionError):
            wallet.export_recovery(plan, SCOPE, state, self.store, self.tracker,
                                   **{**self.export_kwargs(plan, h), "deliver": failed})
        p = self.learned_pi(1, 1, expiry=6000)
        wallet.learn_authorization(SCOPE, SEED, self.crypto, self.store, self.tracker, p, b"P")
        self.store.mark_compromised(SCOPE, 1, "W records epoch 1")
        # The recovery was recorded before the delivery that failed: A does not hold it (34.2 rule 1 (g)).
        self.assertEqual(actions_for(self.tracker.observe_head(SCOPE, h), p), [HOLD_LABEL])   # the bundle


def offer_for_all(notice, auth):
    return [o for o in notice["offers"] if o.get("variant") == auth.variant_id]


# ------------------------------------------------------------------------------------------------
# Spec (commit 6cd01449) sections 35.2 (the payload plan, A-22-01), 35.3 (the end of a grouped rotate
# authorization per carrier, A-22-02) and 36.2 (the selection after a same-key advance inside a payload, A-23-01). A
# test_v23_ or test_v24_ test mirrors a part of a vector V23-W-1 to V23-W-5 or V24-W-1 that the component can express
# and is required here only.

def act(kind, fee_mode=0):
    """A planned act of the payload planner, or its kind name on a side that has none."""
    return wallet.PlannedAct(kind, fee_mode) if hasattr(wallet, "PlannedAct") else kind


def planned_writes(test, state, h, acts, *, current_key=None, own=False):
    """(PI.migration_nonce, commitment, epoch) of each write of the payload `acts` prepared at B (`state`, `h`).

    wallet.plan_payload, each act against its planning state (35.2 rule 1 (b), (c)). A side without a payload
    plan prepares every write against B, as 31.2 rules 1-2 read alone: prepare_recovery for a new key, prepare_recommit
    for the same key; a write that it cannot prepare there is None."""
    if hasattr(wallet, "plan_payload"):
        plan = wallet.plan_payload(SCOPE, state, test.store, SEED, test.crypto, tracker=test.tracker, head=h, acts=acts,
                                   domain_tag=DOMAIN, verifier_version=VERSION, expiry=EXPIRY, max_account_fee=FEE,
                                   current_key=current_key, **(own_kw() if own else {}))
        return [(e.migration_nonce, e.commitment, e.epoch) for e in plan.elements if e.kind == "WRITE"]
    out = []
    for x in acts:
        kind = getattr(x, "kind", x)
        if not kind.startswith("WRITE"):
            continue
        try:
            if kind == "WRITE_NEW_KEY":
                plan = test.plan(state)
            else:
                plan = wallet.prepare_recommit(SCOPE, state, test.store, current_key, SEED, test.crypto,
                                               tracker=test.tracker, domain_tag=DOMAIN, verifier_version=VERSION,
                                               expiry=EXPIRY, max_account_fee=FEE, confirm_extra_proof_and_fee=True)
            out.append((plan.nonce, plan.key.commitment, plan.key.epoch))
        except ValueError:
            out.append(None)
    return out


class PayloadPlanBase(PayloadSafetyBase):
    def setUp(self):
        super().setUp()
        self.keys.update({e: wallet.derive_key(SCOPE, SEED, e, self.crypto) for e in (6, 7)})

    def v24w1(self):
        """V24-W-1: B at migration_nonce 5 with the current key C_4 (the re-commit gate, account nonce 9), epoch 5
        recorded under 31.2 rule 7; the scan of B finds K_4."""
        state = self.canonical(5, 4, "b5")
        h = head(block_hash="b5" * 32, number=50, timestamp=3000, migration_nonce=5, account_nonce=9,
                 commitment=self.keys[4].commitment, fork_time=None)
        self.store.mark_compromised(SCOPE, 5, "epoch 5 recorded (31.2 rule 7)")
        self.tracker.observe_head(SCOPE, h)
        key = scan_current_key(SCOPE, state, lambda e: self.keys[e].commitment).current_key
        return state, h, key

    def split_and_back(self, h):
        """V23-W-4: a builder that split the payload included S alone (head `split`: migration_nonce 2, C_1); a
        reorganization then removed its block (head `back`, with B's values)."""
        split = AccountState(ACCOUNT, "f3" * 32, 32, 2012, 2, 7, "PQ_BY_PROOF", False, self.keys[1].commitment, 900, W, 850)
        self.tracker.observe_head(SCOPE, split)
        back = replace(h, block_hash="f4" * 32, number=32, timestamp=2024)
        back_state = canonical_state(13376, "11" * 32, "22" * 20, "f4" * 32, 1, status="PQ_BY_ENROLL",
                                     commitment=key_commitment("ext"), timestamp=2024, fork_time=900, override_window=W,
                                     enrolled_at=850)
        self.tracker.observe_head(SCOPE, back)
        return split, back, back_state

    def build(self, plan, state, h, **extra):
        return wallet.build_payload(plan, SCOPE, state, self.store, self.tracker, head=h, verify_proof=lambda p, pi: True,
                                    config=CONFIG, activation_config=ACTIVATION_CONFIG, seed64=SEED, crypto=self.crypto,
                                    **extra)

    def v23w5(self):
        """V23-W-5: R_act and R_plain, an activating and a non-activating rotate at account nonce n to the same target
        K_3, signed by K_0 on two branches; F shows final(a) and activated(a) with nonce(a) = n under K_0."""
        n, c_s, c_t = 6, self.keys[0].commitment, self.keys[3].commitment
        r_act = Authorization(ACCOUNT, "ROTATE", n, c_t, activating=True, signer_commitment=c_s, epoch=3)
        r_plain = Authorization(ACCOUNT, "ROTATE", n, c_t, activating=False, signer_commitment=c_s, epoch=3)
        self.tracker.record(SCOPE, r_act, b"R_act-signed-on-branch-1", **IN_BLOCK)
        self.tracker.record(SCOPE, r_plain, b"R_plain-signed-on-branch-2", **IN_BLOCK)
        f = AccountState(ACCOUNT, "d7" * 32, 40, 3000, 1, n, "PQ_BY_PROOF", True, c_s, None, W, 0)
        return n, r_act, r_plain, f


class PayloadPlanRegressionTests(PayloadPlanBase):
    """Sections 35.2, 35.3 and 36.2."""

    def test_r5_v23w1_the_re_commit_is_prepared_against_the_state_that_S_leaves(self):
        state, h, s, p = self.v22w2()                 # B: A's enrollment C_ext at migration_nonce 1; P at 2, epoch 2
        c1 = self.keys[1].commitment
        writes = planned_writes(self, state, h, [act("WRITE_NEW_KEY"), act("WRITE_SAME_KEY", 2)], own=True)
        # [(1, C_1, 1), None]: the same-key re-commit is read at B, whose key is A's C_ext, so none is prepared.
        self.assertEqual(writes, [(1, c1, 1), (2, c1, 1)])

    def test_r5_v23w1_a_same_key_re_commit_prepared_against_B_is_refused(self):
        state, h, s, p = self.v22w2()
        read_at_b = sponsored(pi_auth(2, key_commitment("ext")))      # 'the current key' read at B: A's C_ext
        s_el, payloads = self.write(s, b"S-override-of-branch-1"), []
        with self.assertRaisesRegex(ValueError, "PAYLOAD_ELEMENT_NOT_PREPARED_AGAINST_ITS_PLANNING_STATE"):
            self.tracker.export_bundle(SCOPE, at.OnePayloadBundle(h, (s_el, self.write(read_at_b, b"S2-read-at-B"))),
                                       payloads.append)      # delivered, binding a to A's enrolled key
        self.assertEqual(payloads, [])
        self.tracker.export_bundle(SCOPE, at.OnePayloadBundle(h, (s_el, self.write(sponsored(self.pi_of(2, 1)), b"S2"))),
                                   payloads.append)
        self.assertEqual(payloads, [(b"S-override-of-branch-1", b"S2")])

    def test_r5_v23w2_the_early_finalisation_is_prepared_against_the_state_that_E_leaves(self):
        state = canonical_state(13376, "11" * 32, "22" * 20, "a0" * 32, 0, timestamp=1000, fork_time=None,
                                override_window=W)
        h = self.head_for(state, account_nonce=3, number=10, timestamp=1000)     # LEGACY, before T (T unscheduled)
        self.tracker.observe_head(SCOPE, h)
        writes = planned_writes(self, state, h, [act("ENROLL"), act("WRITE_SAME_KEY", 2)])
        self.assertEqual(writes, [(1, self.keys[0].commitment, 0)])   # [None]: no write at a LEGACY B before T

    def test_r5_v24w1_the_selection_after_a_same_key_advance_uses_S_1(self):
        state, h, key = self.v24w1()
        writes = planned_writes(self, state, h, [act("WRITE_SAME_KEY"), act("WRITE_NEW_KEY")], current_key=key)
        # [(5, C_4, 4), None]: the selection for x_1 is read at B (as at S_0, before the step): epoch 5, recorded.
        self.assertEqual(writes, [(5, self.keys[4].commitment, 4), (6, self.keys[6].commitment, 6)])

    def test_r5_v24w1_a_key_that_x1_newly_selects_at_another_epoch_is_refused(self):
        state, h, key = self.v24w1()
        step = self.write(self.pi_of(5, 4), b"x0-same-key-step-of-C4")
        with self.assertRaisesRegex(ValueError, "PAYLOAD_KEY_NOT_SELECTED_AT_ITS_PLANNING_STATE"):   # accepted
            self.tracker.bundle_preview(SCOPE, at.OnePayloadBundle(h, (step, self.write(self.pi_of(6, 7), b"x1-C7"))),
                                        **BALANCE)
        self.tracker.bundle_preview(SCOPE, at.OnePayloadBundle(h, (step, self.write(self.pi_of(6, 6), b"x1-C6"))),
                                    **BALANCE)

    def test_r5_v24w1_a_payload_relabelled_to_a_head_with_another_current_key_is_refused(self):
        state, h, key = self.v24w1()
        elements = (self.write(self.pi_of(5, 4), b"x0-same-key-step-of-C4"), self.write(self.pi_of(6, 6), b"x1-C6"))
        self.tracker.bundle_preview(SCOPE, at.OnePayloadBundle(h, elements), **BALANCE)            # at B: one plan
        # A reorganization: B' holds migration_nonce 5 with C_3 (another device's same-key step of C_3 at 4), so x_0 is
        # no same-key write against its recomputed planning state and the payload is void (35.2 rule 1 (d)).
        moved = replace(h, block_hash="b6" * 32, number=51, commitment=self.keys[3].commitment)
        self.tracker.observe_head(SCOPE, moved)
        payloads = []
        with self.assertRaisesRegex(ValueError, "PAYLOAD_KEY_NOT_SELECTED_AT_ITS_PLANNING_STATE"):   # delivered
            self.tracker.export_bundle(SCOPE, at.OnePayloadBundle(moved, elements), payloads.append, **BALANCE)
        self.assertEqual(payloads, [])
        if hasattr(wallet, "replan_payload"):
            # The adapter's re-plan says the same: x_0 is no same-key write against its recomputed planning state.
            plan = wallet.plan_payload(SCOPE, state, self.store, SEED, self.crypto, tracker=self.tracker, head=h,
                                       acts=[act("WRITE_SAME_KEY"), act("WRITE_NEW_KEY")], domain_tag=DOMAIN,
                                       verifier_version=VERSION, expiry=EXPIRY, max_account_fee=FEE, current_key=key)
            moved_state = self.canonical(5, 3, "b6")
            replanned = wallet.replan_payload(plan, SCOPE, moved_state, self.store, SEED, self.crypto,
                                              tracker=self.tracker, head=moved)
            self.assertEqual((replanned.status, [v["changed"] for v in replanned.elements]),
                             ("VOID", [["SAME_KEY_MATCH"], []]))

    def test_r5_v23w4_after_its_predecessor_is_gone_the_re_commit_never_leaves_alone(self):
        state, h, s, p = self.v22w2()
        s2 = sponsored(self.pi_of(2, 1))                     # x_1, prepared against S_1
        self.tracker.export_bundle(SCOPE, at.OnePayloadBundle(h, (self.write(s, b"S-override-of-branch-1"),
                                                                  self.write(s2, b"S2-sponsored"))), lambda payload: "relay")
        split, back, back_state = self.split_and_back(h)
        with self.assertRaisesRegex(ValueError, "PREPARED_AGAINST_A_LATER_PLANNING_STATE"):   # delivered alone
            self.tracker.export(SCOPE, s2, b"S2-sponsored", self.sent.append, head=back)
        self.assertEqual(self.sent, [])
        self.assertFalse(self.tracker.resubmission_allowed(SCOPE, s2, back))                # True

    def test_r5_the_offer_names_each_acts_planning_state(self):
        state, h, s, p = self.v22w2()
        payload = offer_for(self.tracker.observe_head(SCOPE, h), p)["payload"]
        acts = (payload.get("plan") or {}).get("acts") or []           # the offer names no planning state
        c1 = self.keys[1].commitment.hex()
        self.assertEqual([(x["kind"], x.get("migration_nonce"), x.get("key"), x.get("commitment"), x.get("epoch"),
                           x["planning_state"]["migration_nonce"], x["planning_state"]["commitment"]) for x in acts],
                         [("WRITE", 1, "NEW_KEY_SELECTED_AT_ITS_PLANNING_STATE", c1, 1, 1, key_commitment("ext").hex()),
                          ("WRITE", 2, "SAME_KEY_AS_ITS_PLANNING_STATE", c1, 1, 2, c1)])
        self.assertEqual(payload["plan"]["anchor"], {"block_hash": h.block_hash, "number": h.number})
        # The frozen gate (V22-W-1 (iii)): S, then the activation of the key that S commits at S_1's account nonce.
        self.fresh_wallet("frozen-offer")
        state, h, s, p = self.v22w1()
        acts = offer_for(self.tracker.observe_head(SCOPE, h), p)["payload"]["plan"]["acts"]
        self.assertEqual([(x["kind"], x.get("migration_nonce"), x.get("account_nonce"), x.get("key"), x.get("reveals"))
                          for x in acts],
                         [("WRITE", 0, None, "NEW_KEY_SELECTED_AT_ITS_PLANNING_STATE", None),
                          ("ACTIVATION", None, 7, None, self.keys[0].commitment.hex())])
        self.assertEqual(acts[1]["planning_state"]["mode"], "PQ_BY_PROOF")


class PayloadPlanCoverageTests(PayloadPlanBase):
    """Behaviours that the text keeps."""

    def test_cov5_a_payload_rebound_unchanged_to_a_new_head_is_delivered(self):
        state, h, key = self.v24w1()
        elements = (self.write(self.pi_of(5, 4), b"x0"), self.write(self.pi_of(6, 6), b"x1"))
        again = replace(h, block_hash="b7" * 32, number=51)       # every bound value the same: rebound unchanged
        self.tracker.observe_head(SCOPE, again)
        payloads = []
        self.tracker.export_bundle(SCOPE, at.OnePayloadBundle(again, elements), payloads.append, **BALANCE)
        self.assertEqual(payloads, [(b"x0", b"x1")])

    def test_cov5_a_selection_that_reuses_the_skipped_epoch_is_refused(self):
        state, h, key = self.v24w1()
        with self.assertRaisesRegex(ValueError, "BUNDLE_ELEMENT_KEY_EXPOSED: element 1"):
            self.tracker.bundle_preview(SCOPE, at.OnePayloadBundle(h, (self.write(self.pi_of(5, 4), b"x0"),
                                                                       self.write(self.pi_of(6, 5), b"x1-epoch-5"))),
                                        **BALANCE)

    def test_cov5_elements_that_left_stay_tracked_whatever_becomes_of_their_payload(self):
        state, h, s, p = self.v22w2()
        s2 = sponsored(self.pi_of(2, 1))
        self.tracker.export_bundle(SCOPE, at.OnePayloadBundle(h, (self.write(s, b"S-override-of-branch-1"),
                                                                  self.write(s2, b"S2-sponsored"))), lambda payload: "relay")
        split, back, back_state = self.split_and_back(h)
        notice = self.tracker.observe_head(SCOPE, back)
        self.assertIn((s2.group_id, s2.variant_id), notice["pending"])
        record = self.tracker.records(SCOPE)[s2.group_id][s2.variant_id]
        self.assertIsNone(record["ended"])

    def test_cov5_the_recovery_bundle_signs_its_acts_against_their_planning_states(self):
        state, h, s, p = self.v22w1()                       # frozen at migration_nonce 0, account nonce 7
        plan = self.plan(state)
        bundle = wallet.prepare_recovery_bundle(plan, SCOPE, state, self.store, self.tracker,
                                                activation_config=ACTIVATION_CONFIG, through_account_nonce=8,
                                                **self.bundle_kwargs(plan, h), **BALANCE)
        # S_1 (after the 0x7e, which consumes no account nonce): the activation of K_0 at 7; S_2: a transaction at 8.
        self.assertEqual([(e.kind, e.account_nonce, e.commitment) for e in bundle.elements[1:]],
                         [("ACTIVATION", 7, self.keys[0].commitment), ("TRANSACTION", 8, self.keys[0].commitment)])
        self.assertEqual([e.carrier for e in bundle.elements[1:]], [self.signed(0, 7, True), self.signed(0, 8, False)])
        if hasattr(wallet, "plan_payload"):
            # The same payload as a plan, each act prepared against its planning state, has the same bytes.
            planned = wallet.plan_payload(SCOPE, state, self.store, SEED, self.crypto, tracker=self.tracker, head=h,
                                          acts=[act("WRITE_NEW_KEY"), act("ACTIVATION"), act("TRANSACTION")],
                                          domain_tag=DOMAIN, verifier_version=VERSION, expiry=EXPIRY,
                                          max_account_fee=FEE)
            self.assertEqual([(e.kind, e.account_nonce, e.epoch) for e in planned.elements],
                             [("WRITE", None, 0), ("ACTIVATION", 7, 0), ("TRANSACTION", 8, 0)])
            self.assertEqual([x[:4] for x in (e.planning_state for e in planned.elements)],
                             [("LEGACY", 0, 7, False), ("PQ_BY_PROOF", 1, 7, False), ("PQ_BY_PROOF", 1, 8, True)])
            built = self.build(planned, state, h, proofs={0: b"MODEL-PROOF-NOT-REAL"}, **BALANCE)
            self.assertEqual([e.carrier for e in built.elements], [e.carrier for e in bundle.elements])


class PayloadPlanVectorTests(PayloadPlanBase):
    """V23-W-1 to V23-W-5 and V24-W-1: the wallet parts (model proofs and carriers, model consensus)."""

    def test_v23_w1_the_plan_holds_S_and_the_re_commit_and_both_apply_in_one_block(self):
        state, h, s, p = self.v22w2()
        c1 = self.keys[1].commitment
        plan = wallet.plan_payload(SCOPE, state, self.store, SEED, self.crypto, tracker=self.tracker, head=h,
                                   acts=[act("WRITE_NEW_KEY"), act("WRITE_SAME_KEY", 2)], domain_tag=DOMAIN,
                                   verifier_version=VERSION, expiry=EXPIRY, max_account_fee=FEE, **own_kw())
        x0, x1 = plan.elements
        self.assertEqual(x0.pi, s.pi)                         # S itself: an unchanged PI keeps its proof
        self.assertEqual((x1.migration_nonce, x1.commitment, x1.epoch, x1.pi[169]), (2, c1, 1, 2))
        self.assertEqual(x1.planning_state, ("PQ_BY_PROOF", 2, 7, False, c1.hex()))
        bundle = self.build(plan, state, h, proofs={0: b"MODEL-PROOF-OF-S", 1: b"MODEL-PROOF-OF-S2"},
                            carriers={1: b"sponsored-carrier-of-S2"})
        end = self.tracker.bundle_preview(SCOPE, bundle)["end_state"]
        self.assertEqual((end["mode"], end["migration_nonce"], end["commitment"], end["activated"]),
                         ("PQ_BY_PROOF", 3, c1.hex(), False))     # Migrated(a, 0x01, C_1, 3, false, true) after S_2
        payloads = []
        self.tracker.export_bundle(SCOPE, bundle, payloads.append)
        self.assertEqual(payloads, [tuple(e.carrier for e in bundle.elements)])
        f = AccountState(ACCOUNT, "e3" * 32, 32, 2012, 3, 7, "PQ_BY_PROOF", False, c1, 900, W, 850)
        self.assertIn((p.group_id, p.variant_id, "MIGRATION_NONCE_CONSUMED"),
                      list(self.tracker.observe_finalized(SCOPE, FinalizedView(f, "e1" * 32))))

    def test_v23_w2_the_plan_holds_E_and_S1_which_matches_C_0(self):
        n = 3
        state = canonical_state(13376, "11" * 32, "22" * 20, "a0" * 32, 0, timestamp=1000, fork_time=None,
                                override_window=W)
        h = self.head_for(state, account_nonce=n, number=10, timestamp=1000)
        c0 = self.keys[0].commitment
        e = Authorization(ACCOUNT, "ENROLL", n, c0, epoch=0)
        p = self.learned_pi(1, 1)
        self.tracker.record(SCOPE, e, b"E-of-branch-1", **IN_BLOCK)     # in a block: a's secp256k1 key is published
        wallet.learn_authorization(SCOPE, SEED, self.crypto, self.store, self.tracker, p, b"P-of-another-device")
        self.store.mark_compromised(SCOPE, 1, "W records epoch 1")
        payload = offer_for(self.tracker.observe_head(SCOPE, h), p)["payload"]
        self.assertEqual([(x["kind"], x.get("account_nonce"), x.get("migration_nonce"), x.get("key")) for x in
                          payload["plan"]["acts"]],
                         [("ENROLL", n, None, "NEW_KEY_SELECTED_AT_ITS_PLANNING_STATE"),
                          ("WRITE", None, 1, "SAME_KEY_AS_ITS_PLANNING_STATE")])
        plan = wallet.plan_payload(SCOPE, state, self.store, SEED, self.crypto, tracker=self.tracker, head=h,
                                   acts=[act("ENROLL"), act("WRITE_SAME_KEY", 2)], domain_tag=DOMAIN,
                                   verifier_version=VERSION, expiry=EXPIRY, max_account_fee=FEE)
        x0, x1 = plan.elements
        self.assertEqual((x0.kind, x0.account_nonce, x0.commitment, x0.epoch), ("ENROLL", n, c0, 0))
        self.assertEqual((x1.migration_nonce, x1.commitment, x1.epoch), (1, c0, 0))     # matches C_0 of S_1, epoch 0
        self.assertEqual(x1.planning_state, ("PQ_BY_ENROLL", 1, n + 1, False, c0.hex()))
        bundle = self.build(plan, state, h, proofs={1: b"MODEL-PROOF-OF-S1"},
                            carriers={0: b"E-of-branch-1", 1: b"sponsored-carrier-of-S1"})
        end = self.tracker.bundle_preview(SCOPE, bundle)["end_state"]
        self.assertEqual((end["mode"], end["migration_nonce"], end["commitment"]), ("PQ_BY_PROOF", 2, c0.hex()))
        payloads = []
        self.tracker.export_bundle(SCOPE, bundle, payloads.append)
        self.assertEqual(payloads, [(b"E-of-branch-1", b"sponsored-carrier-of-S1")])

    def test_v23_w3_a_payload_void_at_a_changed_head_is_prepared_again_from_there(self):
        state, h, s, p = self.v22w2()
        c1 = self.keys[1].commitment
        plan = wallet.plan_payload(SCOPE, state, self.store, SEED, self.crypto, tracker=self.tracker, head=h,
                                   acts=[act("WRITE_NEW_KEY"), act("WRITE_SAME_KEY", 2)], domain_tag=DOMAIN,
                                   verifier_version=VERSION, expiry=EXPIRY, max_account_fee=FEE, **own_kw())
        # B': a reorganization makes canonical a branch on which a write that A includes, S of branch 1, has raised
        # migration_nonce to 2.
        moved_state = canonical_state(13376, "11" * 32, "22" * 20, "f5" * 32, 2, status="PQ_BY_PROOF", commitment=c1,
                                      timestamp=2012, fork_time=900, override_window=W, enrolled_at=850)
        moved = AccountState(ACCOUNT, "f5" * 32, 32, 2012, 2, 7, "PQ_BY_PROOF", False, c1, 900, W, 850)
        self.tracker.observe_head(SCOPE, moved)
        replanned = wallet.replan_payload(plan, SCOPE, moved_state, self.store, SEED, self.crypto, tracker=self.tracker,
                                          head=moved)
        self.assertEqual(replanned.status, "VOID")
        self.assertEqual([v["changed"] for v in replanned.elements],
                         [["PI_MIGRATION_NONCE", "SELECTED_EPOCH"], ["PI_MIGRATION_NONCE"]])
        self.assertEqual([v["verdict"] for v in replanned.elements], ["CHANGED_NEW_PROOF_WITH_FRESH_COINS"] * 2)
        self.assertIsNone(replanned.plan)                    # the same acts at B': epoch 2, recorded
        self.assertIn("EPOCH_COMPROMISED", replanned.error)
        with self.assertRaisesRegex(ValueError, "STALE_PAYLOAD_PLAN"):      # never rebound to B' by relabelling
            self.build(plan, moved_state, moved, proofs={0: b"P0", 1: b"P1"}, carriers={1: b"S2"})
        # Prepared again from B' under 34.2 rule 1: P is at the head's migration_nonce in the re-commit gate.
        offer = offer_for(self.tracker.observe_head(SCOPE, moved), p)
        self.assertEqual(offer["action"], "OFFER_FINALIZING_ACTIVATION_OR_ADVANCE_PAST_PI_NONCE")

    def test_v23_w3_a_changed_account_nonce_voids_the_payload_and_an_unchanged_pi_keeps_its_proof(self):
        state, h, s, p = self.v22w1()                       # frozen, account nonce 7; S of branch 1 in a block
        plan = wallet.plan_payload(SCOPE, state, self.store, SEED, self.crypto, tracker=self.tracker, head=h,
                                   acts=[act("WRITE_NEW_KEY"), act("ACTIVATION")], domain_tag=DOMAIN,
                                   verifier_version=VERSION, expiry=EXPIRY, max_account_fee=FEE)
        # B': a branch on which a's account nonce is 8 (a transaction of a before T, l. 360).
        moved_state = canonical_state(13376, "11" * 32, "22" * 20, "f8" * 32, 0, timestamp=2000, fork_time=900,
                                      override_window=W)
        moved = self.head_for(moved_state, account_nonce=8, number=21)
        self.tracker.observe_head(SCOPE, moved)
        replanned = wallet.replan_payload(plan, SCOPE, moved_state, self.store, SEED, self.crypto, tracker=self.tracker,
                                          head=moved)
        self.assertEqual((replanned.status, [v["verdict"] for v in replanned.elements]),
                         ("VOID", ["UNCHANGED_KEEPS_ITS_PROOF", "CHANGED_SIGN_AGAIN"]))
        self.assertEqual(replanned.elements[1]["changed"], ["ACCOUNT_NONCE"])
        again = replanned.plan                                # the same acts prepared again at B'
        self.assertEqual((again.elements[0].pi, again.elements[1].account_nonce), (plan.elements[0].pi, 8))
        self.assertEqual(replanned.elements[0]["prepared_again"], "UNCHANGED_PI_KEEPS_ITS_PROOF")

    def test_v23_w4_after_a_split_and_a_reorganization_the_payload_is_re_planned_whole(self):
        state, h, s, p = self.v22w2()
        plan = wallet.plan_payload(SCOPE, state, self.store, SEED, self.crypto, tracker=self.tracker, head=h,
                                   acts=[act("WRITE_NEW_KEY"), act("WRITE_SAME_KEY", 2)], domain_tag=DOMAIN,
                                   verifier_version=VERSION, expiry=EXPIRY, max_account_fee=FEE, **own_kw())
        proofs, carriers = {0: b"MODEL-PROOF-OF-S", 1: b"MODEL-PROOF-OF-S2"}, {1: b"sponsored-carrier-of-S2"}
        bundle = self.build(plan, state, h, proofs=proofs, carriers=carriers)
        self.tracker.export_bundle(SCOPE, bundle, lambda payload: "relay")
        split, back, back_state = self.split_and_back(h)
        with self.assertRaisesRegex(ValueError, "PREPARED_AGAINST_A_LATER_PLANNING_STATE"):
            self.tracker.export(SCOPE, bundle.elements[1].authorization, b"sponsored-carrier-of-S2", self.sent.append,
                                head=back)
        replanned = wallet.replan_payload(plan, SCOPE, back_state, self.store, SEED, self.crypto, tracker=self.tracker,
                                          head=back)
        self.assertEqual((replanned.status, [v["verdict"] for v in replanned.elements]),
                         ("REBOUND", ["UNCHANGED_KEEPS_ITS_PROOF", "UNCHANGED_KEEPS_ITS_PROOF"]))
        again = self.build(replanned.plan, back_state, back, proofs=proofs, carriers=carriers)
        self.assertEqual([e.carrier for e in again.elements], [e.carrier for e in bundle.elements])
        payloads = []
        self.tracker.export_bundle(SCOPE, again, payloads.append)
        self.assertEqual((payloads, self.sent), ([tuple(e.carrier for e in bundle.elements)], []))

    def test_v23_w5_the_activating_carrier_ends_at_F_and_the_non_activating_one_stays_a_target(self):
        n, r_act, r_plain, f = self.v23w5()
        self.assertEqual(r_act.group_id, r_plain.group_id)                    # one authorization (a, n)
        self.assertEqual(list(self.tracker.observe_finalized(SCOPE, FinalizedView(f))),
                         [(r_act.group_id, r_act.variant_id, "FINAL_AND_ACTIVATED")])
        self.store.mark_compromised(SCOPE, 3, "the target key is then exposed")
        h = replace(f, block_hash="d8" * 32, number=41, timestamp=3012)
        notice = self.tracker.observe_head(SCOPE, h)
        self.assertEqual(notice["exposed_pending"], [(r_plain.group_id, r_plain.variant_id)])
        offer = offer_for(notice, r_plain)
        self.assertEqual((offer["action"], offer["first"]), ("OFFER_ACCOUNT_NONCE_CONSUMPTION", "ANY_TRANSACTION"))
        self.assertTrue(binding_conditions_allow(r_plain, h))       # A, which holds it, can include it at once
        f2 = replace(f, block_hash="d9" * 32, number=42, timestamp=3024, account_nonce=n + 1)
        self.assertEqual(list(self.tracker.observe_finalized(SCOPE, FinalizedView(f2, f.block_hash))),
                         [(r_plain.group_id, r_plain.variant_id, "ACCOUNT_NONCE_CONSUMED")])

    def test_v23_w5_the_index_ends_when_every_carrier_that_the_device_knows_has_ended(self):
        n, r_act, r_plain, f = self.v23w5()
        index = self.tracker.rotate_index(SCOPE, ACCOUNT, n)
        self.assertEqual((index["group"], index["known"], index["live"], index["ended"]), (r_act.group_id, 2, 2, False))
        self.assertEqual(sorted((c["activating"], c["key_exposed"]) for c in index["carriers"]),
                         [(False, False), (True, False)])
        ended = self.tracker.observe_finalized(SCOPE, FinalizedView(f))
        self.assertEqual(ended.indexes_ended, [])                     # R_plain is still tracked: (a, n) has not ended
        self.store.mark_compromised(SCOPE, 3, "the target key is then exposed")
        by = {c["activating"]: c for c in self.tracker.rotate_index(SCOPE, ACCOUNT, n)["carriers"]}
        self.assertEqual([(by[x]["ended"], by[x]["key_exposed"]) for x in (True, False)],
                         [("FINAL_AND_ACTIVATED", True), (None, True)])
        # Carriers learned later are tracked and judged on their own (35.3 rule 1).
        c_s, c5 = self.keys[0].commitment, self.keys[5].commitment
        for activating, raw in ((True, b"R_act2-learned-later"), (False, b"R_plain2-learned-later")):
            self.tracker.record(SCOPE, Authorization(ACCOUNT, "ROTATE", n, c5, activating=activating, signer_commitment=c_s,
                                                     epoch=5), raw, **IN_BLOCK)
        index = self.tracker.rotate_index(SCOPE, ACCOUNT, n)
        self.assertEqual((index["known"], index["live"], index["live_binding_an_exposed_key"], index["ended"]),
                         (4, 2, 1, False))
        f2 = replace(f, block_hash="d9" * 32, number=42, timestamp=3024, account_nonce=n + 1)
        ended = self.tracker.observe_finalized(SCOPE, FinalizedView(f2, f.block_hash))
        self.assertEqual(ended.indexes_ended, [{"group": r_act.group_id, "account_nonce": n, "carriers": 4}])
        self.assertTrue(self.tracker.rotate_index(SCOPE, ACCOUNT, n)["ended"])

    def test_v24_w1_x1_carries_migration_nonce_6_and_the_key_of_epoch_6(self):
        state, h, key = self.v24w1()
        plan = wallet.plan_payload(SCOPE, state, self.store, SEED, self.crypto, tracker=self.tracker, head=h,
                                   acts=[act("WRITE_SAME_KEY"), act("WRITE_NEW_KEY")], domain_tag=DOMAIN,
                                   verifier_version=VERSION, expiry=EXPIRY, max_account_fee=FEE, current_key=key)
        x0, x1 = plan.elements
        self.assertEqual((x0.role, x0.migration_nonce, x0.commitment, x0.epoch), ("SAME_KEY", 5, self.keys[4].commitment, 4))
        self.assertEqual((x1.role, x1.migration_nonce, x1.commitment, x1.epoch), ("NEW_KEY", 6, self.keys[6].commitment, 6))
        self.assertEqual(x1.planning_state, ("PQ_BY_PROOF", 6, 9, False, self.keys[4].commitment.hex()))
        bundle = self.build(plan, state, h, proofs={0: b"MODEL-PROOF-OF-X0", 1: b"MODEL-PROOF-OF-X1"}, **BALANCE)
        end = self.tracker.bundle_preview(SCOPE, bundle, **BALANCE)["end_state"]
        self.assertEqual((end["migration_nonce"], end["commitment"]), (7, self.keys[6].commitment.hex()))
        payloads = []
        self.tracker.export_bundle(SCOPE, bundle, payloads.append, **BALANCE)
        self.assertEqual(len(payloads), 1)
        # Without the step, the selection at B is epoch 5, which is recorded.
        with self.assertRaisesRegex(ValueError, "EPOCH_COMPROMISED"):
            wallet.plan_payload(SCOPE, state, self.store, SEED, self.crypto, tracker=self.tracker, head=h,
                                acts=[act("WRITE_NEW_KEY"), act("ACTIVATION")], domain_tag=DOMAIN,
                                verifier_version=VERSION, expiry=EXPIRY, max_account_fee=FEE, current_key=key)


# ------------------------------------------------------------------------------------------------
# Spec (commit 2a4fcd54) section 31.2 rule 10 (d) (the same-key step from PQ_BY_ENROLL for an own
# key, and as a rotate to the current key), (e) (the fee fields from the owner's choice under l. 417, the PI in the
# layout of the named version, and the sponsored acts of 34.2 rule 1 (f) built by the component), (f) (validate_plan
# checks every PI field), and section 37.3 (S-1 to S-6, S-8 to S-11) with vector V25-W-1.

STEP_OVERRIDE = "0x7E_SAME_KEY_EARLY_FINALISATION_THROUGH_THE_OVERRIDE_GATE"     # wallet_epochs.STEP_0x7E_OVERRIDE
STEP_RECOMMIT = "0x7E_RECOMMIT_THROUGH_THE_RECOMMIT_GATE"
STEP_ROTATE = "0x7C_ROTATE_TO_THE_CURRENT_KEY"
STEP_ACTIVATING_ROTATE = "ACTIVATING_0x7C_CARRYING_THE_ROTATE_TO_THE_CURRENT_KEY"
REGISTRY = "00" * 19 + "08"                       # the research client's PQ_REGISTRY address (a model value)
ROTATE_CONFIG = dict(ACTIVATION_CONFIG, registry=REGISTRY)
SPONSOR_ADDRESS = "88" * 20                       # a PQ account other than legacy_address (3.2.6)
SPONSOR_SEED = bytes([0x22]) * 32                 # public synthetic seed of the model sponsor's key


def fee_kw(**fields):
    """{"fee": FeeChoice(**fields)} where the side has the owner's fee choice; {} on a side that fixed mode 0."""
    return {"fee": wallet.FeeChoice(**fields)} if hasattr(wallet, "FeeChoice") else {}


def reference_protocol():
    """Independent canonical-wire oracle, shipped with these model tests."""
    import _test_reference_protocol
    return _test_reference_protocol


class SigningPolicyBase(PayloadPlanBase):
    def model_sponsor(self, valid_until=EXPIRY):
        """The carrier's sponsor of a sponsored single, signing with its own model key (never the owner's)."""
        pk = self.crypto("pk", SPONSOR_SEED)
        return wallet.Sponsor(SPONSOR_ADDRESS, valid_until, lambda message, ctx: self.crypto("sign", SPONSOR_SEED, message,
                                                                                             ctx), public_key=pk)

    def sponsor_kw(self, valid_until=EXPIRY):
        return {"sponsor": self.model_sponsor(valid_until)} if hasattr(wallet, "Sponsor") else {}

    def sponsor_signature_verifies(self, raw, option_index):
        """The sponsor's signature of a sponsored 0x7e (16.4: over 0x7e || RLP(tx with sponsor_sig empty), tag
        ETH-PQ-SPONSOR/v1; ModelCrypto's hash is SHA-256, the helper's is keccak256)."""
        tx = reference_protocol().rlp_decode(raw[1:])
        signature = tx[option_index][2]
        tx[option_index][2] = b""
        ctx = b"ETH-PQ-SPONSOR/v1"
        message = ctx + self.crypto("hash", b"\x7e" + wallet.wire.rlp(tx))
        return self.crypto.text("verify", self.crypto("pk", SPONSOR_SEED), message, ctx, signature) == "true"

    def own_enrollment(self):
        """B: the owner's own 0x7d (C_0) at migration_nonce 1, the override gate open (T unscheduled, l. 61), account
        nonce 8; epoch 1 recorded under 31.2 rule 7; the scan of B finds K_0."""
        c0 = self.keys[0].commitment
        state = canonical_state(13376, "11" * 32, "22" * 20, "d1" * 32, 1, status="PQ_BY_ENROLL", commitment=c0,
                                timestamp=2000, fork_time=None, override_window=W, enrolled_at=950)
        h = AccountState(ACCOUNT, "d1" * 32, 31, 2000, 1, 8, "PQ_BY_ENROLL", False, c0, None, W, 950)
        self.tracker.observe_head(SCOPE, h)
        self.store.mark_compromised(SCOPE, 1, "epoch 1 recorded (31.2 rule 7)")
        return state, h, scan_current_key(SCOPE, state, lambda e: self.keys[e].commitment).current_key

    def proof_account(self, *, activated, block="d2"):
        """B: PQ_BY_PROOF at migration_nonce 2 with the current key C_1, account nonce 8; epoch 2 recorded."""
        c1 = self.keys[1].commitment
        state = canonical_state(13376, "11" * 32, "22" * 20, block * 32, 2, status="PQ_BY_PROOF", activated=activated,
                                commitment=c1)
        h = AccountState(ACCOUNT, block * 32, 31, 2000, 2, 8, "PQ_BY_PROOF", activated, c1, None, W, 0)
        self.tracker.observe_head(SCOPE, h)
        self.store.mark_compromised(SCOPE, 2, "epoch 2 recorded (31.2 rule 7)")
        return state, h, scan_current_key(SCOPE, state, lambda e: self.keys[e].commitment).current_key

    def v25w1(self, fork_time=9_000_000, n=5):
        """V25-W-1 after the reorganization: F = the head, LEGACY with nonce n, migration_nonce 0, before T (T scheduled
        unless fork_time is None). E, W's 0x7d at n (C_0), and R, W's activating 0x7c at n + 1 signed by K_0 that calls
        rotate to K_1, were included on branch 1 (A holds both); K_1 is exposed and W records epoch 1."""
        h = frozen_head(fork_time=fork_time, timestamp=1000, account_nonce=n)
        e = Authorization(ACCOUNT, "ENROLL", n, self.keys[0].commitment, epoch=0)
        r = self.rotate(n + 1, 0, 1, activating=True)
        self.tracker.record(SCOPE, e, b"E-of-branch-1", **IN_BLOCK)
        self.tracker.record(SCOPE, r, b"R-of-branch-1", **IN_BLOCK)
        self.store.mark_compromised(SCOPE, 1, "K_1 exposed; W records epoch 1")
        self.tracker.observe_head(SCOPE, h)
        return h, e, r

    def edited(self, plan, a, b, value):
        """The plan with PI bytes [a, b) replaced and its checksum recomputed: only a field check can catch it."""
        pi = plan.pi[:a] + value + plan.pi[b:]
        return replace(plan, pi=pi, pi_sha256=hashlib.sha256(pi).hexdigest())


class SigningPolicyRegressionTests(SigningPolicyBase):
    """Section 31.2 rule 10 (d)-(f) and section 37.3."""

    # ---- 31.2 rule 10 (d)
    def test_r6_d_the_same_key_step_goes_through_the_override_gate_of_the_owners_own_enrollment(self):
        state, h, key = self.own_enrollment()
        selected = wallet_epochs.select_new_key_epoch(SCOPE, state, self.store, current_key=key)
        # BLOCKED, since its same-key offer needed the re-commit gate (rule 10 (d), l. 327).
        self.assertEqual((selected.status, selected.epoch, getattr(selected, "steps", None)),
                         ("OFFER_SAME_KEY_RECOMMIT", 0, (STEP_OVERRIDE,)))
        step = wallet.prepare_recommit(SCOPE, state, self.store, key, SEED, self.crypto, tracker=self.tracker,
                                       domain_tag=DOMAIN, verifier_version=VERSION, expiry=EXPIRY, max_account_fee=FEE,
                                       confirm_extra_proof_and_fee=True)
        self.assertEqual((step.same_key_recommit, step.pi[93:125], int.from_bytes(step.pi[84:92], "big"), step.pi[169]),
                         (True, self.keys[0].commitment, 1, 0))     # own ETH: the enrolled key is the owner's (l. 417)
        wallet.export_recovery(step, SCOPE, state, self.store, self.tracker, **self.export_kwargs(step, h))
        self.assertEqual(len(self.sent), 1)
        self.assertEqual(Authorization.from_pi(ACCOUNT, step.pi).nonce, 1)

    def test_r6_d_an_activated_binding_final_account_takes_a_rotate_to_the_current_key(self):
        state, h, key = self.proof_account(activated=True)
        selected = wallet_epochs.select_new_key_epoch(SCOPE, state, self.store, current_key=key)
        self.assertEqual((selected.status, getattr(selected, "steps", None)),
                         ("OFFER_SAME_KEY_ROTATE", (STEP_ROTATE,)))           # BLOCKED
        step = wallet.prepare_same_key_rotate(SCOPE, state, self.store, key, SEED, self.crypto, ROTATE_CONFIG,
                                              tracker=self.tracker, head=h, confirm_extra_transaction_and_fee=True)
        tx = reference_protocol().rlp_decode(step.raw[1:])
        c1, pk1 = self.keys[1].commitment, self.keys[1].public_key
        self.assertEqual((step.raw[0], len(tx), tx[2], tx[6].hex(), tx[7], tx[8][:4].hex(), tx[11]),
                         (0x7C, 13, (8).to_bytes(1, "big"), REGISTRY, b"", "262f8ae0", []))
        # The calldata carries pk_1 and a proof of possession by K_1 over the 0x7c's nonce (24.2 rules 2 and 7).
        self.assertEqual((tx[8][35], tx[8][132:132 + 1312]), (1, pk1))
        pop = tx[8][132 + 1312 + 32:]
        pop_message = b"ETH-PQ-ROTATE-POP/v1" + self.crypto("hash", b"PQ-ROTATE" + (13376).to_bytes(32, "big")
                                                           + bytes.fromhex(ACCOUNT.address) + (8).to_bytes(8, "big")
                                                           + b"\x01" + pk1)
        self.assertEqual(self.crypto.text("verify", pk1, pop_message, b"ETH-PQ-ROTATE-POP/v1", pop[:32]), "true")
        a = step.authorization
        self.assertEqual((a.kind, a.nonce, a.commitment, a.signer_commitment, a.activating, a.epoch),
                         ("ROTATE", 8, c1, c1, False, 1))
        wallet.export_same_key_rotate(step, SCOPE, state, self.store, key, SEED, self.crypto, tracker=self.tracker,
                                      head=h, deliver=self.sent.append)
        self.assertEqual(self.sent, [step.raw])
        self.assertIn(a.variant_id, self.tracker.records(SCOPE)[a.group_id])

    def test_r6_d_an_unactivated_account_takes_an_activating_0x7c_that_carries_the_rotate(self):
        state, h, key = self.proof_account(activated=False, block="d3")
        selected = wallet_epochs.select_new_key_epoch(SCOPE, state, self.store, current_key=key)
        # The re-commit gate admits both forms of 31.2 rule 8 (a).
        self.assertEqual(getattr(selected, "steps", None), (STEP_RECOMMIT, STEP_ACTIVATING_ROTATE))
        step = wallet.prepare_same_key_rotate(SCOPE, state, self.store, key, SEED, self.crypto, ROTATE_CONFIG,
                                              tracker=self.tracker, head=h, confirm_extra_transaction_and_fee=True)
        tx = reference_protocol().rlp_decode(step.raw[1:])
        self.assertEqual((tx[11], step.authorization.activating, step.form),
                         ([self.keys[1].public_key], True, STEP_ACTIVATING_ROTATE))
        # A binding-final PQ_BY_ENROLL account that is not activated: the same activating rotate (BLOCKED).
        self.fresh_wallet("binding-final-enrollment")
        c0 = self.keys[0].commitment
        enrolled = canonical_state(13376, "11" * 32, "22" * 20, "d4" * 32, 1, status="PQ_BY_ENROLL", commitment=c0,
                                   timestamp=900 + W, fork_time=900, override_window=W, enrolled_at=850)
        self.store.mark_compromised(SCOPE, 1, "epoch 1 recorded")
        key0 = scan_current_key(SCOPE, enrolled, lambda e: self.keys[e].commitment).current_key
        selected = wallet_epochs.select_new_key_epoch(SCOPE, enrolled, self.store, current_key=key0)
        self.assertEqual((selected.status, getattr(selected, "steps", None)),
                         ("OFFER_SAME_KEY_ROTATE", (STEP_ACTIVATING_ROTATE,)))

    # ---- 31.2 rule 10 (e)
    def test_r6_e_the_pi_takes_the_fee_fields_of_the_owners_choice(self):
        state = self.frozen_state()
        self.tracker.observe_head(SCOPE, self.head_for(state, account_nonce=7))
        named = self.plan(state, **fee_kw(fee_mode=1, fee_sponsor=SPONSOR_ADDRESS, fee_auth_until=4500))
        self.assertEqual((named.pi[169], named.pi[170:190].hex(), int.from_bytes(named.pi[190:198], "big")),
                         (1, SPONSOR_ADDRESS, 4500))
        zero = self.plan(state, **fee_kw(fee_mode=2))
        self.assertEqual((zero.pi[169], zero.pi[170:198]), (2, bytes(28)))
        self.assertEqual(zero.pi[:169], named.pi[:169])

    def test_r6_e_the_pi_follows_the_layout_of_the_named_version(self):
        state = self.frozen_state()
        self.tracker.observe_head(SCOPE, self.head_for(state, account_nonce=7))
        consent = (wallet.fee_consent(layout=1, max_account_fee=FEE, verifier_version=VERSION)["token"]
                   if hasattr(wallet, "fee_consent") else None)
        plan = self.plan(state, **fee_kw(layout=1, sponsored=False, consent=consent))
        self.assertEqual(len(plan.pi), 169)                     # 198, whatever the version's layout
        ref = reference_protocol()
        tx = ref.rlp_decode(wallet.wire.rlp([13376, bytes.fromhex(ACCOUNT.address), 0, 1, plan.key.commitment, EXPIRY,
                                             FEE, 2, 3, 6000000, [], VERSION, [], b""]))
        expected = ref.public_inputs(0x7E, tx, 1)[0]            # the reference computes the chain's real DOMAIN_TAG
        self.assertEqual(plan.pi[:32] + plan.pi[64:], expected[:32] + expected[64:])
        with self.assertRaisesRegex(ValueError, "LAYOUT_1_BOUNTY_NEEDS_THE_OWNERS_CONSENT"):
            self.plan(state, **fee_kw(layout=1, sponsored=False))

    def test_r6_e_mode_3_and_the_named_sponsor_follow_l_417(self):
        state = self.frozen_state()
        self.tracker.observe_head(SCOPE, self.head_for(state, account_nonce=7))
        for fields, refusal in (({"fee_mode": 3, "fee_auth_until": 4500}, "FEE_MODE_3_NEEDS_THE_OWNERS_DISPLAYED_CONSENT"),
                                ({"fee_mode": 1, "fee_sponsor": ACCOUNT.address, "fee_auth_until": 10},
                                 "FEE_SPONSOR_IS_LEGACY_ADDRESS"),
                                ({"fee_mode": 1, "fee_sponsor": SPONSOR_ADDRESS, "fee_auth_until": EXPIRY + 1},
                                 "fee_auth_until <= expiry")):
            with self.subTest(refusal=refusal), self.assertRaisesRegex(ValueError, refusal):   # a mode-0 PI
                self.plan(state, **fee_kw(**fields))
        consent = getattr(wallet, "fee_consent", None)
        self.assertIsNotNone(consent, "no displayed consent of mode 3 exists")
        token = consent(layout=2, max_account_fee=FEE, verifier_version=VERSION, fee_auth_until=4500)
        self.assertIn("never a wallet default", token["statement"])
        self.assertEqual(self.plan(state, fee=wallet.FeeChoice(fee_mode=3, fee_auth_until=4500,
                                                                consent=token["token"])).pi[169], 3)
        # The consent names the cap and fee_auth_until: a token shown for another cap or date consents to neither.
        for other in (consent(layout=2, max_account_fee=FEE + 1, verifier_version=VERSION, fee_auth_until=4500),
                      consent(layout=2, max_account_fee=FEE, verifier_version=VERSION, fee_auth_until=4499)):
            with self.assertRaisesRegex(ValueError, "FEE_MODE_3_NEEDS_THE_OWNERS_DISPLAYED_CONSENT"):
                self.plan(state, fee=wallet.FeeChoice(fee_mode=3, fee_auth_until=4500, consent=other["token"]))

    def test_r6_e_without_a_choice_no_own_funds_in_the_override_of_another_partys_enrollment(self):
        c_ext, f, state, h = self.stealth()
        self.tracker.observe_head(SCOPE, h)
        with self.assertRaisesRegex(ValueError, "FEE_CHOICE_REQUIRED"):        # a mode-0 override
            self.plan(state)
        own = self.plan(state, **own_funds())
        self.assertIn("OWN_FUNDS_WHERE_ANOTHER_PARTY_CAN_SEND_FROM_A", " ".join(own.warnings))
        self.assertEqual(self.plan(state, **fee_kw(fee_mode=2)).warnings, ())

    def test_r6_e_export_builds_the_sponsored_0x7e_with_the_sponsors_signature(self):
        state = self.frozen_state()
        h = self.head_for(state, account_nonce=7)
        self.tracker.observe_head(SCOPE, h)
        plan = self.plan(state, **fee_kw(fee_mode=2))
        wallet.export_recovery(plan, SCOPE, state, self.store, self.tracker, **self.export_kwargs(plan, h),
                               **self.sponsor_kw(4000))
        tx = reference_protocol().rlp_decode(self.sent[0][1:])
        self.assertEqual((len(tx), tx[7], tx[13][:2]), (17, b"\x02", [bytes.fromhex(SPONSOR_ADDRESS), (4000).to_bytes(2, "big")]))
        self.assertTrue(self.sponsor_signature_verifies(self.sent[0], 13))
        ref = reference_protocol()
        self.assertEqual(ref.decode(self.sent[0], {VERSION: ref.Version(2, 0, 10**12)})[2], 2)
        with self.assertRaisesRegex(ValueError, "SPONSOR_REQUIRED"):
            wallet.export_recovery(plan, SCOPE, state, self.store, self.tracker, **self.export_kwargs(plan, h))
        with self.assertRaisesRegex(ValueError, "sponsor_valid_until <= expiry"):
            wallet.export_recovery(plan, SCOPE, state, self.store, self.tracker, **self.export_kwargs(plan, h),
                                   sponsor=self.model_sponsor(EXPIRY + 1))
        with self.assertRaisesRegex(ValueError, "never legacy_address"):
            wallet.export_recovery(plan, SCOPE, state, self.store, self.tracker, **self.export_kwargs(plan, h),
                                   sponsor=replace(self.model_sponsor(), address=ACCOUNT.address))
        forged = replace(self.model_sponsor(), sign=lambda message, ctx: self.crypto("sign", bytes(32), message, ctx))
        with self.assertRaisesRegex(ValueError, "SPONSOR_SIGNATURE_INVALID"):
            wallet.export_recovery(plan, SCOPE, state, self.store, self.tracker, **self.export_kwargs(plan, h),
                                   sponsor=forged)
        self.assertEqual(len(self.sent), 1)

    def test_r6_e_check_7_refuses_an_unsponsored_carrier_whose_fee_fields_pass_the_cap(self):
        state = self.frozen_state()
        h = self.head_for(state, account_nonce=7)
        self.tracker.observe_head(SCOPE, h)
        plan = self.plan(state)
        dear = dict(CONFIG, max_fee_per_gas=4)                  # 6,000,000 x 4 > 20,000,000 (FEE)
        with self.assertRaisesRegex(ValueError, "FEE_CAP_EXCEEDED"):            # delivered
            wallet.export_recovery(plan, SCOPE, state, self.store, self.tracker,
                                   **{**self.export_kwargs(plan, h), "config": dear})
        self.assertEqual((self.sent, self.tracker.records(SCOPE)), ([], {}))

    def test_r6_e_the_adapter_builds_the_sponsored_act_after_an_override(self):
        state, h, s, p = self.v22w2()                 # V22-W-2 (iii) / V23-W-1: S, then the sponsored re-commit S_2
        plan = wallet.plan_payload(SCOPE, state, self.store, SEED, self.crypto, tracker=self.tracker, head=h,
                                   acts=[act("WRITE_NEW_KEY"), act("WRITE_SAME_KEY", 2)], domain_tag=DOMAIN,
                                   verifier_version=VERSION, expiry=EXPIRY, max_account_fee=FEE, **own_kw())
        try:
            bundle = self.build(plan, state, h, proofs={0: b"MODEL-PROOF-OF-S", 1: b"MODEL-PROOF-OF-S2"},
                                **self.sponsor_kw())
            built = bundle.elements[1].carrier
        except ValueError as exc:
            built = str(exc).split(":")[0]                    # SPONSORED_CARRIER_REQUIRED (the caller's)
        self.assertIsInstance(built, bytes)
        tx = reference_protocol().rlp_decode(built[1:])
        self.assertEqual((len(tx), tx[2], tx[4], tx[7], tx[13][0].hex()),
                         (17, b"\x02", self.keys[1].commitment, b"\x02", SPONSOR_ADDRESS))
        self.assertTrue(self.sponsor_signature_verifies(built, 13))
        payloads = []
        self.tracker.export_bundle(SCOPE, bundle, payloads.append)
        self.assertEqual(payloads, [tuple(e.carrier for e in bundle.elements)])

    def test_r6_e_a_layout_1_pi_is_tracked_and_its_carrier_class_decides_who_pays(self):
        state, h, s, p = self.v22w2()
        pi = sponsored(self.pi_of(2, 1)).pi[:169]                # the same re-commit under a layout-1 version
        try:
            recommit = Authorization.from_pi(ACCOUNT, pi, epoch=1)
        except ValueError:
            recommit = None                                   # a complete layout-2 PI was required
        self.assertIsNotNone(recommit)
        s_el = self.write(s, b"S-override-of-branch-1")
        unstated = at.PayloadElement("WRITE", b"layout-1-recommit", authorization=recommit)
        # A layout-1 PI names no fee mode: a carrier not stated to be sponsored counts as paid by a, which the enrolled
        # key's transaction can pre-empt (34.2 rule 1 (f)); the adapter states the sponsored carrier it builds.
        with self.assertRaisesRegex(ValueError, "BUNDLE_ACT_PREEMPTIBLE"):
            self.tracker.bundle_preview(SCOPE, at.OnePayloadBundle(h, (s_el, unstated)))
        stated = at.PayloadElement("WRITE", b"layout-1-recommit", authorization=recommit, sponsored=True)
        self.tracker.bundle_preview(SCOPE, at.OnePayloadBundle(h, (s_el, stated)))
        self.assertEqual((recommit.layout, recommit.fee_mode), (1, None))

    # ---- 31.2 rule 10 (f)
    def test_r6_f_validate_plan_checks_every_pi_field_against_the_owners_choice(self):
        state = self.frozen_state()
        self.tracker.observe_head(SCOPE, self.head_for(state, account_nonce=7))
        plan = self.plan(state)
        for field, a, b, value in (("expiry", 129, 137, (EXPIRY + 1).to_bytes(8, "big")),
                                   ("max_account_fee", 137, 169, (FEE + 1).to_bytes(32, "big")),
                                   ("DOMAIN_TAG", 32, 64, bytes(32)),
                                   ("verifier_version", 125, 129, (VERSION + 1).to_bytes(4, "big"))):
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, field):   # accepted
                wallet.validate_plan(self.edited(plan, a, b, value), SCOPE, state, self.store, self.tracker)

    def test_r6_f_an_edited_expiry_never_leaves_through_export(self):
        state = self.frozen_state()
        h = self.head_for(state, account_nonce=7)
        self.tracker.observe_head(SCOPE, h)
        plan = self.edited(self.plan(state), 129, 137, (EXPIRY + 99).to_bytes(8, "big"))
        with self.assertRaisesRegex(ValueError, "expiry differs"):                     # delivered
            wallet.export_recovery(plan, SCOPE, state, self.store, self.tracker, **self.export_kwargs(plan, h))
        self.assertEqual((self.sent, self.tracker.records(SCOPE)), ([], {}))

    def test_r6_f_the_plans_key_is_derived_again_before_export(self):
        state = self.frozen_state()
        h = self.head_for(state, account_nonce=7)
        self.tracker.observe_head(SCOPE, h)
        plan = self.plan(state)
        other = replace(self.keys[3], epoch=0)                   # C_3 presented as the key of epoch 0
        swapped = self.edited(replace(plan, key=other), 93, 125, other.commitment)
        with self.assertRaisesRegex(ValueError, "pq_pk_commit is not the key of the plan's epoch"):   # sent
            wallet.export_recovery(swapped, SCOPE, state, self.store, self.tracker, **self.export_kwargs(swapped, h))
        self.assertEqual(self.sent, [])

    def test_r6_f_the_callers_record_of_the_owners_choice_is_compared(self):
        state = self.frozen_state()
        self.tracker.observe_head(SCOPE, self.head_for(state, account_nonce=7))
        plan = self.plan(state)
        choice_type = getattr(wallet, "PlanChoice", None)
        if choice_type is None:
            self.fail("a plan names no owner's choice for validate_plan to compare")
        owners = choice_type(DOMAIN, VERSION, EXPIRY, FEE, wallet.FeeChoice(fee_mode=2))
        with self.assertRaisesRegex(ValueError, "RECOVERY_PLAN_CHOICE_MISMATCH"):
            wallet.validate_plan(plan, SCOPE, state, self.store, self.tracker, choice=owners)
        self.assertTrue(wallet.validate_plan(plan, SCOPE, state, self.store, self.tracker, choice=plan.choice))

    def test_r6_f_a_pi_that_expires_before_the_next_block_is_not_prepared(self):
        state = self.frozen_state()                              # header.timestamp 2000; the next block at 2012 or later
        self.tracker.observe_head(SCOPE, self.head_for(state, account_nonce=7))
        with self.assertRaisesRegex(ValueError, "PLANNED_WRITE_EXPIRES_BEFORE_ITS_BLOCK"):   # prepared
            wallet.prepare_recovery(SCOPE, state, self.store, SEED, self.crypto, tracker=self.tracker,
                                    domain_tag=DOMAIN, verifier_version=VERSION, expiry=2011, max_account_fee=FEE)

    # ---- 37.3 rule 4 and vector V25-W-1
    def test_r6_v25w1_the_owners_ecdsa_transactions_are_no_act_where_the_0x7d_that_A_holds_makes_them_fail(self):
        h, e, r = self.v25w1()
        offer = offer_for(self.tracker.observe_head(SCOPE, h), r)
        payload = offer["payload"]
        # TRANSACTION_OF_THE_LEGACY_ACCOUNT_AT_ITS_NONCE (ECDSA at n and n + 1), which E placed before them
        # makes fail, after which R binds from deadline(a).
        self.assertEqual((offer["action"], payload["first"]), (BUNDLE_LABEL, "ENROLLMENT_0x7D_AT_ACCOUNT_NONCE"))
        self.assertEqual([(x["kind"], x.get("account_nonce"), x.get("reveals")) for x in payload["plan"]["acts"]],
                         [("ENROLL", 5, None), ("ACTIVATION", 6, self.keys[0].commitment.hex())])
        self.assertEqual((payload["precursor_carriers"], payload["through_account_nonce"]),
                         ([[e.group_id, e.variant_id]], 6))
        run = payload["rejected_act"]["run"]               # E, which A holds, placed before the ECDSA transactions
        self.assertTrue(run[1].startswith("TRACKED_ENROLL_") and run[2].startswith("PAYLOAD"), run)
        self.assertNotIn("meets_rule_1_a", offer)

    def test_r6_v25w1_E_alone_never_leaves_without_its_act(self):
        h, e, r = self.v25w1()
        with self.assertRaises(ValueError) as caught:
            self.tracker.export(SCOPE, e, b"E-of-branch-1", self.sent.append, head=h)
        # TRANSACTION_AT_THE_ACCOUNT_NONCE_FIRST with a token that sends E alone once the owner confirms.
        self.assertEqual((caught.exception.remedy, caught.exception.token), ("ONE_PAYLOAD_BUNDLE", None))
        self.assertEqual(caught.exception.payload["first"], "ENROLLMENT_0x7D_AT_ACCOUNT_NONCE")
        self.assertEqual(self.sent, [])

    # ---- 37.3 rule 7 (S-11)
    def test_r6_s11_no_payload_is_offered_with_an_act_that_is_not_valid_in_its_planning_state(self):
        n, k0 = 5, self.keys[0].commitment
        h = head(block_hash="c5" * 32, number=30, timestamp=3000, account_nonce=n, commitment=k0, fork_time=None)
        r = self.rotate(n + 1, 0, 1, activating=False)
        self.tracker.record(SCOPE, r, b"R-at-n+1", **IN_BLOCK)
        self.store.mark_compromised(SCOPE, 1, "W records epoch 1")
        self.tracker.observe_head(SCOPE, h)
        epochs = set(self.store.security(SCOPE).compromised_epochs)
        with at._locked(self.tracker.lock_path):
            s = self.tracker._scope(self.tracker._read(), SCOPE)
        model = at._Model(self.tracker, s, epochs, h)
        key = next(iter(model.targets))
        Step = at.Step if hasattr(at, "Step") else __import__("reachability").Step
        act = Step("ACTIVATION", n, k0, label="OWN_ACTIVATION")
        stray = Step("ORDINARY", n + 7, k0, label="A_TRANSACTION_AT_A_NONCE_THAT_ITS_PLANNING_STATE_DOES_NOT_HAVE")
        follow = Step("ORDINARY", n + 1, k0, label="OWN_TRANSACTION")
        self.assertTrue(model.admissible([act, follow], [key]))
        # The stray element is popped in the run, which still ends R.
        self.assertFalse(model.admissible([act, stray, follow], [key]))


class SigningPolicyCoverageTests(SigningPolicyBase):
    """Behaviours that the text keeps."""

    def test_cov6_without_a_choice_the_frozen_recovery_keeps_round_5s_bytes(self):
        state = self.frozen_state()
        self.tracker.observe_head(SCOPE, self.head_for(state, account_nonce=7))
        plan = self.plan(state)
        expected = (ACCOUNT.chain_id.to_bytes(32, "big") + DOMAIN + bytes.fromhex(ACCOUNT.address) + bytes(8) + b"\x01"
                    + self.keys[0].commitment + VERSION.to_bytes(4, "big") + EXPIRY.to_bytes(8, "big")
                    + FEE.to_bytes(32, "big") + bytes(29))
        self.assertEqual(plan.pi, expected)

    def test_cov6_v25w1_contrast_while_T_is_unscheduled_E_alone_meets_rule_1_a(self):
        h, e, r = self.v25w1(fork_time=None)
        offer = offer_for(self.tracker.observe_head(SCOPE, h), r)
        # R's frame reverts in every reachable state (no finite deadline(a), l. 61): the owner's ECDSA transactions stay
        # an act that nothing placed before them makes fail, and E alone leaves.
        self.assertEqual(offer["payload"]["first"], "TRANSACTION_OF_THE_LEGACY_ACCOUNT_AT_ITS_NONCE")
        self.tracker.export(SCOPE, e, b"E-of-branch-1", self.sent.append, head=h)
        self.assertEqual(self.sent, [b"E-of-branch-1"])

    def test_cov6_the_owners_act_never_activates_an_enrolled_key_known_exposed(self):
        h, e, r = self.v25w1()
        self.store.mark_compromised(SCOPE, 0, "K_0 exposed as well")
        offer = offer_for(self.tracker.observe_head(SCOPE, h), r)
        # 31.2 rule 7 (b): the wallet does not on its own activate a recorded key, so E with the activation of K_0 is no
        # act here; the offer keeps a transaction of the LEGACY account (with its statement that every act
        # can be pre-empted, 34.2 rule 1 (b)).
        acts = (offer.get("payload") or {}).get("plan", {}).get("acts", [])
        self.assertNotIn(("ACTIVATION", self.keys[0].commitment.hex()), [(x["kind"], x.get("reveals")) for x in acts])
        self.assertEqual(offer["payload"]["first"], "TRANSACTION_OF_THE_LEGACY_ACCOUNT_AT_ITS_NONCE")

    def test_cov6_a_sponsored_carrier_from_a_sponsor_service_is_still_accepted(self):
        state, h, s, p = self.v22w2()
        plan = wallet.plan_payload(SCOPE, state, self.store, SEED, self.crypto, tracker=self.tracker, head=h,
                                   acts=[act("WRITE_NEW_KEY"), act("WRITE_SAME_KEY", 2)], domain_tag=DOMAIN,
                                   verifier_version=VERSION, expiry=EXPIRY, max_account_fee=FEE, **own_kw())
        bundle = self.build(plan, state, h, proofs={0: b"P0", 1: b"P1"}, carriers={1: b"carrier-of-a-sponsor-service"})
        self.assertEqual(bundle.elements[1].carrier, b"carrier-of-a-sponsor-service")

    def test_cov6_the_recommit_gate_keeps_its_0x7e_same_key_step(self):
        state, h, key = self.proof_account(activated=False, block="d5")
        step = wallet.prepare_recommit(SCOPE, state, self.store, key, SEED, self.crypto, tracker=self.tracker,
                                       domain_tag=DOMAIN, verifier_version=VERSION, expiry=EXPIRY, max_account_fee=FEE,
                                       confirm_extra_proof_and_fee=True)
        self.assertEqual((step.same_key_recommit, step.pi[93:125], int.from_bytes(step.pi[84:92], "big")),
                         (True, self.keys[1].commitment, 2))


class SigningPolicyVectorTests(SigningPolicyBase):
    """V25-W-1, and V22-W-2, V22-W-7, V23-W-1, V23-W-2 with sponsored carriers that the component builds; V23-W-3 as
    corrected (wallet parts; model proofs, model consensus)."""

    def test_v6_v25w1_i_E_then_R_reverts_before_deadline_and_binds_from_it(self):
        reach = __import__("reachability")
        T_, n = 9_000_000, 5
        cfg = reach.Config(T_, W)
        f = reach.St("LEGACY", 0, n, False, None, 0)
        e = reach.Step("ENROLL", n, self.keys[0].commitment)
        r = reach.Step("ROTATE", n + 1, self.keys[1].commitment, signer=self.keys[0].commitment, activating=True)
        after_e = reach.apply(e, f, 1012, cfg)                # Enrolled(a, 0x01, C_0, header.timestamp) before T
        self.assertEqual((after_e.mode, after_e.mn, after_e.an, after_e.commitment), ("PQ_BY_ENROLL", 1, n + 1,
                                                                                     self.keys[0].commitment))
        before = reach.apply(r, after_e, T_ + W - 1, cfg)     # Activated; the rotate frame reverts (NOT_FINAL)
        self.assertEqual((before.activated, before.mn, before.commitment), (True, 1, self.keys[0].commitment))
        self.assertFalse(reach.binds(r, after_e, T_ + W - 1, cfg))
        at_deadline = reach.apply(r, after_e, T_ + W, cfg)    # Rotated(a, 0x01, C_1); migration_nonce 2
        self.assertEqual((at_deadline.mn, at_deadline.commitment), (2, self.keys[1].commitment))
        self.assertTrue(reach.binds(r, after_e, T_ + W, cfg))

    def test_v6_v25w1_ii_W_sends_E_with_the_activation_of_K_0_and_ends_R_only_past_n_plus_1(self):
        h, e, r = self.v25w1()
        state = canonical_state(13376, "11" * 32, "22" * 20, h.block_hash, 0, timestamp=1000, fork_time=9_000_000,
                                override_window=W)
        offer = offer_for(self.tracker.observe_head(SCOPE, h), r)
        plan = wallet.plan_payload(SCOPE, state, self.store, SEED, self.crypto, tracker=self.tracker, head=h,
                                   acts=wallet.acts_from_offer(offer), domain_tag=DOMAIN, verifier_version=VERSION,
                                   expiry=EXPIRY, max_account_fee=FEE)
        self.assertEqual([(x.kind, x.account_nonce, x.epoch) for x in plan.elements], [("ENROLL", 5, 0), ("ACTIVATION", 6, 0)])
        bundle = self.build(plan, state, h, proofs={}, carriers={0: b"E-of-branch-1"})
        self.assertEqual(bundle.elements[1].carrier, self.signed(0, 6, True))   # W's activation of K_0 at n + 1, no rotate
        payloads = []
        self.tracker.export_bundle(SCOPE, bundle, payloads.append)
        self.assertEqual(payloads, [(b"E-of-branch-1", bundle.elements[1].carrier)])
        f1 = AccountState(ACCOUNT, "e5" * 32, 40, 1100, 1, 6, "PQ_BY_ENROLL", False, self.keys[0].commitment,
                          9_000_000, W, 1012)
        self.assertNotIn(r.variant_id, [v for _, v, _ in self.tracker.observe_finalized(SCOPE, FinalizedView(f1))])
        f2 = replace(f1, block_hash="e6" * 32, number=41, timestamp=1112, account_nonce=7, activated=True)
        self.assertIn((r.group_id, r.variant_id, "ACCOUNT_NONCE_CONSUMED"),
                      list(self.tracker.observe_finalized(SCOPE, FinalizedView(f2, f1.block_hash))))

    def test_v6_v22w2_iii_the_offer_maps_to_S_and_a_sponsored_recommit_that_the_adapter_builds(self):
        state, h, s, p = self.v22w2()
        offer = offer_for(self.tracker.observe_head(SCOPE, h), p)
        acts = wallet.acts_from_offer(offer, sponsored=wallet.FeeChoice(fee_mode=2))
        self.assertEqual([(x.kind, x.fee_mode) for x in acts], [("WRITE_NEW_KEY", 0), ("WRITE_SAME_KEY", 2)])
        plan = wallet.plan_payload(SCOPE, state, self.store, SEED, self.crypto, tracker=self.tracker, head=h, acts=acts,
                                   domain_tag=DOMAIN, verifier_version=VERSION, expiry=EXPIRY, max_account_fee=FEE,
                                   **own_kw())
        self.assertEqual(plan.elements[0].pi, s.pi)              # S itself: W's override of branch 1, unchanged
        bundle = self.build(plan, state, h, proofs={0: b"MODEL-PROOF-OF-S", 1: b"MODEL-PROOF-OF-S2"}, sponsor=self.model_sponsor())
        ref = reference_protocol()
        kinds = [ref.decode(e.carrier, {VERSION: ref.Version(2, 0, 10**12)})[1] for e in bundle.elements]
        self.assertEqual([(len(t), t[13] != []) for t in kinds], [(17, False), (17, True)])
        self.assertTrue(self.sponsor_signature_verifies(bundle.elements[1].carrier, 13))
        with self.assertRaisesRegex(ValueError, "BUNDLE_ACT_PREEMPTIBLE"):     # the activation is not the act here
            self.tracker.bundle_preview(SCOPE, at.OnePayloadBundle(h, (bundle.elements[0], self.activation_element(1, 7))))
        payloads = []
        self.tracker.export_bundle(SCOPE, bundle, payloads.append)
        self.assertEqual(len(payloads), 1)

    def test_v6_v23w1_the_sponsored_recommit_matches_C_1_of_S_1_and_both_apply_in_one_block(self):
        state, h, s, p = self.v22w2()
        c1 = self.keys[1].commitment
        plan = wallet.plan_payload(SCOPE, state, self.store, SEED, self.crypto, tracker=self.tracker, head=h,
                                   acts=[wallet.PlannedAct("WRITE_NEW_KEY"),
                                         wallet.PlannedAct("WRITE_SAME_KEY", fee=wallet.FeeChoice(
                                             fee_mode=1, fee_sponsor=SPONSOR_ADDRESS, fee_auth_until=EXPIRY))],
                                   domain_tag=DOMAIN, verifier_version=VERSION, expiry=EXPIRY, max_account_fee=FEE,
                                   **own_kw())
        x1 = plan.elements[1]
        self.assertEqual((x1.migration_nonce, x1.commitment, x1.epoch, x1.pi[169], x1.pi[170:190].hex()),
                         (2, c1, 1, 1, SPONSOR_ADDRESS))
        bundle = self.build(plan, state, h, proofs={0: b"P-S", 1: b"P-S2"}, sponsor=self.model_sponsor())
        end = self.tracker.bundle_preview(SCOPE, bundle)["end_state"]
        self.assertEqual((end["mode"], end["migration_nonce"], end["commitment"]), ("PQ_BY_PROOF", 3, c1.hex()))
        tx = reference_protocol().rlp_decode(bundle.elements[1].carrier[1:])
        self.assertEqual(tx[13][0].hex(), SPONSOR_ADDRESS)    # the named sponsor carries it, so it can be reimbursed

    def test_v6_v22w7_ii_after_E_the_early_finalisation_is_a_sponsored_write_that_the_adapter_builds(self):
        h = frozen_head(fork_time=9_000_000, timestamp=1000, account_nonce=0)
        state = canonical_state(13376, "11" * 32, "22" * 20, h.block_hash, 0, timestamp=1000, fork_time=9_000_000,
                                override_window=W)
        e = Authorization(ACCOUNT, "ENROLL", 0, self.keys[0].commitment, epoch=0)
        p = self.learned_pi(1, 1)
        self.tracker.record(SCOPE, e, b"E", **IN_BLOCK)
        wallet.learn_authorization(SCOPE, SEED, self.crypto, self.store, self.tracker, p, b"P")
        self.store.mark_compromised(SCOPE, 1, "W records epoch 1")
        offer = offer_for(self.tracker.observe_head(SCOPE, h), p)
        acts = wallet.acts_from_offer(offer, sponsored=wallet.FeeChoice(fee_mode=2))
        plan = wallet.plan_payload(SCOPE, state, self.store, SEED, self.crypto, tracker=self.tracker, head=h, acts=acts,
                                   domain_tag=DOMAIN, verifier_version=VERSION, expiry=EXPIRY, max_account_fee=FEE,
                                   **own_kw())
        self.assertEqual([(x.kind, x.migration_nonce, x.commitment) for x in plan.elements],
                         [("ENROLL", None, self.keys[0].commitment), ("WRITE", 1, self.keys[0].commitment)])
        bundle = self.build(plan, state, h, proofs={1: b"MODEL-PROOF-OF-S1"}, carriers={0: b"E"}, sponsor=self.model_sponsor())
        self.assertTrue(self.sponsor_signature_verifies(bundle.elements[1].carrier, 13))
        preview = self.tracker.bundle_preview(SCOPE, bundle)
        # A's own 0x7d placed before the payload pops E, and S1 still applies through the override gate it opened.
        by = {x["by"]: x["end_state"] for x in preview["preemptions"]}
        self.assertEqual(by["0x7D_OF_A_AT_THE_ACCOUNT_NONCE"]["migration_nonce"], 2)
        payloads = []
        self.tracker.export_bundle(SCOPE, bundle, payloads.append)
        self.assertEqual(payloads[0][0], b"E")

    def test_v6_v23w2_S1_matches_C_0_of_S_1_keeps_epoch_0_and_is_built_by_the_adapter(self):
        n = 3
        state = canonical_state(13376, "11" * 32, "22" * 20, "a0" * 32, 0, timestamp=1000, fork_time=None,
                                override_window=W)
        h = self.head_for(state, account_nonce=n, number=10, timestamp=1000)
        self.tracker.record(SCOPE, Authorization(ACCOUNT, "ENROLL", n, self.keys[0].commitment, epoch=0), b"E", **IN_BLOCK)
        self.tracker.observe_head(SCOPE, h)
        plan = wallet.plan_payload(SCOPE, state, self.store, SEED, self.crypto, tracker=self.tracker, head=h,
                                   acts=[act("ENROLL"), act("WRITE_SAME_KEY", 2)], domain_tag=DOMAIN,
                                   verifier_version=VERSION, expiry=EXPIRY, max_account_fee=FEE)
        bundle = self.build(plan, state, h, proofs={1: b"P-S1"}, carriers={0: b"E"}, sponsor=self.model_sponsor())
        tx = reference_protocol().rlp_decode(bundle.elements[1].carrier[1:])
        self.assertEqual((tx[2], tx[4], tx[7]), (b"\x01", self.keys[0].commitment, b"\x02"))   # nonce 1, C_0, mode 2
        self.assertEqual(plan.elements[1].epoch, 0)

    def test_v6_v23w3_as_corrected_at_B_prime_S2_alone_keeps_its_pi_and_proof(self):
        state, h, s, p = self.v22w2()
        c1 = self.keys[1].commitment
        plan = wallet.plan_payload(SCOPE, state, self.store, SEED, self.crypto, tracker=self.tracker, head=h,
                                   acts=[act("WRITE_NEW_KEY"), act("WRITE_SAME_KEY", 2)], domain_tag=DOMAIN,
                                   verifier_version=VERSION, expiry=EXPIRY, max_account_fee=FEE, **own_kw())
        # B': S alone, split off the payload by a builder that received it, is included (37.3 rule 8).
        moved_state = canonical_state(13376, "11" * 32, "22" * 20, "f5" * 32, 2, status="PQ_BY_PROOF", commitment=c1,
                                      timestamp=2012, fork_time=900, override_window=W, enrolled_at=850)
        moved = AccountState(ACCOUNT, "f5" * 32, 32, 2012, 2, 7, "PQ_BY_PROOF", False, c1, 900, W, 850)
        self.tracker.observe_head(SCOPE, moved, inclusions=())
        replanned = wallet.replan_payload(plan, SCOPE, moved_state, self.store, SEED, self.crypto, tracker=self.tracker,
                                          head=moved)
        self.assertEqual(replanned.status, "VOID")
        offer = offer_for(self.tracker.observe_head(SCOPE, moved), p)
        self.assertEqual(offer["action"], "OFFER_FINALIZING_ACTIVATION_OR_ADVANCE_PAST_PI_NONCE")
        # S_2 alone, its PI and proof unchanged: the same re-commit prepared at B' is byte-identical, and it leaves.
        moved_key = scan_current_key(SCOPE, moved_state, lambda e: self.keys[e].commitment).current_key
        again = wallet.prepare_recommit(SCOPE, moved_state, self.store, moved_key, SEED, self.crypto, tracker=self.tracker,
                                        domain_tag=DOMAIN, verifier_version=VERSION, expiry=EXPIRY, max_account_fee=FEE,
                                        confirm_extra_proof_and_fee=True, fee=wallet.FeeChoice(fee_mode=2))
        self.assertEqual(again.pi, plan.elements[1].pi)
        wallet.export_recovery(again, SCOPE, moved_state, self.store, self.tracker,
                               **self.export_kwargs(again, moved), sponsor=self.model_sponsor())
        self.assertEqual(len(self.sent), 1)

    def test_v6_rot_d2_the_rotate_calldata_is_the_strict_abi(self):
        pk, pop = bytes(range(256)) * 5 + bytes(32), bytes([7]) * 2420     # ML-DSA-44 lengths: 1,312 and 2,420
        data = wallet.rotate_calldata(1, pk, pop)
        self.assertEqual(len(data), 3908)                       # 164 + P1 + P2 (24.2 rule 2)
        word = lambda i: int.from_bytes(data[i:i + 32], "big")
        self.assertEqual((data[:4].hex(), word(4), word(36), word(68), word(100), word(132 + 1312)),
                         ("262f8ae0", 1, 0x60, 0x80 + 1312, 1312, 2420))
        self.assertEqual((data[132:132 + 1312], data[1476:1476 + 2420], data[1476 + 2420:]), (pk, pop, bytes(12)))

    def test_v6_layout_1_carriers_decode_under_a_layout_1_version_only(self):
        state = self.frozen_state()
        h = self.head_for(state, account_nonce=7)
        self.tracker.observe_head(SCOPE, h)
        consent = wallet.fee_consent(layout=1, max_account_fee=FEE, verifier_version=VERSION)["token"]
        ref = reference_protocol()
        for sponsored_carrier in (False, True):
            with self.subTest(sponsored=sponsored_carrier):
                self.fresh_wallet(f"layout1-{sponsored_carrier}")
                self.tracker.observe_head(SCOPE, h)
                plan = self.plan(state, fee=wallet.FeeChoice(layout=1, sponsored=sponsored_carrier, consent=consent))
                wallet.export_recovery(plan, SCOPE, state, self.store, self.tracker,
                                       **{**self.export_kwargs(plan, h), "config": dict(CONFIG, pi_layout=1)},
                                       **(self.sponsor_kw() if sponsored_carrier else {}))
                raw = self.sent[-1]
                kind, tx, layout = ref.decode(raw, {VERSION: ref.Version(1, 0, 10**12)})
                self.assertEqual((layout, len(tx), tx[10] != []), (1, 14, sponsored_carrier))
                with self.assertRaises(ref.Invalid):            # V-5: new bytes under a version of the other layout
                    ref.decode(raw, {VERSION: ref.Version(2, 0, 10**12)})


# ------------------------------------------------------------------------------------------------
# The draft of spec section 39.2 rule 1 (the act in the re-commit gate and after a precursor, against a
# member that changes the commitment: the case that section 38.3 recorded as open), section 31.2 rule 5's range
# repair for a key that only MATCH_ABOVE_BOUND finds (rule 10 (d), 38.3 rule 3), and the reading of
# l. 417 (38.3 rule 1, S-12). A test_v7_ test mirrors a wallet part of vector V26-W-1, V27-W-1 or V27-W-2 (or
# V27-W-1's consensus part in the model) and is required here only.

SPONSORED_WRITES_LABEL = "OFFER_SPONSORED_WRITES_PAST_PI_NONCE"
RANGE_REPAIR_LABEL = "OFFER_RANGE_REPAIR"
SPONSORED_WRITES_ACT = "SPONSORED_WRITES_PAST_PI_MIGRATION_NONCE"


def select_or_fail(test, state, store, **kwargs):
    """select_new_key_epoch, with a refusal turned into an assertion."""
    try:
        return wallet_epochs.select_new_key_epoch(SCOPE, state, store, **kwargs)
    except ValueError as exc:
        test.fail(f"the selection refuses the key that MATCH_ABOVE_BOUND found: {exc}")


class SponsoredRemedyBase(SigningPolicyBase):
    def v27w1(self, *, v_epoch=1, with_v=True):
        """V27-W-1 after the reorganization: `a` is PQ_BY_PROOF, code empty, migration_nonce 1 with C_0 (K_0 not exposed),
        account nonce 5, T past; V, another device's re-commit at nonce 1 committing C_<v_epoch> (X1 = 4500), and P, that
        device's re-commit at nonce 2 committing C_2 (X = 6000), both of fee mode 2, were in blocks of the abandoned
        branch (A holds them) and are learned there; W records epoch 2."""
        c0 = self.keys[0].commitment
        state = canonical_state(13376, "11" * 32, "22" * 20, "c7" * 32, 1, status="PQ_BY_PROOF", commitment=c0,
                                timestamp=2000, fork_time=900, override_window=W)
        h = AccountState(ACCOUNT, "c7" * 32, 30, 2000, 1, 5, "PQ_BY_PROOF", False, c0, 900, W, 0)
        v = sponsored(self.learned_pi(1, v_epoch, expiry=4500))
        p = sponsored(self.learned_pi(2, 2, expiry=6000))
        if with_v:
            wallet.learn_authorization(SCOPE, SEED, self.crypto, self.store, self.tracker, v, b"V-of-another-device")
        wallet.learn_authorization(SCOPE, SEED, self.crypto, self.store, self.tracker, p, b"P-of-another-device")
        self.store.mark_compromised(SCOPE, 2, "K_2 exposed; W records epoch 2")
        wallet.observe_head(SCOPE, SEED, self.crypto, self.store, self.tracker, h)
        return state, h, v, p

    def v27w2(self, *, with_e1=True):
        """V27-W-2 after the reorganization: W's own enrollment (C_0, K_0 not exposed) at migration_nonce 1, the override
        gate open, account nonce 8; S, W's override at nonce 1 committing C_1 (X1 = 4600), in a block of the abandoned
        branch; P, another device's re-commit at nonce 2 committing C_2 (X = 6000), learned there; and E1, a third
        device's same-key early finalisation at nonce 1 committing C_0 (X0 = 4500), seen in a pool (A holds all three);
        W records epoch 2."""
        c0 = self.keys[0].commitment
        state = canonical_state(13376, "11" * 32, "22" * 20, "d7" * 32, 1, status="PQ_BY_ENROLL", commitment=c0,
                                timestamp=2000, fork_time=900, override_window=W, enrolled_at=950)
        h = AccountState(ACCOUNT, "d7" * 32, 31, 2000, 1, 8, "PQ_BY_ENROLL", False, c0, 900, W, 950)
        s = sponsored(self.pi_of(1, 1, expiry=4600))
        p = sponsored(self.learned_pi(2, 2, expiry=6000))
        self.tracker.record(SCOPE, s, b"S-override-of-branch-1", **IN_BLOCK)
        wallet.learn_authorization(SCOPE, SEED, self.crypto, self.store, self.tracker, p, b"P-of-another-device")
        if with_e1:
            e1 = sponsored(self.learned_pi(1, 0, expiry=4500))
            wallet.learn_authorization(SCOPE, SEED, self.crypto, self.store, self.tracker, e1, b"E1-seen-in-a-pool",
                                       custody="IN_POOL")
        self.store.mark_compromised(SCOPE, 2, "K_2 exposed; W records epoch 2")
        wallet.observe_head(SCOPE, SEED, self.crypto, self.store, self.tracker, h)
        return state, h, s, p

    def above_bound(self, *, activated=False, block="a7"):
        """B: PQ_BY_PROOF at migration_nonce 2 whose current key is the key of epoch 4 (a rotate that applied below its
        selection nonce, 31.2 rule 5), account nonce 9: the in-bound scan finds nothing, and the above-bound aid, on the
        owner's request, MATCH_ABOVE_BOUND at e = 4."""
        c4 = self.keys[4].commitment
        state = canonical_state(13376, "11" * 32, "22" * 20, block * 32, 2, status="PQ_BY_PROOF", activated=activated,
                                commitment=c4)
        h = AccountState(ACCOUNT, block * 32, 31, 2000, 2, 9, "PQ_BY_PROOF", activated, c4, None, W, 0)
        self.tracker.observe_head(SCOPE, h)
        derive = lambda e: wallet.derive_key(SCOPE, SEED, e, self.crypto).commitment     # noqa: E731
        self.assertEqual(scan_current_key(SCOPE, state, derive).status, "NO_MATCH_WITHIN_BOUND")
        found = wallet_epochs.scan_above_bound(SCOPE, state, derive, owner_request=True)
        self.assertEqual((found.status, found.current_key.epoch), ("MATCH_ABOVE_BOUND", 4))
        return state, h, found.current_key

    def plan_acts(self, offer):
        return [(x["kind"], x.get("migration_nonce"), x.get("key"), x.get("fee")) for x in offer["payload"]["plan"]["acts"]]


class SponsoredRemedyRegressionTests(SponsoredRemedyBase):
    """Section 39.2 rule 1, section 31.2 rule 5 and section 38.3 rule 1."""

    # ---- spec 39.2 rule 1: the activation as the act, and the sponsored writes otherwise
    def test_r7_a_v27w1_the_activation_is_no_act_where_a_write_of_another_key_stands_at_the_current_nonce(self):
        state, h, v, p = self.v27w1()
        offer = offer_for(self.tracker.observe_head(SCOPE, h), p)
        # The activation of K_0 alone, which V, held by A, placed before it makes fail (BAD_ACTIVATION, l. 315)
        # while P is includable after V (check 6, l. 265).
        self.assertEqual(offer["action"], SPONSORED_WRITES_LABEL)
        payload = offer["payload"]
        self.assertEqual((payload["case"], payload["act"], payload["fee_path"], payload["then_once_in_a_block"]),
                         ("RECOMMIT", SPONSORED_WRITES_ACT, "SPONSOR", "ACTIVATION_OF_THE_KEY_THE_WRITES_COMMIT"))
        self.assertEqual(self.plan_acts(offer), [("WRITE", 1, "SAME_KEY_AS_ITS_PLANNING_STATE", "SPONSORED"),
                                                 ("WRITE", 2, "SAME_KEY_AS_ITS_PLANNING_STATE", "SPONSORED")])
        run = payload["activation_rejected"]["run"]
        self.assertIn(f"TRACKED_PI_{v.group_id[:12]}", run)       # V placed before the activation
        self.assertEqual(run[-1][:len("INCLUDABLE_AFTER_THE_PAYLOAD")], "INCLUDABLE_AFTER_THE_PAYLOAD")

    def test_r7_a_v27w1_the_writes_are_planned_built_and_delivered_as_one_payload(self):
        state, h, v, p = self.v27w1()
        offer = offer_for(self.tracker.observe_head(SCOPE, h), p)
        self.assertIn("plan", offer.get("payload") or {}, "the offer must include the sponsored writes")
        acts = wallet.acts_from_offer(offer, sponsored=wallet.FeeChoice(fee_mode=2))
        self.assertEqual([(x.kind, x.fee_mode) for x in acts], [("WRITE_SAME_KEY", 2), ("WRITE_SAME_KEY", 2)])
        key0 = scan_current_key(SCOPE, state, lambda e: self.keys[e].commitment).current_key
        plan = wallet.plan_payload(SCOPE, state, self.store, SEED, self.crypto, tracker=self.tracker, head=h, acts=acts,
                                   domain_tag=DOMAIN, verifier_version=VERSION, expiry=EXPIRY, max_account_fee=FEE,
                                   current_key=key0)
        c0 = self.keys[0].commitment
        self.assertEqual([(e.kind, e.migration_nonce, e.commitment, e.epoch, e.pi[169]) for e in plan.elements],
                         [("WRITE", 1, c0, 0, 2), ("WRITE", 2, c0, 0, 2)])
        bundle = self.build(plan, state, h, proofs={0: b"P-W1", 1: b"P-W2"}, sponsor=self.model_sponsor())
        self.assertTrue(all(self.sponsor_signature_verifies(e.carrier, 13) for e in bundle.elements))
        analysis = self.tracker.bundle_preview(SCOPE, bundle)
        self.assertEqual(analysis["revived_between_elements"], [[p.group_id, p.variant_id]])   # W_1 alone opens P
        payloads = []
        self.tracker.export_bundle(SCOPE, bundle, payloads.append)
        self.assertEqual(payloads, [tuple(e.carrier for e in bundle.elements)])

    def test_r7_a_v27w1_a_lone_same_key_write_at_the_current_nonce_gets_the_writes_as_its_remedy(self):
        state, h, v, p = self.v27w1()
        w1 = sponsored(self.pi_of(1, 0))                     # W's same-key re-commit of C_0 at nonce 1, alone
        with self.assertRaises(at.RevivalWarning) as caught:
            self.tracker.export(SCOPE, w1, b"W1-alone", self.sent.append, head=h)
        # ACTIVATE_CURRENT_KEY_FIRST, the activation that V makes fail.
        self.assertEqual(caught.exception.remedy, "ONE_PAYLOAD_BUNDLE")
        self.assertEqual(caught.exception.payload["act"], SPONSORED_WRITES_ACT)
        self.assertEqual(self.sent, [])

    def test_r7_a_v27w2_a_write_that_displaces_the_precursor_makes_the_sponsored_write_the_act(self):
        state, h, s, p = self.v27w2()
        offer = offer_for(self.tracker.observe_head(SCOPE, h), p)
        payload = offer["payload"]
        # The activation of the precursor's key, which the other write at nonce 1, placed before the payload,
        # makes fail after displacing the precursor (check 6; BAD_ACTIVATION).
        self.assertEqual((payload["act"], payload.get("activation_as_act")), (SPONSORED_WRITES_ACT, False))
        self.assertIn("displaces the precursor", payload["why"])
        acts = self.plan_acts(offer)
        self.assertEqual([(kind, nonce, fee) for kind, nonce, _, fee in acts],
                         [("WRITE", 1, "SPONSORED"), ("WRITE", 2, "SPONSORED")])
        self.assertEqual(acts[1][2], "SAME_KEY_AS_ITS_PLANNING_STATE")

    def test_r7_a_v27w2_the_activation_after_S_is_refused_and_the_sponsored_write_after_S_passes(self):
        state, h, s, p = self.v27w2()
        s_el = self.write(s, b"S-override-of-branch-1")
        with self.assertRaisesRegex(ValueError, "BUNDLE_ACT_PREEMPTIBLE"):      # the bundle passes
            self.tracker.bundle_preview(SCOPE, at.OnePayloadBundle(h, (s_el, self.activation_element(1, 8))))
        w2 = sponsored(self.pi_of(2, 1))                     # the sponsored same-key re-commit of C_1 at nonce 2
        analysis = self.tracker.bundle_preview(SCOPE, at.OnePayloadBundle(h, (s_el, self.write(w2, b"W2"))))
        self.assertEqual(analysis["revived_between_elements"], [[p.group_id, p.variant_id]])

    # ---- 31.2 rule 5: the range repair of a key that only MATCH_ABOVE_BOUND finds (rule 10 (d), 38.3 rule 3)
    def test_r7_d_match_above_bound_offers_the_range_repair_before_any_new_selection(self):
        state, h, key = self.above_bound()
        selected = select_or_fail(self, state, self.store, current_key=key)
        self.assertEqual((selected.status, selected.epoch, getattr(selected, "repair_steps", None), selected.steps),
                         ("OFFER_RANGE_REPAIR", 4, 3, (STEP_RECOMMIT, STEP_ACTIVATING_ROTATE)))

    def test_r7_d_no_new_key_is_selected_while_the_repair_is_due(self):
        state, h, key = self.above_bound()
        select_or_fail(self, state, self.store, current_key=key)          # the wallet learns the key above U
        with self.assertRaisesRegex(ValueError, "CURRENT_KEY_ABOVE_U_SAME_KEY_REPAIR_BEFORE_ANY_NEW_SELECTION"):
            self.plan(state)                                               # a new key at m = 2
        with self.assertRaisesRegex(ValueError, "CURRENT_KEY_ABOVE_U_SAME_KEY_REPAIR_BEFORE_ANY_NEW_SELECTION"):
            wallet.plan_payload(SCOPE, state, self.store, SEED, self.crypto, tracker=self.tracker, head=h,
                                acts=[act("WRITE_NEW_KEY"), act("ACTIVATION")], domain_tag=DOMAIN,
                                verifier_version=VERSION, expiry=EXPIRY, max_account_fee=FEE)

    def test_r7_d_the_repair_step_is_prepared_with_the_above_bound_key_and_keeps_its_epoch(self):
        state, h, key = self.above_bound()
        try:
            step = wallet.prepare_recommit(SCOPE, state, self.store, key, SEED, self.crypto, tracker=self.tracker,
                                           domain_tag=DOMAIN, verifier_version=VERSION, expiry=EXPIRY,
                                           max_account_fee=FEE, confirm_extra_proof_and_fee=True)
        except ValueError as exc:
            self.fail(f"the range repair's step is refused: {exc}")
        c4 = self.keys[4].commitment
        self.assertEqual((step.same_key_recommit, step.key.epoch, int.from_bytes(step.pi[84:92], "big"),
                          step.pi[93:125]), (True, 4, 2, c4))
        self.assertTrue(wallet.validate_plan(step, SCOPE, state, self.store, self.tracker, seed64=SEED,
                                             crypto=self.crypto))
        wallet.export_recovery(step, SCOPE, state, self.store, self.tracker, **self.export_kwargs(step, h))
        self.assertEqual(len(self.sent), 1)

    def test_r7_d_three_same_key_writes_bring_the_key_inside_U_and_then_a_new_key_is_selected(self):
        state, h, key = self.above_bound()
        try:
            plan = wallet.plan_payload(SCOPE, state, self.store, SEED, self.crypto, tracker=self.tracker, head=h,
                                       acts=[act("WRITE_SAME_KEY")] * 3 + [act("WRITE_NEW_KEY")], domain_tag=DOMAIN,
                                       verifier_version=VERSION, expiry=EXPIRY, max_account_fee=FEE, current_key=key)
        except ValueError as exc:
            self.fail(f"the range repair is not planned: {exc}")
        self.assertEqual([(e.migration_nonce, e.epoch, e.role) for e in plan.elements],
                         [(2, 4, "SAME_KEY"), (3, 4, "SAME_KEY"), (4, 4, "SAME_KEY"), (5, 5, "NEW_KEY")])
        with self.assertRaisesRegex(ValueError, "CURRENT_KEY_ABOVE_U_SAME_KEY_REPAIR_BEFORE_ANY_NEW_SELECTION"):
            wallet.plan_payload(SCOPE, state, self.store, SEED, self.crypto, tracker=self.tracker, head=h,
                                acts=[act("WRITE_SAME_KEY"), act("WRITE_NEW_KEY")], domain_tag=DOMAIN,
                                verifier_version=VERSION, expiry=EXPIRY, max_account_fee=FEE, current_key=key)
        after = canonical_state(13376, "11" * 32, "22" * 20, "a9" * 32, 5, status="PQ_BY_PROOF",
                                commitment=self.keys[4].commitment)
        found = scan_current_key(SCOPE, after, lambda e: self.keys[e].commitment)
        self.assertEqual((found.status, found.current_key.epoch), ("MATCH", 4))   # the key lies inside U again

    def test_r7_d_observe_head_offers_the_range_repair_for_an_above_bound_current_epoch(self):
        state, h, key = self.above_bound()
        notice = self.tracker.observe_head(SCOPE, h, current_epoch=4)
        repair = [(o["epoch"], o["repair_steps"], o["found_by"]) for o in notice["offers"]
                  if o.get("action") == RANGE_REPAIR_LABEL]
        self.assertEqual(repair, [(4, 3, "MATCH_ABOVE_BOUND")])               # no offer

    def test_r7_d_an_activated_account_repairs_by_rotates_to_the_current_key(self):
        state, h, key = self.above_bound(activated=True, block="a8")
        selected = select_or_fail(self, state, self.store, current_key=key)
        self.assertEqual((selected.status, selected.steps), ("OFFER_RANGE_REPAIR", (STEP_ROTATE,)))
        step = wallet.prepare_same_key_rotate(SCOPE, state, self.store, key, SEED, self.crypto, ROTATE_CONFIG,
                                              tracker=self.tracker, head=h, confirm_extra_transaction_and_fee=True)
        a, c4 = step.authorization, self.keys[4].commitment
        self.assertEqual((a.kind, a.nonce, a.commitment, a.signer_commitment, a.activating, a.epoch),
                         ("ROTATE", 9, c4, c4, False, 4))
        wallet.export_same_key_rotate(step, SCOPE, state, self.store, key, SEED, self.crypto, tracker=self.tracker,
                                      head=h, deliver=self.sent.append)
        self.assertEqual(self.sent, [step.raw])

    # ---- spec 38.3 rule 1 (S-12): own funds in the override of another party's enrollment
    def test_r7_s12_own_funds_there_only_where_no_sponsored_path_exists_and_after_the_warning(self):
        c_ext, f, state, h = self.stealth()
        self.tracker.observe_head(SCOPE, h)
        with self.assertRaisesRegex(ValueError, "OWN_FUNDS_WHILE_A_SPONSORED_PATH_EXISTS"):
            self.plan(state, fee=wallet.FeeChoice())                 # prepared, with a warning
        with self.assertRaises(ValueError) as error:
            self.plan(state, fee=wallet.FeeChoice(), no_sponsored_path=True)
        self.assertEqual(str(error.exception),
                         "OWN_FUNDS_NEEDS_THE_DISPLAYED_WARNING: the wallet shows own_funds_warning() and prepares the "
                         "override that a pays only on the owner's explicit choice after it (confirm_own_funds; l. 252, "
                         "l. 417; spec 38.3 rule 1)")
        warning = wallet.own_funds_warning(legacy_address=ACCOUNT.address, max_account_fee=FEE, verifier_version=VERSION)
        self.assertIn("take the account's balance before the override lands", warning["statement"])
        plan = self.plan(state, fee=wallet.FeeChoice(), no_sponsored_path=True, confirm_own_funds=warning["token"])
        self.assertEqual((plan.pi[169], plan.warnings[0].split(":")[0]),
                         (0, "OWN_FUNDS_WHERE_ANOTHER_PARTY_CAN_SEND_FROM_A"))
        self.assertEqual(self.plan(state, fee=wallet.FeeChoice(fee_mode=2)).warnings, ())

    def test_r7_s12_a_payload_whose_first_write_a_pays_follows_the_same_reading(self):
        state, h, s, p = self.v22w2()
        acts = [act("WRITE_NEW_KEY"), act("WRITE_SAME_KEY", 2)]
        kwargs = dict(tracker=self.tracker, head=h, acts=acts, domain_tag=DOMAIN, verifier_version=VERSION,
                      expiry=EXPIRY, max_account_fee=FEE)
        with self.assertRaisesRegex(ValueError, "OWN_FUNDS_WHILE_A_SPONSORED_PATH_EXISTS"):
            wallet.plan_payload(SCOPE, state, self.store, SEED, self.crypto, **kwargs)   # planned, warned
        plan = wallet.plan_payload(SCOPE, state, self.store, SEED, self.crypto, **kwargs, **own_kw())
        self.assertEqual(plan.warnings[0].split(":")[0], "OWN_FUNDS_WHERE_ANOTHER_PARTY_CAN_SEND_FROM_A")
        sponsored_first = [wallet.PlannedAct("WRITE_NEW_KEY", fee=wallet.FeeChoice(fee_mode=2)), act("WRITE_SAME_KEY", 2)]
        self.assertEqual(wallet.plan_payload(SCOPE, state, self.store, SEED, self.crypto,
                                             **{**kwargs, "acts": sponsored_first}).warnings, ())

    def test_r7_s12_the_warning_token_binds_the_account_the_cap_and_the_version(self):
        self.assertTrue(hasattr(wallet, "own_funds_warning"), "own funds require the displayed warning")
        c_ext, f, state, h = self.stealth()
        self.tracker.observe_head(SCOPE, h)
        for fields in ({"legacy_address": "33" * 20, "max_account_fee": FEE, "verifier_version": VERSION},
                       {"legacy_address": ACCOUNT.address, "max_account_fee": FEE + 1, "verifier_version": VERSION},
                       {"legacy_address": ACCOUNT.address, "max_account_fee": FEE, "verifier_version": VERSION + 1}):
            other = wallet.own_funds_warning(**fields)["token"]
            with self.subTest(fields=fields), self.assertRaisesRegex(ValueError, "OWN_FUNDS_NEEDS_THE_DISPLAYED_WARNING"):
                self.plan(state, fee=wallet.FeeChoice(), no_sponsored_path=True, confirm_own_funds=other)


class SponsoredRemedyCoverageTests(SponsoredRemedyBase):
    """Behaviours that the draft keeps."""

    def test_cov7_v27w1_iv_a_same_key_write_at_the_current_nonce_keeps_the_activation_as_the_act(self):
        state, h, v, p = self.v27w1(v_epoch=0)               # V commits C_0 again, as S1 of WE-16 does
        self.assertEqual(offer_for(self.tracker.observe_head(SCOPE, h), p)["action"], ACTIVATION_LABEL)

    def test_cov7_without_a_write_at_the_current_nonce_the_activation_stays_the_act(self):
        state, h, v, p = self.v27w1(with_v=False)
        self.assertEqual(offer_for(self.tracker.observe_head(SCOPE, h), p)["action"], ACTIVATION_LABEL)

    def test_cov7_v22w2_vi_without_a_displacing_write_the_activation_after_S_stays_the_act(self):
        state, h, s, p = self.v27w2(with_e1=False)
        payload = offer_for(self.tracker.observe_head(SCOPE, h), p)["payload"]
        self.assertEqual(payload["act"], "ACTIVATION_OF_THE_KEY_THE_WRITE_COMMITS")
        bundle = at.OnePayloadBundle(h, (self.write(s, b"S-override-of-branch-1"), self.activation_element(1, 8)))
        self.assertEqual(self.tracker.bundle_preview(SCOPE, bundle)["revived_between_elements"],
                         [[p.group_id, p.variant_id]])

    def test_cov7_v22w1_the_frozen_gate_keeps_the_activation_after_S(self):
        state, h, s, p = self.v22w1()
        payload = offer_for(self.tracker.observe_head(SCOPE, h), p)["payload"]
        self.assertEqual(payload["act"], "ACTIVATION_OF_THE_KEY_THE_WRITE_COMMITS")

    def test_cov7_a_recorded_above_bound_key_is_no_range_repair(self):
        c4 = self.keys[4].commitment
        state = canonical_state(13376, "11" * 32, "22" * 20, "aa" * 32, 2, status="PQ_BY_PROOF", commitment=c4)
        h = AccountState(ACCOUNT, "aa" * 32, 31, 2000, 2, 9, "PQ_BY_PROOF", False, c4, None, W, 0)
        self.tracker.observe_head(SCOPE, h)
        self.store.mark_compromised(SCOPE, 4, "K_4 exposed (31.2 rule 7)")
        derive = lambda e: self.keys[e].commitment                                         # noqa: E731
        key = wallet_epochs.scan_above_bound(SCOPE, state, derive, owner_request=True).current_key
        kwargs = {"current_key": key} if hasattr(wallet_epochs.CurrentKey, "above_bound") else {}
        selected = wallet_epochs.select_new_key_epoch(SCOPE, state, self.store, **kwargs)
        self.assertEqual((selected.status, selected.epoch), ("SELECTED", 2))     # 31.2 rule 7 (b)'s replacement
        with self.assertRaises(ValueError):
            wallet.prepare_recommit(SCOPE, state, self.store, key, SEED, self.crypto, tracker=self.tracker,
                                    domain_tag=DOMAIN, verifier_version=VERSION, expiry=EXPIRY, max_account_fee=FEE,
                                    confirm_extra_proof_and_fee=True)

    def test_cov7_a_replan_keeps_the_owners_confirmed_own_funds_choice(self):
        c_ext, f, state, h = self.stealth()                  # A's enrollment C_ext at migration_nonce 1, nonce 7
        self.tracker.observe_head(SCOPE, h)
        acts = [act("WRITE_NEW_KEY"), act("WRITE_SAME_KEY", 2), act("ACTIVATION")]
        plan = wallet.plan_payload(SCOPE, state, self.store, SEED, self.crypto, tracker=self.tracker, head=h, acts=acts,
                                   domain_tag=DOMAIN, verifier_version=VERSION, expiry=EXPIRY, max_account_fee=FEE,
                                   **own_kw())
        # B': A's activation of its enrolled key took account nonce 7 (the override gate has no code condition).
        moved = AccountState(ACCOUNT, "f6" * 32, 32, 2012, 1, 8, "PQ_BY_ENROLL", True, c_ext, 900, W, 850)
        moved_state = canonical_state(13376, "11" * 32, "22" * 20, "f6" * 32, 1, status="PQ_BY_ENROLL", activated=True,
                                      commitment=c_ext, timestamp=2012, fork_time=900, override_window=W, enrolled_at=850)
        self.tracker.observe_head(SCOPE, moved)
        replanned = wallet.replan_payload(plan, SCOPE, moved_state, self.store, SEED, self.crypto, tracker=self.tracker,
                                          head=moved)
        self.assertEqual(replanned.status, "VOID")
        self.assertIsNotNone(replanned.plan, replanned.error)  # the owner's choice of own funds is prepared again
        self.assertEqual([(e.kind, e.migration_nonce, e.account_nonce) for e in replanned.plan.elements],
                         [("WRITE", 1, None), ("WRITE", 2, None), ("ACTIVATION", None, 8)])

    def test_cov7_own_funds_in_the_owners_own_enrollment_need_neither_statement_nor_warning(self):
        state, h, s, p = self.v27w2(with_e1=False)
        plan = self.plan(state)                               # the override to K_1, self-paid, without asking
        self.assertEqual((plan.pi[169], plan.warnings), (0, ()))


class SponsoredRemedyVectorTests(SponsoredRemedyBase):
    """Wallet parts of V26-W-1, V27-W-1 and V27-W-2, and V27-W-1's consensus part in the model; required here only."""

    def test_v7_v27w1_i_ii_the_model_reaches_the_outcomes_that_the_check_order_gives(self):
        import reachability as reach
        cfg = reach.Config(900, W)
        c0, c1, c2 = (self.keys[e].commitment for e in (0, 1, 2))
        head_st = reach.St("PQ_BY_PROOF", 1, 5, False, c0, 0)
        v = reach.Step("WRITE", 1, c1, expiry=4500)
        p = reach.Step("WRITE", 2, c2, expiry=6000)
        activation = reach.Step("ACTIVATION", 5, c0)
        w1, w2 = reach.Step("WRITE", 1, c0, expiry=EXPIRY), reach.Step("WRITE", 2, c0, expiry=EXPIRY)
        t = 2012
        self.assertFalse(reach.valid(p, head_st, t, cfg))                 # check 6 (0x0105)
        after_v = reach.apply(v, head_st, t, cfg)                         # Migrated(a, 0x01, C_1, 2, false, true)
        self.assertFalse(reach.valid(activation, after_v, t, cfg))        # BAD_ACTIVATION (l. 315)
        self.assertTrue(reach.valid(p, after_v, t, cfg))                  # Migrated(a, 0x01, C_2, 3, false, true)
        both = reach.apply(w2, reach.apply(w1, head_st, t, cfg), t, cfg)
        self.assertEqual((both.mn, both.commitment), (3, c0))
        self.assertFalse(reach.valid(p, both, t, cfg))                    # check 6 at every later position
        self.assertFalse(reach.valid(w1, after_v, t, cfg))                # W_1 popped after V (check 6)
        after = reach.apply(w2, after_v, t, cfg)                          # W_2 valid after V: C_0 at nonce 3
        self.assertEqual((after.mn, after.commitment, reach.valid(p, after, t, cfg)), (3, c0, False))
        final = reach.apply(activation, after, t, cfg)                    # Activated: final(a) and activated(a)
        self.assertTrue(reach.final(final, t, cfg) and final.activated)

    def test_v7_v27w1_iii_W_ends_P_only_at_a_chain_finalized_block_past_its_nonce(self):
        state, h, v, p = self.v27w1()
        self.assertEqual(offer_for(self.tracker.observe_head(SCOPE, h), p)["action"], SPONSORED_WRITES_LABEL)
        c0 = self.keys[0].commitment
        landed = AccountState(ACCOUNT, "c8" * 32, 31, 2012, 3, 5, "PQ_BY_PROOF", False, c0, 900, W, 0)
        self.assertEqual(actions_for(self.tracker.observe_head(SCOPE, landed), p), ["WAIT_FINALITY_WATCH_REORG"])
        f = replace(landed, number=29, block_hash="c6" * 32, timestamp=1990, migration_nonce=1)    # F: nothing ends
        self.assertEqual(self.tracker.observe_finalized(SCOPE, FinalizedView(f)), [])
        ended = self.tracker.observe_finalized(SCOPE, FinalizedView(landed, "c6" * 32))
        self.assertIn((p.group_id, p.variant_id, "MIGRATION_NONCE_CONSUMED"), list(ended))

    def test_v7_v27w1_iv_without_a_sponsored_path_writes_paid_by_a_under_the_balance_condition(self):
        state, h, v, p = self.v27w1()
        fallback = offer_for(self.tracker.observe_head(SCOPE, h), p)["payload"]["where_no_sponsored_path"]
        self.assertEqual((fallback["act"], fallback["otherwise"]["offers_meanwhile"]),
                         ("WRITES_PAID_BY_A_PAST_PI_MIGRATION_NONCE", "ACTIVATION_OF_THE_CURRENT_KEY"))
        self.assertEqual([(x["migration_nonce"], x["fee"]) for x in fallback["plan"]["acts"]],
                         [(1, "PAID_BY_A"), (2, "PAID_BY_A")])
        self.assertIn("BALANCE_COVERS_EVERY_TAKE", fallback["where"])

    def test_v7_v27w2_iii_W_offers_S_with_the_sponsored_recommit_that_the_adapter_builds(self):
        state, h, s, p = self.v27w2()
        offer = offer_for(self.tracker.observe_head(SCOPE, h), p)
        acts = wallet.acts_from_offer(offer, sponsored=wallet.FeeChoice(fee_mode=2))
        self.assertEqual([(x.kind, x.fee_mode) for x in acts], [("WRITE_NEW_KEY", 2), ("WRITE_SAME_KEY", 2)])
        # S itself, a carrier that A holds (expiry X1 = 4600): a fresh one would outlive it (34.2 rule 1 (b)).
        plan = wallet.plan_payload(SCOPE, state, self.store, SEED, self.crypto, tracker=self.tracker, head=h, acts=acts,
                                   domain_tag=DOMAIN, verifier_version=VERSION, expiry=4600, max_account_fee=FEE)
        c1 = self.keys[1].commitment
        self.assertEqual([(e.migration_nonce, e.commitment, e.epoch) for e in plan.elements], [(1, c1, 1), (2, c1, 1)])
        self.assertEqual(plan.elements[0].pi, s.pi)
        bundle = self.build(plan, state, h, proofs={0: b"P-S", 1: b"P-W2"}, sponsor=self.model_sponsor(4600))
        payloads = []
        self.tracker.export_bundle(SCOPE, bundle, payloads.append)
        self.assertEqual(len(payloads), 1)

    def test_v7_v26w1_ii_W_asks_for_a_fee_choice_and_prepares_the_sponsored_override(self):
        c_ext, f, state, h = self.stealth()
        self.tracker.observe_head(SCOPE, h)
        with self.assertRaisesRegex(ValueError, "FEE_CHOICE_REQUIRED"):
            self.plan(state)
        for fields in ({"fee_mode": 2}, {"fee_mode": 1, "fee_sponsor": SPONSOR_ADDRESS, "fee_auth_until": 4500}):
            with self.subTest(fields=fields):
                plan = self.plan(state, fee=wallet.FeeChoice(**fields))
                self.assertEqual((plan.pi[169], plan.warnings, plan.key.epoch), (fields["fee_mode"], (), 1))
        with self.assertRaisesRegex(ValueError, "OWN_FUNDS_WHILE_A_SPONSORED_PATH_EXISTS"):
            self.plan(state, fee=wallet.FeeChoice())
        own = self.plan(state, **own_funds())                 # no sponsored path; the owner's choice after the warning
        self.assertEqual((own.pi[169], len(own.warnings)), (0, 1))

    def test_v7_v26w1_contrast_the_owners_own_enrollment_then_its_key_recorded_exposed(self):
        state, h, s, p = self.v27w2(with_e1=False)
        self.assertEqual(self.plan(state).pi[169], 0)        # the owner's own enrollment, K_0 not exposed
        self.store.mark_compromised(SCOPE, 0, "K_0 exposed; W records epoch 0 (31.2 rule 7)")
        with self.assertRaisesRegex(ValueError, "FEE_CHOICE_REQUIRED"):
            self.plan(state)                                  # its holder can now take a's balance (l. 252)
        sponsored_override = self.plan(state, fee=wallet.FeeChoice(fee_mode=2))
        self.assertEqual((sponsored_override.key.epoch, sponsored_override.pi[93:125]), (1, self.keys[1].commitment))


if __name__ == "__main__":
    unittest.main(verbosity=2)
