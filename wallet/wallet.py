"""Public-test migration wallet: authorization tracking and monotonic key-exposure state."""
from dataclasses import dataclass, replace
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

from wallet_epochs import (
    CanonicalState, DerivationScope, WalletEpochStore, CurrentKey, UINT32_MAX, UINT64_MAX, check5_gate,
    derive_epoch_seed, local_seed_identity, select_new_key_epoch,
    revalidate_key_use, ROTATE_STEP_FORMS, STEP_ACTIVATING_ROTATE, WRITE_STEP_FORMS,
)
from authorization_tracking import (
    Account, AccountState, Authorization, AuthorizationTracker, OnePayloadBundle, PayloadElement, Transaction,
    activation_preview, legacy_before_T, state_gate, PI_LAYOUT_BYTES,
)

ROOT = Path(__file__).resolve().parent
SLOT = 12               # l. 1230: the earliest block after B is at B.timestamp + SLOT (the tracker's default slot)


def _load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


wire = _load("epoch_existing_wallet_wire", ROOT / "wire.py")


@dataclass(frozen=True)
class KeyMaterial:
    epoch: int
    xi: bytes  # Private key material: never persisted by this adapter.
    public_key: bytes
    commitment: bytes


@dataclass(frozen=True)
class FeeChoice:
    """(31.2 rule 10 (e)): the owner's fee choice for one PI, fixed before proving (l. 417; section 19.2).

    `layout` is the PI layout of the named verifier_version (its manifest's PI_LAYOUT_1, 169 bytes, or
    PI_LAYOUT_2, 198 bytes; section 19.2 'Layout identifier and version'). Under layout 2 the PI carries
    `fee_mode`, `fee_sponsor` and `fee_auth_until` (offsets 169, 170, 190): mode 0 self-pay (only an
    unsponsored single carries it), 1 a named sponsor with a fixed reimbursement, 2 a zero-reimbursement
    third-party submission, 3 the public bounty (only on the owner's explicit consent naming the cap and
    fee_auth_until, never by default: `consent`, the token of fee_consent()). Under layout 1 the PI has no fee
    field: `sponsored` says whether the owner's own carrier is sponsored, and `consent` is the owner's consent
    that any sponsor may collect up to the cap wherever a 0x7f of the version can carry the proof (l. 417;
    section 18.24). The canonical constraints of section 19.2 that do not depend on the expiry or the account are
    checked here; the others when a PI is built (_check_fee_choice).
    """
    layout: int = 2
    fee_mode: int | None = 0
    fee_sponsor: str | None = None
    fee_auth_until: int = 0
    sponsored: bool | None = None
    consent: str | None = None

    def __post_init__(self):
        if self.layout not in (1, 2):
            raise ValueError("PI_LAYOUT_UNKNOWN: a version's manifest names PI_LAYOUT_1 or PI_LAYOUT_2 (section 19.2)")
        if type(self.fee_auth_until) is not int or not 0 <= self.fee_auth_until <= UINT64_MAX:
            raise ValueError("fee_auth_until is a u64")
        if self.fee_sponsor is not None:
            if not isinstance(self.fee_sponsor, str) or len(self.fee_sponsor.removeprefix("0x")) != 40:
                raise ValueError("fee_sponsor is a 20-byte address")
            object.__setattr__(self, "fee_sponsor", bytes.fromhex(self.fee_sponsor.removeprefix("0x")).hex())
        if self.consent is not None and (not isinstance(self.consent, str) or not self.consent):
            raise ValueError("a consent is the token of fee_consent()")
        if self.layout == 1:
            if self.fee_mode not in (None, 0) or self.fee_sponsor is not None or self.fee_auth_until:
                raise ValueError("NON_CANONICAL_ENCODING: a layout-1 PI has no fee_mode, fee_sponsor or fee_auth_until "
                                 "(section 19.2, V-5)")
            object.__setattr__(self, "fee_mode", None)      # the default 0 means 'none' under layout 1
            if type(self.sponsored) is not bool:
                raise ValueError("a layout-1 choice states whether the owner's carrier is sponsored")
            return
        if self.sponsored is not None:
            raise ValueError("under layout 2 the fee mode says whether the carrier is sponsored (section 19.2 table)")
        if type(self.fee_mode) is not int or self.fee_mode not in (0, 1, 2, 3):
            raise ValueError("NON_CANONICAL_ENCODING: fee_mode is 0, 1, 2 or 3 (section 19.2)")
        if self.fee_mode == 1:
            if self.fee_sponsor is None or self.fee_sponsor == "00" * 20:
                raise ValueError("NON_CANONICAL_ENCODING: a mode-1 PI names its sponsor, fee_sponsor != 0^20 (section 19.2)")
        elif self.fee_sponsor is not None and self.fee_sponsor != "00" * 20:
            raise ValueError("NON_CANONICAL_ENCODING: only a mode-1 PI names a fee_sponsor (section 19.2)")
        if self.fee_mode in (0, 2) and self.fee_auth_until:
            raise ValueError("NON_CANONICAL_ENCODING: modes 0 and 2 have fee_auth_until = 0 (section 19.2)")

    @property
    def is_sponsored(self):
        """Who carries the PI: modes 1-3 only a sponsored carrier, mode 0 only an unsponsored single (section 19.2
        table); under layout 1 the owner's own carrier as chosen."""
        return self.sponsored if self.layout == 1 else self.fee_mode != 0

    def tail(self):
        """The three layout-2 fields of the PI (offsets 169-197); empty under layout 1."""
        if self.layout == 1:
            return b""
        return (bytes([self.fee_mode]) + bytes.fromhex(self.fee_sponsor or "00" * 20)
                + self.fee_auth_until.to_bytes(8, "big"))


SELF_PAY = FeeChoice()       # layout 2, mode 0: an owner who funds the migration from legacy_address (l. 417)


def fee_consent(*, layout, max_account_fee, verifier_version, fee_auth_until=0):
    """(l. 417; section 19.2): the consent that the wallet displays before proving, and its token.

    Mode 3 (layout 2) is selected only on the owner's explicit consent naming the cap and fee_auth_until; under a
    layout-1 version the wallet names the carriers on which max_account_fee can be collected and obtains the
    owner's consent that any sponsor may collect up to the cap wherever a 0x7f of the version can carry the proof
    (section 18.24). The caller shows `statement`, and passes `token` as FeeChoice.consent only after the owner
    confirmed it; a token binds the layout, the cap, fee_auth_until and the version."""
    for value, maximum, name in ((max_account_fee, (1 << 256) - 1, "max_account_fee"),
                                 (verifier_version, (1 << 32) - 1, "verifier_version"),
                                 (fee_auth_until, UINT64_MAX, "fee_auth_until")):
        if type(value) is not int or not 0 <= value <= maximum:
            raise ValueError(f"{name} is outside its range")
    if layout == 2:
        statement = (f"PUBLIC BOUNTY (fee mode 3, section 19.2): any sponsor that includes a valid carrier of this proof "
                     f"is reimbursed min({max_account_fee} wei, balance) from legacy_address while header.timestamp <= "
                     f"{fee_auth_until} (verifier_version {verifier_version}); this is never a wallet default (l. 417)")
    elif layout == 1:
        statement = (f"LAYOUT-1 BOUNTY (section 18.24 rows 1-6): any sponsor may collect up to {max_account_fee} wei from "
                     f"legacy_address on every carrier of verifier_version {verifier_version} that can carry the proof: "
                     "a sponsored single, a sponsored close and every 0x7f entry, re-wrapped by anyone (l. 285, l. 417)")
    else:
        raise ValueError("PI_LAYOUT_UNKNOWN")
    token = hashlib.sha256(json.dumps(["fee-consent", layout, max_account_fee, fee_auth_until, verifier_version],
                                      separators=(",", ":")).encode()).hexdigest()
    return {"statement": statement, "token": token}


@dataclass(frozen=True)
class PlanChoice:
    """(31.2 rule 10 (f)): every PI value that is not read from the bound state or the derived key.

    DOMAIN_TAG and verifier_version come from the authenticated configuration of the chain and the named version;
    the layout, expiry, max_account_fee and the fee fields are the owner's choice (l. 417). validate_plan
    rebuilds the PI from the bound state, the plan's key and this choice and compares it byte for byte, so that
    no field rests on the in-memory checksum alone (WVP-07)."""
    domain_tag: bytes
    verifier_version: int
    expiry: int
    max_account_fee: int
    fee: FeeChoice = SELF_PAY

    def __post_init__(self):
        if not isinstance(self.domain_tag, bytes) or len(self.domain_tag) != 32:
            raise ValueError("DOMAIN_TAG must be the configured 32-byte value")
        for value, maximum, name in ((self.verifier_version, (1 << 32) - 1, "verifier_version"),
                                     (self.expiry, UINT64_MAX, "expiry"),
                                     (self.max_account_fee, (1 << 256) - 1, "max_account_fee")):
            if type(value) is not int or not 0 <= value <= maximum:
                raise ValueError(f"{name} is outside its range")
        if not isinstance(self.fee, FeeChoice):
            raise ValueError("FeeChoice required")


@dataclass(frozen=True)
class Sponsor:
    """(31.2 rule 10 (e); section 3.2.6, l. 283): the carrier's sponsor of a sponsored single 0x7e.

    A PQ account other than legacy_address that pays the gas and signs `sponsor_sig` over keccak256(0x7e ||
    canonical(tx without sponsor_sig)) in domain ETH-PQ-SPONSOR/v1; `valid_until` is its sponsor_valid_until,
    at most the PI's expiry (a decode rule, NON_CANONICAL_ENCODING). `sign(message, ctx)` is the sponsor's
    signer (the sponsor's key, never the owner's); `public_key`, when given, lets the adapter verify the
    signature before anything is recorded. The adapter builds the carrier; the sponsor only signs it."""
    address: str
    valid_until: int
    sign: object
    public_key: bytes | None = None

    def __post_init__(self):
        if not isinstance(self.address, str) or len(self.address.removeprefix("0x")) != 40:
            raise ValueError("sponsor address is a 20-byte address")
        object.__setattr__(self, "address", bytes.fromhex(self.address.removeprefix("0x")).hex())
        if type(self.valid_until) is not int or not 0 <= self.valid_until <= UINT64_MAX:
            raise ValueError("sponsor_valid_until is a u64")
        if not callable(self.sign):
            raise ValueError("the sponsor's signer is required")


@dataclass(frozen=True)
class RecoveryPlan:
    scope_key: str
    anchor: str
    key: KeyMaterial
    pi: bytes
    nonce: int
    pi_sha256: str
    requires_fresh_proof: bool = True
    same_key_recommit: bool = False
    choice: PlanChoice | None = None      # (31.2 rule 10 (e), (f)): what the PI's values were chosen from
    warnings: tuple = ()                   # what l. 252 and l. 417 say about the owner's explicit choice


def _scope_matches_seed(scope, seed64):
    if scope.seed_identity != local_seed_identity(seed64):
        raise ValueError("adapter requires the stable local identity of this seed")


def _require_tracker(store, tracker):
    if not isinstance(tracker, AuthorizationTracker):
        raise ValueError("AUTHORIZATION_TRACKER_REQUIRED")
    if tracker.directory.resolve() != store.directory.resolve():
        raise ValueError("TRACKER_SECURITY_STORE_MISMATCH")


def _above_bound(scope, state, current_key):
    """(31.2 rule 5): the current key of `state` that only MATCH_ABOVE_BOUND found (its epoch at or above the
    state's migration_nonce); such a key is used for the same-key writes of the range repair only."""
    return isinstance(current_key, CurrentKey) and current_key.above_bound(scope, state)


def _refuse_exposed_current_key(scope, state, store, tracker, current_key, *, repair=False):
    """D-1: a commitment-level exposure reaches the epoch ledger before any key use.

    31.2 rule 7 (b) and rule 9 ('known otherwise, in which case a wallet that keeps
    records adds it'): the verified epoch of an exposed current key is persisted,
    then the use is refused. The tracker must share the epoch store's directory.
    (31.2 rule 5): with `repair`, a key that only MATCH_ABOVE_BOUND found is verified too.
    """
    _require_tracker(store, tracker)
    if not isinstance(current_key, CurrentKey) or not (
            current_key.matches(scope, state) or (repair and _above_bound(scope, state, current_key))):
        raise ValueError("STALE_OR_UNVERIFIED_CURRENT_KEY")
    if tracker.link_current_key(scope, state.commitment, current_key.epoch):
        raise ValueError("CURRENT_KEY_COMPROMISED")


def _require_head_for_state(head, state):
    """The tracker's head is the bound block's own state (31.2 rule 1).

    A CanonicalState field that was not read (None) is not compared, except
    fork_time, whose None means that no release schedules T (l. 61).
    """
    if not isinstance(head, AccountState):
        raise ValueError("HEAD_ACCOUNT_STATE_REQUIRED")
    account = Account(state.chain_id, state.genesis_hash, state.legacy_address)
    if ((head.account, head.block_hash, head.migration_nonce, head.mode, head.activated,
         head.commitment, head.fork_time, head.protocol_time, head.legacy_seed_proof_from_t0,
         head.effective_code_kind)
            != (account, state.block_hash, state.migration_nonce, state.status, state.activated,
                state.commitment, state.fork_time, state.protocol_time, state.legacy_seed_proof_from_t0,
                state.effective_code_kind)):
        raise ValueError("HEAD_STATE_MISMATCH")
    for name in ("timestamp", "override_window", "enrolled_at"):
        value = getattr(state, name)
        if value is not None and value != getattr(head, name):
            raise ValueError("HEAD_STATE_MISMATCH")


def derive_key(scope: DerivationScope, seed64: bytes, epoch: int, crypto) -> KeyMaterial:
    _scope_matches_seed(scope, seed64)
    xi = derive_epoch_seed(seed64, "ML-DSA-44", scope.path, epoch)
    pk = crypto("pk", xi)
    if len(pk) != 1312:
        raise ValueError("ML-DSA-44 worker returned a wrong-length key")
    return KeyMaterial(epoch, xi, pk, crypto("hash", b"\x01" + pk))


def link_recorded_epochs(scope, seed64, crypto, store, tracker, *, epochs=()):
    """A record by epoch reaches every key it names.

    A record of 31.2 rule 7 names epochs, and a PI learned on chain carries no epoch, so
    the tracker alone cannot tell that the record covers it. For every recorded epoch, and
    every epoch in `epochs`, this derives C_e (ML-DSA-44, the scope's path) and links it to
    e in the tracker; an epoch that is already linked is not derived again. From then on
    every tracked authorization that commits C_e is exposed when e is recorded, whatever
    its carrier says. Returns the epochs linked by this call.
    """
    _scope_matches_seed(scope, seed64)
    _require_tracker(store, tracker)
    wanted = set(store.security(scope).compromised_epochs)
    for epoch in epochs:
        if type(epoch) is not int or not 0 <= epoch <= UINT32_MAX:
            raise ValueError("epoch is outside its unsigned range")
        wanted.add(epoch)
    linked = []
    for epoch in sorted(wanted - tracker.linked_epochs(scope)):
        key = derive_key(scope, seed64, epoch, crypto)
        tracker.link_key(scope, key.commitment, epoch,
                         reason="key of a recorded or derived epoch whose commitment is known exposed")
        linked.append(epoch)
    return linked


def observe_head(scope, seed64, crypto, store, tracker, head, *, inclusions=(), current_epoch=None):
    """Observe a head through the adapter: link the recorded epochs first, then let the tracker offer.

    observe_head's offers then see an authorization learned
    without its epoch whose key a record names by epoch. Epoch 0 and the epoch of the
    head's migration_nonce are linked too (the keys that a 0x7d and a write at the current nonce
    commit, 31.2 rule 2), so that the tracker knows the key of a fresh precursor.
    """
    link_recorded_epochs(scope, seed64, crypto, store, tracker,
                         epochs=(0,) + ((head.migration_nonce,) if head.migration_nonce <= UINT32_MAX else ()))
    return tracker.observe_head(scope, head, inclusions=inclusions, current_epoch=current_epoch)


def observe_finalized(scope, seed64, crypto, store, tracker, view):
    """Observe a chain-finalized state through the adapter.

    A seed-derived 0x7d commits C_0 (31.2 rule 2 at m = 0), so the adapter links epoch 0
    and every recorded epoch before the tracker judges whether F's PQ_BY_ENROLL commitment
    is one that the device did not create (spec 34.2 rule 2).
    """
    link_recorded_epochs(scope, seed64, crypto, store, tracker, epochs=(0,))
    return tracker.observe_finalized(scope, view)


def learn_authorization(scope, seed64, crypto, store, tracker, auth, carrier, *, custody="IN_BLOCK"):
    """Track a binding authorization learned on chain (32.2 rule 1), with the epoch 31.2 rule 2 gives it.

    A PI that commits a new seed-derived key at migration nonce m
    was selected at e = m, and a 0x7d at e = 0 (it applies only from LEGACY, m = 0). The
    adapter derives C_e and, where the commitment matches, records the authorization with
    e. Otherwise (a same-key write, a rotate, a key of another path or algorithm) it is
    recorded as it is, and the commitments that link_recorded_epochs derives still bring a
    record by epoch to it. Learned on chain, its carrier is in a block (custody
    IN_BLOCK, one that A holds, 34.2 rule 1 (g)); a caller that learned it from a pool says so.
    """
    if not isinstance(auth, Authorization):
        raise ValueError("authorization required")
    link_recorded_epochs(scope, seed64, crypto, store, tracker)
    if auth.epoch is None and auth.kind in ("PI", "ENROLL"):
        epoch = auth.nonce if auth.kind == "PI" else 0
        if epoch <= UINT32_MAX and derive_key(scope, seed64, epoch, crypto).commitment == auth.commitment:
            auth = replace(auth, epoch=epoch)
    return tracker.record(scope, auth, carrier, custody=custody)


def _others_can_send_from_a(scope, state, seed64, crypto, tracker, gate):
    """(l. 252, l. 417): whether another party can originate a 0x7c of `a` before an override lands.

    In the override case the enrolled key's holder can activate it and sweep the balance unless the enrolled
    key is the owner's own seed key (C_0, the key that a seed-derived 0x7d commits, 31.2 rule 2, or a key that the
    device links to an epoch) and is not known exposed. Only the override case asks (l. 417 names own ETH 'in the
    frozen and re-commit cases' without condition)."""
    if gate != "OVERRIDE":
        return False
    c = state.commitment
    own = c == derive_key(scope, seed64, 0, crypto).commitment or tracker.own_commitment(scope, c)
    return not own or tracker.key_exposed(scope, c)


OWN_FUNDS_WARNING = ("OWN_FUNDS_WHERE_ANOTHER_PARTY_CAN_SEND_FROM_A: the enrolled key's holder can sweep the balance "
                     "before the override block, and the self-paid carrier then fails (l. 252, l. 417); the owner "
                     "chose own funds explicitly")


def own_funds_warning(*, legacy_address, max_account_fee, verifier_version):
    """(spec 38.3 rule 1, S-12; l. 252, l. 417): the warning that the wallet displays before it prepares an
    override that `a` pays in the override of an enrollment whose key another party holds, and its token.

    Such an override is prepared only where the wallet has no sponsored path to offer, and only on the owner's explicit
    choice after this warning: the holder of the enrolled key can activate it and take a's balance before the override
    lands, which makes the override fail (check 7, INSUFFICIENT_FEE_BALANCE) and costs a new proof while deadline(a)
    runs (l. 252). The caller shows `statement` and passes `token` as confirm_own_funds only after the owner confirmed
    it; a token binds the account, the cap and the version."""
    for value, maximum, name in ((max_account_fee, (1 << 256) - 1, "max_account_fee"),
                                 (verifier_version, (1 << 32) - 1, "verifier_version")):
        if type(value) is not int or not 0 <= value <= maximum:
            raise ValueError(f"{name} is outside its range")
    address = bytes.fromhex(legacy_address.removeprefix("0x")).hex()
    statement = (f"OWN FUNDS IN THE OVERRIDE OF AN ENROLLMENT WHOSE KEY ANOTHER PARTY HOLDS (account {address}): the holder "
                 "of the enrolled key can activate it and take the account's balance before the override lands; the "
                 f"override, which may take up to {max_account_fee} wei, then fails (check 7) and needs a new proof while "
                 "the override window runs (l. 252, l. 417); offered only because the wallet has no sponsored path "
                 "(spec 38.3 rule 1)")
    token = hashlib.sha256(json.dumps(["own-funds-warning", address, max_account_fee, verifier_version],
                                      separators=(",", ":")).encode()).hexdigest()
    return {"statement": statement, "token": token}


def _resolve_fee(fee, others_can_send, *, no_sponsored_path=False, confirmed=None, token=None):
    """(31.2 rule 10 (e); l. 252, l. 417): the owner's FeeChoice, or the self-pay choice where it is one.

    fee None is no choice: the wallet then proves mode 0 under layout 2 (an owner who funds the migration from
    legacy_address proves mode 0 and submits it unsponsored, l. 417; the first production activation enables
    layout-2 versions only, section 19.2 rule 5), except where another party can send from `a` before the
    override lands: there own ETH is not the wallet's fee path (l. 252: 'then use a sponsor and a private relay';
    l. 417), so it refuses FEE_CHOICE_REQUIRED and the owner chooses.
    (spec 38.3 rule 1, S-12): an explicit own-funds choice there is taken only where the wallet has no
    sponsored path to offer (`no_sponsored_path`, the caller's statement) and only after the displayed warning
    (`confirmed` equal to own_funds_warning's `token`)."""
    if fee is None:
        if others_can_send:
            raise ValueError("FEE_CHOICE_REQUIRED: in the override case of an enrolled key that another party holds, its "
                             "holder can originate a 0x7c and sweep the balance before the override block, so own ETH "
                             "is not the wallet's fee path; choose a sponsored fee mode (1, 2, or 3 with the displayed "
                             "consent) and submit through a sponsor and a private relay (l. 252, l. 417; section 19.2)")
        return SELF_PAY, ()
    if not isinstance(fee, FeeChoice):
        raise ValueError("FeeChoice required")
    if type(no_sponsored_path) is not bool:
        raise ValueError("no_sponsored_path must be boolean")
    if others_can_send and not fee.is_sponsored:
        if not no_sponsored_path:
            raise ValueError("OWN_FUNDS_WHILE_A_SPONSORED_PATH_EXISTS: in the override of an enrollment whose key another "
                             "party holds, an override that a pays is prepared only where the wallet has no sponsored "
                             "path to offer (no_sponsored_path=True); otherwise the fee path is a sponsor or an aggregator "
                             "with a private relay (l. 252, l. 417; spec 38.3 rule 1)")
        if token is None or confirmed != token:
            raise ValueError("OWN_FUNDS_NEEDS_THE_DISPLAYED_WARNING: the wallet shows own_funds_warning() and prepares the "
                             "override that a pays only on the owner's explicit choice after it (confirm_own_funds; l. 252, "
                             "l. 417; spec 38.3 rule 1)")
        return fee, (OWN_FUNDS_WARNING,)
    return fee, ()


def _check_fee_choice(choice, state):
    """(31.2 rule 10 (e)): the canonical constraints of section 19.2 that depend on the expiry and the
    account, and the rules of l. 417 on the owner's choice."""
    fee = choice.fee
    if fee.layout == 1:
        token = fee_consent(layout=1, max_account_fee=choice.max_account_fee,
                            verifier_version=choice.verifier_version)["token"]
        if fee.consent != token:
            raise ValueError("LAYOUT_1_BOUNTY_NEEDS_THE_OWNERS_CONSENT: under a layout-1 version any sponsor may collect "
                             "up to max_account_fee wherever a 0x7f of the version can carry the proof; the wallet names "
                             "the carriers and obtains the owner's consent first (l. 417; section 18.24; fee_consent())")
        return
    if fee.fee_mode in (1, 3) and fee.fee_auth_until > choice.expiry:
        raise ValueError("NON_CANONICAL_ENCODING: fee_auth_until <= expiry for modes 1 and 3 (section 19.2)")
    if fee.fee_mode == 1 and fee.fee_sponsor == state.legacy_address:
        raise ValueError("FEE_SPONSOR_IS_LEGACY_ADDRESS: the wallet never names legacy_address as fee_sponsor; such a "
                         "mode-1 proof can never be reimbursed (l. 417)")
    if fee.fee_mode == 3:
        token = fee_consent(layout=2, max_account_fee=choice.max_account_fee, verifier_version=choice.verifier_version,
                            fee_auth_until=fee.fee_auth_until)["token"]
        if fee.consent != token:
            raise ValueError("FEE_MODE_3_NEEDS_THE_OWNERS_DISPLAYED_CONSENT: mode 3 is a public bounty, never a default "
                             "and never selected without a displayed consent naming the cap and fee_auth_until "
                             "(l. 417; section 19.2; fee_consent())")


def _require_expiry_after_the_head(expiry, state, slot):
    """Check 4 (l. 259) at the earliest block after B (l. 1230): a PI whose expiry is below B.timestamp + SLOT can
    never be included (PROOF_EXPIRED)."""
    if state.timestamp is not None and expiry < state.timestamp + slot:
        raise ValueError("PLANNED_WRITE_EXPIRES_BEFORE_ITS_BLOCK: the PI's expiry is below B.timestamp + SLOT, the "
                         "earliest timestamp of a block after B (check 4, l. 259; l. 1230)")


def prepare_recovery(scope, state, store, seed64, crypto, *, tracker, domain_tag,
                     verifier_version, expiry, max_account_fee, fee=None, no_sponsored_path=False,
                     confirm_own_funds=None):
    """Prepare a statement in the layout of the named version; no receipt/proof is fabricated.

    Rule 10 (c): a gate of check 5 must be open at the bound state (pre-T LEGACY,
    frozen, override or re-commit; check5_gate), else the check-5 code is raised.
    The tracker is required, with the directory check of the
    signers; the recorded epochs are linked first, and a selected key whose commitment is
    known exposed is refused (EPOCH_COMPROMISED) after its epoch is persisted.
    (31.2 rule 10 (e)): the fee fields come from the owner's choice (`fee`, a FeeChoice; l. 417):
    the PI follows the layout of the named version (169 bytes under layout 1, 198 under layout 2) and, under
    layout 2, carries the owner's fee_mode, fee_sponsor and fee_auth_until; mode 3 and a layout-1 bounty need the
    owner's displayed consent (fee_consent()). fee None is the self-pay choice (mode 0, layout 2) where own ETH is a
    fee path of l. 417 and is refused (FEE_CHOICE_REQUIRED) in the override case of an enrolled key that another
    party holds (l. 252). The authenticated domain/version configuration remains
    the existing client's responsibility. Re-read state and call validate_plan immediately before use.
    An explicit own-funds choice needs `no_sponsored_path=True` (the caller's statement that the wallet
    has no sponsored path to offer) and `confirm_own_funds`, the token of own_funds_warning() that the owner confirmed
    (spec 38.3 rule 1); and no new key is selected while a current key that only MATCH_ABOVE_BOUND found awaits
    the range repair of 31.2 rule 5 (CURRENT_KEY_ABOVE_U_SAME_KEY_REPAIR_BEFORE_ANY_NEW_SELECTION).
    """
    _require_tracker(store, tracker)
    gate, reason = check5_gate(state)
    if gate is None:
        raise ValueError(reason)
    link_recorded_epochs(scope, seed64, crypto, store, tracker)
    selection = select_new_key_epoch(scope, state, store)
    if selection.status != "SELECTED":
        raise ValueError(selection.reason)
    key = derive_key(scope, seed64, selection.epoch, crypto)
    if tracker.link_key(scope, key.commitment, key.epoch,
                        reason="selected key whose commitment is known exposed"):
        raise ValueError("EPOCH_COMPROMISED")
    fee, warnings = _resolve_fee(fee, _others_can_send_from_a(scope, state, seed64, crypto, tracker, gate),
                                 no_sponsored_path=no_sponsored_path, confirmed=confirm_own_funds,
                                 token=own_funds_warning(legacy_address=state.legacy_address,
                                                         max_account_fee=max_account_fee,
                                                         verifier_version=verifier_version)["token"])
    choice = PlanChoice(domain_tag, verifier_version, expiry, max_account_fee, fee)
    _check_fee_choice(choice, state)
    _require_expiry_after_the_head(expiry, state, tracker.slot)
    pi = _pi(state, key, domain_tag, verifier_version, expiry, max_account_fee, fee)
    return RecoveryPlan(scope.key, state.anchor, key, pi, state.migration_nonce,
                        hashlib.sha256(pi).hexdigest(), choice=choice, warnings=warnings)


# The fields of PI_bytes (16.3; under layout 2 the three fee fields of section 19.2 follow at 169-197).
PI_FIELDS = (("chain_id", 0, 32), ("DOMAIN_TAG", 32, 64), ("legacy_address", 64, 84), ("migration_nonce", 84, 92),
             ("alg_id", 92, 93), ("pq_pk_commit", 93, 125), ("verifier_version", 125, 129), ("expiry", 129, 137),
             ("max_account_fee", 137, 169), ("fee_mode", 169, 170), ("fee_sponsor", 170, 190),
             ("fee_auth_until", 190, 198))


def _pi(state, key, domain_tag, verifier_version, expiry, max_account_fee, fee=SELF_PAY, *, migration_nonce=None):
    """The complete PI of a write of `key` (a KeyMaterial or a commitment) in the layout of the named version.

    The nine layout-1 fields of 16.3 (169 bytes) and, under layout 2, fee_mode, fee_sponsor and fee_auth_until
    (198 bytes; section 19.2). (31.2 rule 10 (e)): the fee fields come from the owner's FeeChoice (an
    int is a layout-2 fee mode). `migration_nonce` defaults to B's.
    """
    if not isinstance(domain_tag, bytes) or len(domain_tag) != 32:
        raise ValueError("DOMAIN_TAG must be the configured 32-byte value")
    if isinstance(fee, int):
        fee = FeeChoice(fee_mode=fee)
    m = state.migration_nonce if migration_nonce is None else migration_nonce
    commitment = key.commitment if isinstance(key, KeyMaterial) else key
    pi = (state.chain_id.to_bytes(32, "big") + domain_tag
          + bytes.fromhex(state.legacy_address) + m.to_bytes(8, "big")
          + b"\x01" + commitment + verifier_version.to_bytes(4, "big")
          + expiry.to_bytes(8, "big") + max_account_fee.to_bytes(32, "big")
          + fee.tail())
    if len(pi) != PI_LAYOUT_BYTES[fee.layout]:
        raise ValueError("expected complete public inputs of the named layout")
    return pi


def prepare_recommit(scope, state, store, current_key, seed64, crypto, *, tracker,
                     domain_tag, verifier_version, expiry, max_account_fee,
                     confirm_extra_proof_and_fee, fee=None):
    """Prepare the explicitly accepted extra step, never send or advance state.

    D-1: the tracker is consulted first; a current key whose commitment is known
    exposed is refused (CURRENT_KEY_COMPROMISED) after its epoch is persisted.
    The recorded epochs are linked first.
    (31.2 rule 10 (d), (e)): the 0x7e same-key step through every gate that 31.2 rule 8 (a) names: the
    re-commit gate, and the override gate of the owner's own seed-derived enrolled key (the same-key early
    finalisation of l. 327); a binding-final account takes the rotate of prepare_same_key_rotate instead. The fee
    fields come from the owner's FeeChoice as in prepare_recovery.
    (31.2 rule 5): a current key that only MATCH_ABOVE_BOUND finds (from scan_above_bound) takes the same step
    as one of the range repair's e - migration_nonce + 1 writes (the selection's OFFER_RANGE_REPAIR), whether or not the
    epoch at the current nonce is recorded; the key keeps its epoch e.
    """
    link_recorded_epochs(scope, seed64, crypto, store, tracker)
    repair = _above_bound(scope, state, current_key)
    _refuse_exposed_current_key(scope, state, store, tracker, current_key, repair=repair)
    if confirm_extra_proof_and_fee is not True:
        raise ValueError("explicit approval of the extra proof and fee is required")
    selected = select_new_key_epoch(scope, state, store, current_key=current_key)
    if selected.status not in ("OFFER_SAME_KEY_RECOMMIT", "OFFER_RANGE_REPAIR") \
            or not set(selected.steps) & set(WRITE_STEP_FORMS):
        raise ValueError("SAFE_SAME_KEY_ADVANCEMENT_UNAVAILABLE" + (
            ": the same-key step here is a rotate to the current key (prepare_same_key_rotate; 31.2 rule 8 (a))"
            if selected.status in ("OFFER_SAME_KEY_ROTATE", "OFFER_RANGE_REPAIR") else ""))
    decision = revalidate_key_use(scope, state, store, current_key, for_range_repair=repair)
    if not decision.allowed:
        raise ValueError(decision.reason)
    key = derive_key(scope, seed64, current_key.epoch, crypto)
    if key.commitment != state.commitment:
        raise ValueError("current key does not match the state commitment")
    gate, _ = check5_gate(state)
    fee, warnings = _resolve_fee(fee, _others_can_send_from_a(scope, state, seed64, crypto, tracker, gate))
    choice = PlanChoice(domain_tag, verifier_version, expiry, max_account_fee, fee)
    _check_fee_choice(choice, state)
    _require_expiry_after_the_head(expiry, state, tracker.slot)
    pi = _pi(state, key, domain_tag, verifier_version, expiry, max_account_fee, fee)
    return RecoveryPlan(scope.key, state.anchor, key, pi, state.migration_nonce,
                        hashlib.sha256(pi).hexdigest(),
                        same_key_recommit=True, choice=choice, warnings=warnings)


def validate_plan(plan, scope, state, store, tracker=None, *, choice=None, seed64=None, crypto=None):
    """Revalidate a plan at fresh state.

    With a tracker, a same-key plan also passes D-1's gate, and a new-key plan's key is linked to its epoch first, so that a
    commitment-level exposure persists that epoch and the plan is refused.
    (31.2 rule 10 (f)): every PI field is checked against the bound state and the owner's choice: the PI
    is rebuilt from B's chain_id, legacy_address and migration_nonce, the plan's key, and the PlanChoice (DOMAIN_TAG
    and verifier_version of the configuration; the layout, expiry, max_account_fee and fee fields of the owner's
    choice), and compared byte for byte; the first differing field is named. `choice`, the caller's own record of
    the owner's choice, must equal the plan's; with `seed64` and `crypto` the plan's key is derived again. The
    choice's constraints (section 19.2; l. 417) and check 4 at B.timestamp + SLOT are checked again. (31.2
    rule 10 (d)): a same-key plan is valid in every gate for which the selection offers a 0x7e same-key step (the
    re-commit gate, and the override gate of the owner's own enrolled key).
    """
    if plan.scope_key != scope.key or plan.anchor != state.anchor:
        raise ValueError("STALE_RECOVERY_PLAN")
    gate, reason = check5_gate(state)
    if gate is None:
        raise ValueError("STATE_GATE_CLOSED: " + reason)
    if plan.same_key_recommit and gate not in ("RECOMMIT", "OVERRIDE"):
        raise ValueError("STATE_GATE_CLOSED: SAME_KEY_PLAN_NEEDS_A_WRITE_GATE")
    # This checksum detects accidental editing of an in-memory plan; it is not
    # an authorization signature. Serialized untrusted plans are not accepted
    # as user consent. Every field is also rebuilt from its source below.
    pi = plan.pi
    if (len(pi) not in PI_LAYOUT_BYTES.values() or hashlib.sha256(pi).hexdigest() != plan.pi_sha256
            or plan.nonce != state.migration_nonce
            or (not plan.same_key_recommit and plan.key.epoch != state.migration_nonce)):
        raise ValueError("RECOVERY_PLAN_BINDING_MISMATCH")
    if not isinstance(plan.choice, PlanChoice):
        raise ValueError("RECOVERY_PLAN_BINDING_MISMATCH: the plan names no owner's choice (31.2 rule 10 (f))")
    if choice is not None and choice != plan.choice:
        raise ValueError("RECOVERY_PLAN_CHOICE_MISMATCH: the plan was prepared for another choice than the owner's "
                         "(31.2 rule 10 (f))")
    chosen = plan.choice
    _check_fee_choice(chosen, state)
    expected = _pi(state, plan.key, chosen.domain_tag, chosen.verifier_version, chosen.expiry, chosen.max_account_fee,
                   chosen.fee)
    if pi != expected:
        if len(pi) != len(expected):
            raise ValueError(f"RECOVERY_PLAN_BINDING_MISMATCH: PI_LAYOUT ({len(pi)} bytes, the named layout has "
                             f"{len(expected)}; section 19.2)")
        field = next(name for name, a, b in PI_FIELDS if pi[a:b] != expected[a:b])
        raise ValueError(f"RECOVERY_PLAN_BINDING_MISMATCH: {field} differs from the bound state and the owner's choice "
                         "(31.2 rule 10 (f))")
    _require_expiry_after_the_head(chosen.expiry, state, SLOT if tracker is None else tracker.slot)
    if seed64 is not None:
        if derive_key(scope, seed64, plan.key.epoch, crypto).commitment != plan.key.commitment:
            raise ValueError("RECOVERY_PLAN_BINDING_MISMATCH: pq_pk_commit is not the key of the plan's epoch")
    if plan.same_key_recommit:
        current = CurrentKey(scope.key, state.anchor, plan.key.epoch, plan.key.commitment)
        repair = _above_bound(scope, state, current)      # a step of the range repair of 31.2 rule 5
        if tracker is not None:
            _refuse_exposed_current_key(scope, state, store, tracker, current, repair=repair)
        selected = select_new_key_epoch(scope, state, store, current_key=current)
        if (selected.status not in ("OFFER_SAME_KEY_RECOMMIT", "OFFER_RANGE_REPAIR")
                or not set(selected.steps) & set(WRITE_STEP_FORMS)
                or not revalidate_key_use(scope, state, store, current, for_range_repair=repair).allowed):
            raise ValueError("RECOMMIT_PLAN_NO_LONGER_SAFE")
        return True
    if tracker is not None:
        _require_tracker(store, tracker)
        if tracker.link_key(scope, plan.key.commitment, plan.key.epoch,
                            reason="planned key whose commitment is known exposed"):
            raise ValueError("RECOVERY_PLAN_NO_LONGER_SAFE")
    selected = select_new_key_epoch(scope, state, store)
    if selected.status != "SELECTED" or selected.epoch != plan.key.epoch:
        raise ValueError("RECOVERY_PLAN_NO_LONGER_SAFE")
    return True


def _fee_fields(config):
    fee_fields = [config["max_priority_fee_per_gas"], config["max_fee_per_gas"], config["migration_gas_limit"]]
    if any(type(n) is not int or not 0 <= n < (1 << 256) for n in fee_fields):
        raise ValueError("invalid fee/gas configuration")
    return fee_fields


def _encode_0x7e(state, nonce, pi, proof, config, fee, *, sponsor=None, crypto=None):
    """The Route A single 0x7e of `pi` in its layout (16.4; the layout-2 wire form of section 19.2).

    Unsponsored (sponsor_option []) for a mode-0 PI or a layout-1 choice that is not sponsored: check 7 (l. 266)
    needs gas_limit x max_fee <= max_account_fee (FEE_CAP_EXCEEDED otherwise). Sponsored for modes 1-3 or a
    sponsored layout-1 choice (31.2 rule 10 (e)): the adapter builds the carrier, [sponsor,
    sponsor_valid_until, sponsor_sig], with sponsor != legacy_address and sponsor_valid_until <= expiry (decode
    rules, 16.4, 3.2.6), and the sponsor signs keccak256(0x7e || canonical(tx without sponsor_sig)) in domain
    ETH-PQ-SPONSOR/v1 (16.4 signing preimages; `crypto("hash")` is the helper's keccak256). A layout-2 PI of mode 0
    on a sponsored carrier, or of mode 1-3 on an unsponsored one, is rejected (section 19.2 table)."""
    layout = 1 if len(pi) == 169 else 2
    if len(pi) != PI_LAYOUT_BYTES[layout] or fee.layout != layout:
        raise ValueError("PI_LAYOUT_MISMATCH: the carrier follows the layout of the PI's named version (section 19.2)")
    fee_fields = _fee_fields(config)
    expiry, cap = int.from_bytes(pi[129:137], "big"), int.from_bytes(pi[137:169], "big")
    tree = [state.chain_id, bytes.fromhex(state.legacy_address), nonce, pi[92], pi[93:125], expiry, cap]
    if layout == 2:
        tree += [pi[169], pi[170:190], int.from_bytes(pi[190:198], "big")]
    option = len(tree) + 3
    tree += [*fee_fields, [], int.from_bytes(pi[125:129], "big"), [0, proof], []]
    if not fee.is_sponsored:
        if fee_fields[2] * fee_fields[1] > cap:
            raise ValueError("FEE_CAP_EXCEEDED: an unsponsored 0x7e needs gas_limit x max_fee <= max_account_fee "
                             "(check 7, l. 266)")
        return b"\x7e" + wire.rlp(tree)
    if not isinstance(sponsor, Sponsor):
        raise ValueError("SPONSOR_REQUIRED: a PI of a sponsored fee mode is carried only by a sponsored carrier "
                         "(section 19.2 table); the adapter builds it with the sponsor's signature (Sponsor)")
    if sponsor.address == state.legacy_address:
        raise ValueError("NON_CANONICAL_ENCODING: a sponsored 0x7e's sponsor is never legacy_address (3.2.6, l. 283)")
    if sponsor.valid_until > expiry:
        raise ValueError("NON_CANONICAL_ENCODING: sponsor_valid_until <= expiry on a sponsored 0x7e (16.4)")
    tree[option] = [bytes.fromhex(sponsor.address), sponsor.valid_until, b""]
    ctx = b"ETH-PQ-SPONSOR/v1"
    message = ctx + crypto("hash", b"\x7e" + wire.rlp(tree))
    signature = sponsor.sign(message, ctx)
    if not isinstance(signature, bytes) or not signature:
        raise ValueError("the sponsor's signer returned no signature")
    if sponsor.public_key is not None and crypto.text("verify", sponsor.public_key, message, ctx, signature) != "true":
        raise ValueError("SPONSOR_SIGNATURE_INVALID: the sponsor's signature does not verify (BAD_SPONSOR_SIG)")
    tree[option][2] = signature
    return b"\x7e" + wire.rlp(tree)


def _verified_carrier(plan, scope, state, store, tracker, *, head, proof, journal, config,
                      verify_proof, seed64, crypto, sponsor=None, choice=None):
    """Check the plan and the proof, then encode the 0x7e of the plan's layout and fee mode; returns (raw, auth).

    (31.2 rule 10 (e), (f)): validate_plan checks every PI field against the bound state and the owner's
    choice (`choice`, when the caller passes its own record) and derives the key again; a configuration that names
    the version's layout (`pi_layout`) must agree with the PI; a sponsored PI is carried by the sponsored 0x7e that
    the adapter builds with `sponsor`."""
    _require_tracker(store, tracker)
    _require_head_for_state(head, state)
    link_recorded_epochs(scope, seed64, crypto, store, tracker)
    validate_plan(plan, scope, state, store, tracker, choice=choice, seed64=seed64, crypto=crypto)
    if not isinstance(proof, bytes) or not proof or journal != plan.pi:
        raise ValueError("PROOF_JOURNAL_BINDING_MISMATCH")
    if (config["chain_id"] != state.chain_id
            or bytes.fromhex(config["domain_tag"].removeprefix("0x")) != plan.pi[32:64]
            or config["verifier_version"] != int.from_bytes(plan.pi[125:129], "big")
            or config.get("pi_layout", plan.choice.fee.layout) != plan.choice.fee.layout):
        raise ValueError("STALE_PROOF_CONFIGURATION")
    if not callable(verify_proof):
        raise ValueError("verification and delivery callbacks required")
    if verify_proof(proof, plan.pi) is not True:
        raise ValueError("INVALID_PROOF")
    # Recheck after verification, which may take time or process notifications.
    validate_plan(plan, scope, state, store, tracker, choice=choice)
    raw = _encode_0x7e(state, plan.nonce, plan.pi, proof, config, plan.choice.fee, sponsor=sponsor, crypto=crypto)
    account = Account(state.chain_id, state.genesis_hash, state.legacy_address)
    return raw, Authorization.from_pi(account, plan.pi, epoch=plan.key.epoch)


def export_recovery(plan, scope, state, store, tracker, *, head, proof, journal,
                    config, verify_proof, deliver, seed64, crypto, confirm_revival=None,
                    no_one_payload_path=False, sponsor=None, choice=None):
    """Verify and encode the 0x7e of the plan's layout and fee mode, check revival, persist, then deliver.

    verify_proof must perform LOCAL IN-PROCESS complete backend verification at
    its fixed STARK verifier key/parameters and bind the expected PI198 journal;
    no placeholder proof or truthy substitute is accepted here. The callback itself is trusted
    application code and must not transmit proof/PI elsewhere. This helper is
    not an implementation of that verifier.
    `head` is the tracker's AccountState of the bound block, already observed by
    tracker.observe_head. seed64 and crypto let the adapter link every
    recorded epoch to its commitment before the tracker decides whether export is safe.
    D-2: the tracker refuses the write when it would make a tracked exposed
    authorization includable (RevivalWarning). Where the remedy is not a bundle, the
    warning's token, passed as confirm_revival after the owner's explicit confirmation,
    delivers it alone; where it is ONE_PAYLOAD_BUNDLE, prepare_recovery_bundle builds the
    remedy, and the write leaves alone only with no_one_payload_path=True and the token
    of the warning that states the gap (spec 34.2 rule 1 (c)).
    The caller refreshes canonical state/config and serializes signing/export
    with compromise notifications, as for the other adapter entry points.
    (31.2 rule 10 (e), (f)): the carrier follows the plan's layout and fee mode (a sponsored PI goes in the
    sponsored 0x7e that the adapter builds with `sponsor`), and `choice`, the caller's record of the owner's choice,
    is compared with the plan's at every validation.
    """
    if not callable(deliver):
        raise ValueError("verification and delivery callbacks required")
    raw, auth = _verified_carrier(plan, scope, state, store, tracker, head=head, proof=proof,
                                  journal=journal, config=config, verify_proof=verify_proof,
                                  seed64=seed64, crypto=crypto, sponsor=sponsor, choice=choice)

    # The registered bytes include the proof. xi / local identifiers are absent.
    def after_record(carrier):
        # Recording may link a previously exposed commitment to its newly
        # learned epoch. Respect that newly persisted ban before bytes leave.
        validate_plan(plan, scope, state, store, tracker, choice=choice)
        return deliver(carrier)

    return tracker.export(scope, auth, raw, after_record, head=head, confirm_revival=confirm_revival,
                          no_one_payload_path=no_one_payload_path)


def _signing_record(key):
    # The existing helper's historical field name is public_test_seed. It remains
    # in memory here and is not included in the returned transaction description.
    return {"public_test_seed": key.xi.hex(), "public_key": key.public_key.hex()}


SPONSORED_ACT_ROUTE = ("the act is sponsored writes past PI.migration_nonce (34.2 rule 1 (f)): plan them with "
                       "plan_payload (acts_from_offer maps the offer's plan to its acts) and let build_payload build "
                       "the sponsored carriers with the sponsor's signature (build_payload(..., sponsor=...); 31.2 rule "
                       "10 (e))")


def prepare_recovery_bundle(plan, scope, state, store, tracker, *, head, proof, journal, config,
                            verify_proof, seed64, crypto, activation_config, fee_path=None,
                            through_account_nonce=None, balance_covers_acts=False, sponsor=None, choice=None):
    """Prepare the migration write and its required follow-up acts as one payload.

    Verify the proof against the expected journal and validate the bound plan,
    then encode its fee mode and sponsor choice. Sign follow-up activation or
    account-nonce-consuming transactions with the resulting current key. The
    tracker checks the complete ordered payload against every reachable tracked
    authorization before returning it; this function does not deliver anything.

    Section 34.2 requires the payload to make the relevant exposed authorization
    unusable and discharge authorizations its precursor revives. Fresh precursors
    may be held back, and a preemptible activation may require sponsored writes
    past the proof's migration nonce instead. The caller must truthfully state
    whether the account balance covers the follow-up acts. The returned bundle
    is revalidated at the observed head by tracker.export_bundle before delivery.
    """
    if type(balance_covers_acts) is not bool:
        raise ValueError("balance_covers_acts must be boolean")
    raw, auth = _verified_carrier(plan, scope, state, store, tracker, head=head, proof=proof,
                                  journal=journal, config=config, verify_proof=verify_proof,
                                  seed64=seed64, crypto=crypto, sponsor=sponsor, choice=choice)
    key = derive_key(scope, seed64, plan.key.epoch, crypto)
    if key.commitment != plan.key.commitment:
        raise ValueError("derived key does not match the planned key")
    if tracker.link_key(scope, key.commitment, key.epoch, reason="planned key whose commitment is known exposed") \
            or key.epoch in store.security(scope).compromised_epochs:
        raise ValueError("CURRENT_KEY_COMPROMISED")
    if activation_config["chain_id"] != state.chain_id:
        raise ValueError("activation chain differs from canonical state")
    n = head.account_nonce
    address = bytes.fromhex(state.legacy_address)
    record = _signing_record(key)
    activation, _ = wire.signed_pq(crypto, activation_config, address, record, n, 0, True)
    elements = [PayloadElement("WRITE", raw, authorization=auth, sponsored=plan.choice.fee.is_sponsored),
                PayloadElement("ACTIVATION", activation, commitment=key.commitment, account_nonce=n)]
    bundle = OnePayloadBundle(head, tuple(elements), fee_path=fee_path)
    if through_account_nonce is None:
        through_account_nonce = tracker.rotate_acts_needed(scope, bundle, balance_covers_acts=balance_covers_acts)
    if through_account_nonce is not None:
        if type(through_account_nonce) is not int or not n < through_account_nonce <= n + 64:
            raise ValueError("through_account_nonce must lie above the head's account nonce (at most 64 ahead)")
        for nonce in range(n + 1, through_account_nonce + 1):
            transaction, _ = wire.signed_pq(crypto, activation_config, address, record, nonce, 0, False)
            elements.append(PayloadElement("TRANSACTION", transaction, commitment=key.commitment, account_nonce=nonce))
        bundle = OnePayloadBundle(head, tuple(elements), fee_path=fee_path)
    try:
        tracker.bundle_preview(scope, bundle, balance_covers_acts=balance_covers_acts)
    except ValueError as exc:
        if str(exc).startswith("BUNDLE_ACT_PREEMPTIBLE"):
            raise ValueError(f"{exc}; {SPONSORED_ACT_ROUTE}") from exc
        raise
    return bundle


def _activation_key(scope, state, store, current_key, seed64, crypto, config, tracker):
    if state.alg_id != 1 or state.alg_name != "ML-DSA-44":
        raise ValueError("adapter supports ML-DSA-44 only")
    if state.status != "PQ_BY_PROOF" or state.activated:
        raise ValueError("activation adapter requires unactivated proof binding")
    link_recorded_epochs(scope, seed64, crypto, store, tracker)
    _refuse_exposed_current_key(scope, state, store, tracker, current_key)
    decision = revalidate_key_use(scope, state, store, current_key)
    if not decision.allowed:
        raise ValueError(decision.reason)
    key = derive_key(scope, seed64, current_key.epoch, crypto)
    if key.commitment != state.commitment:
        raise ValueError("derived key does not match the current binding")
    if config["chain_id"] != state.chain_id:
        raise ValueError("activation chain differs from canonical state")
    return key


def sign_activation(scope, state, store, current_key: CurrentKey, seed64,
                    crypto, config, *, tracker, head, transaction_nonce,
                    confirm_revival=None, no_one_payload_path=False):
    """Actual pure ML-DSA-44 signature using the existing 0x7c wire encoder.

    D-1: the tracker is consulted first; a current key whose commitment is known
    exposed is refused (CURRENT_KEY_COMPROMISED) after its epoch is persisted,
    as the epoch record already refuses (31.2 rule 7 (b)). `head` is the observed AccountState of the bound block,
    the activation is at its account nonce, and the tracker applies the revival
    check to the state after the activation (check_activation): where the activation
    would make a tracked exposed authorization includable, such as a non-activating
    rotate at the next account nonce, nothing is signed, and the remedy is the
    one-payload bundle of prepare_activation_bundle. The caller still provides the
    ordinary account nonce, canonical state, fork and fee configuration. This
    component is not a replacement for client validation.
    """
    key = _activation_key(scope, state, store, current_key, seed64, crypto, config, tracker)
    _require_head_for_state(head, state)
    if transaction_nonce != head.account_nonce:
        raise ValueError("ACTIVATION_NONCE_NOT_AT_HEAD")
    tracker.check_activation(scope, head, state.commitment, confirm_revival=confirm_revival,
                             no_one_payload_path=no_one_payload_path)
    raw, row = wire.signed_pq(crypto, config, bytes.fromhex(state.legacy_address),
                              _signing_record(key), transaction_nonce, 0, True)
    # (spec 34.2 rule 1 (a)): once it leaves, anyone who holds it can
    # include it again, so it is a member of K; recorded before the caller sends it.
    tracker.record_transaction(scope, Transaction(head.account, "ACTIVATION", transaction_nonce, state.commitment),
                               raw, custody="SIGNED")
    return raw, row


def prepare_activation_bundle(scope, state, store, current_key: CurrentKey, seed64, crypto,
                              config, *, tracker, head, through_account_nonce=None):
    """Bundle the activation with the transactions that make a tracked rotate stale.

    Signs the activation of the current key at the head's account nonce n, then ordinary
    0x7c transactions (value 0, to config's recipient) at n + 1, ..., k, where k is
    `through_account_nonce` or, by default, the highest account nonce of a tracked rotate
    with an exposed key that the activation alone would make includable (the
    RevivalWarning's payload names it). Returns OnePayloadBundle(head, [ACTIVATION,
    TRANSACTION, ...]) for tracker.export_bundle, which validates it again and delivers it
    whole; nothing is recorded or delivered here. The same checks as sign_activation apply
    except the revival check, which the bundle's own analysis replaces.
    The default `through_account_nonce` is the tracker's
    activation_acts_needed, the shortest extension with which the payload meets spec 34.2
    rule 1 (a) over K and O (the owner's transactions that have left a device included); where the
    lone activation meets it, this refuses with NO_ACTS_NEEDED (sign_activation signs it).
    """
    key = _activation_key(scope, state, store, current_key, seed64, crypto, config, tracker)
    _require_head_for_state(head, state)
    if through_account_nonce is None:
        through_account_nonce = tracker.activation_acts_needed(scope, head, state.commitment)
        if through_account_nonce is None:
            raise ValueError("NO_ACTS_NEEDED: the lone activation meets spec 34.2 rule 1 (a) over every "
                             "transaction of a that the device knows; sign_activation signs it")
    n = head.account_nonce
    if type(through_account_nonce) is not int or not n < through_account_nonce <= n + 64:
        raise ValueError("through_account_nonce must lie above the head's account nonce (at most 64 ahead)")
    record = _signing_record(key)
    address = bytes.fromhex(state.legacy_address)
    activation, _ = wire.signed_pq(crypto, config, address, record, n, 0, True)
    elements = [PayloadElement("ACTIVATION", activation, commitment=key.commitment, account_nonce=n)]
    for nonce in range(n + 1, through_account_nonce + 1):
        raw, _ = wire.signed_pq(crypto, config, address, record, nonce, 0, False)
        elements.append(PayloadElement("TRANSACTION", raw, commitment=key.commitment, account_nonce=nonce))
    return OnePayloadBundle(head, tuple(elements))


# ---------------------------------------------------------------------------------------------------------------
# (spec section 35.2, the payload plan, A-22-01; section 36.2, the selection after a same-key advance
# inside a payload, A-23-01).

PLAN_ACT_KINDS = ("WRITE_NEW_KEY", "WRITE_SAME_KEY", "ENROLL", "ACTIVATION", "TRANSACTION")


@dataclass(frozen=True)
class PlannedAct:
    """One act of a payload plan as an offer names it, before its values are taken from its planning state.

    WRITE_NEW_KEY: a 0x7e that commits the key that 31.2 rule 2 selects at the act's planning state (e = m_i);
    WRITE_SAME_KEY: a 0x7e that re-commits the key of its planning state (31.2 rule 8 (a), or the early
    finalisation of l. 327 through the override gate); ENROLL: a 0x7d at the planning state's account nonce,
    committing C_0; ACTIVATION: the activation of the key of its planning state; TRANSACTION: an ordinary 0x7c
    signed by the key of its planning state. `fee_mode` is a write's PI fee_mode (byte 169, section 19.2): 0 is
    paid by a; 1-3 are sponsored. (31.2 rule 10 (e)): a write's `fee` is the owner's FeeChoice for its PI
    (a layout-1 choice, a named sponsor of mode 1, a consent of mode 3); `fee_mode` alone stands for
    FeeChoice(fee_mode=...), and the sponsored carrier of a mode 1-3 write is built by build_payload with the
    sponsor's signature.
    """
    kind: str
    fee_mode: int = 0
    fee: FeeChoice | None = None

    def __post_init__(self):
        if self.kind not in PLAN_ACT_KINDS:
            raise ValueError("unknown planned act")
        if type(self.fee_mode) is not int or not 0 <= self.fee_mode <= 3:
            raise ValueError("a fee mode is 0, 1, 2 or 3")
        if (self.fee_mode or self.fee is not None) and not self.kind.startswith("WRITE"):
            raise ValueError("only a 0x7e carries a fee mode")
        if self.fee is not None:
            if not isinstance(self.fee, FeeChoice):
                raise ValueError("FeeChoice required")
            if self.fee_mode and (self.fee.layout != 2 or self.fee.fee_mode != self.fee_mode):
                raise ValueError("the act's fee_mode and its FeeChoice disagree")
            if self.fee.layout == 2:
                object.__setattr__(self, "fee_mode", self.fee.fee_mode)
        elif self.kind.startswith("WRITE"):
            object.__setattr__(self, "fee", FeeChoice(fee_mode=self.fee_mode))


@dataclass(frozen=True)
class PlannedElement:
    """The act x_index prepared against its planning state S_index (35.2 rule 1 (b), (c)).

    `planning_state` is S_index as (mode, migration_nonce, account nonce, activated, commitment hex), a model
    state that is never a canonical block (35.2 rule 1 (a)); `migration_nonce` is a write's PI.migration_nonce
    (m_index); `account_nonce` a 0x7d's or 0x7c's account nonce; `epoch` and `commitment` the key that the
    element commits, enrolls, reveals or is signed by; `pi` a write's complete PI in the layout of the named
    version; `fee` a write's FeeChoice (which says, under layout 1, whether its carrier is sponsored).
    """
    index: int
    kind: str
    role: str
    planning_state: tuple
    migration_nonce: int | None
    account_nonce: int | None
    epoch: int
    commitment: bytes
    fee_mode: int | None = None
    pi: bytes | None = None
    fee: FeeChoice | None = None

    def bound_values(self):
        return (self.kind, self.role, self.migration_nonce, self.account_nonce, self.epoch, self.commitment,
                self.fee_mode, self.pi)


@dataclass(frozen=True)
class PayloadPlan:
    """A payload of 34.2 rule 1 (c) as one plan bound to one canonical block B (35.2 rule 1 (a)).

    `anchor` is the CanonicalState anchor of B (31.2 rule 1) and `head` B as the tracker observes it; `acts` are
    the planned acts in payload order and `elements` the acts prepared against their planning states;
    `planned_at` is head.timestamp + SLOT, the earliest timestamp of a block after B, at which the planning
    states' gates are read; `choices` are the owner's PI values that 31.2 rule 1 binds as there (domain tag,
    verifier version, expiry, max_account_fee). Preparing an element after the first does not make it sendable
    alone (35.2 rule 1 (e)): only build_payload, with every element in order, turns the plan into a payload.
    """
    scope_key: str
    anchor: str
    head: AccountState
    acts: tuple
    elements: tuple
    planned_at: int
    choices: tuple
    warnings: tuple = ()          # what l. 252 and l. 417 say about an explicit own-funds choice

    @property
    def plan_id(self):
        return hashlib.sha256(repr((self.scope_key, self.anchor, self.head.to_dict(),
                                    [e.bound_values() for e in self.elements])).encode()).hexdigest()


@dataclass(frozen=True)
class PayloadReplan:
    """replan_payload's result (35.2 rule 1 (d)): REBOUND (the same elements, anchored at the new head) or VOID.

    `elements` gives, per element, the verdict against its recomputed planning state; `plan` is the rebound plan,
    or, where the plan is void, the same acts prepared again at the new head where they can be (None and `error`
    otherwise). The act list itself comes from the offers at the new head, which the tracker re-derives there
    under 34.2 rule 1; the tracker judges every payload again when it is built or exported.
    """
    status: str
    plan: PayloadPlan | None
    elements: tuple
    error: str | None = None


def _planning_tuple(si):
    return (si.mode, si.migration_nonce, si.account_nonce, si.activated,
            None if si.commitment is None else si.commitment.hex())


def _planned_pi(state, migration_nonce, commitment, domain_tag, verifier_version, expiry, max_account_fee, fee):
    """The complete PI of a planned write: _pi with PI.migration_nonce = m_i and the key that the write commits.
    `fee` is the act's FeeChoice in the named layout; an int selects a layout-2 fee mode."""
    return _pi(state, commitment, domain_tag, verifier_version, expiry, max_account_fee, fee,
               migration_nonce=migration_nonce)


def _require_key_usable(scope, store, tracker, commitment, epoch, index):
    if epoch in store.security(scope).compromised_epochs or tracker.key_exposed(scope, commitment):
        raise ValueError(f"CURRENT_KEY_COMPROMISED: act {index} would use the key of epoch {epoch}, which is known "
                         "exposed (31.2 rule 7 (b); 31.2 rule 8 (b): no same-key step of a recorded key)")


ENROLLMENT_EXPOSURE_WARNING = "ENROLLMENT_PUBLISHES_THE_LEGACY_PUBLIC_KEY_BEFORE_INCLUSION"


def plan_payload(scope, state, store, seed64, crypto, *, tracker, head, acts, domain_tag, verifier_version, expiry,
                 max_account_fee, current_key=None, no_sponsored_path=False, confirm_own_funds=None,
                 knowingly_enroll=False):
    """Spec 35.2 rule 1 (with 36.2): prepare the acts of one payload against their planning states.

    `state` is 31.2 rule 1's reading at the canonical block B and `head` B as the tracker observes it; `acts` the
    PlannedActs (or their kind names) in payload order, two or more (a lone write is prepare_recovery's plan).
    S_0 is B's state and S_i the state after x_0, ..., x_{i-1}, each taken as valid, at head.timestamp + SLOT.
    Each act takes its values from its own S_i: a write's PI.migration_nonce is m_i; a same-key write re-commits
    the key of S_i, whose epoch the plan knows (a key that an earlier act wrote, or the verified current key of B:
    `current_key`, a CurrentKey that a scan of B found), and keeps that epoch; a key that x_i newly selects is the
    key of e = m_i, refused where m_i > 2^32 - 1 (EPOCH_EXHAUSTED) or e is recorded (EPOCH_COMPROMISED: 31.2 rule 8
    (a), a same-key step first, after which the selection uses the next planning state, 36.2); a 0x7d's or 0x7c's
    account nonce is nonce(a) in S_i; an activation needs the activation condition in S_i, a transaction an
    activated sender in S_i; a write needs a gate of check 5 open in S_i (and, at B, check5_gate of rule 10 (c)).
    (31.2 rule 10 (e)): each write's PI takes the fee fields and the layout of its act's FeeChoice, under
    the constraints of section 19.2 and l. 417 (a mode-3 or layout-1 choice needs the owner's consent); a first
    write through the override gate of an enrolled key that another party holds, paid from a, carries the warning
    of l. 252 in `warnings`. Nothing is signed, proved, recorded or sent here.
    (spec 38.3 rule 1): such a first write is planned only where the wallet has no sponsored path to offer
    (`no_sponsored_path`) and on the owner's explicit choice after own_funds_warning(), confirmed through
    `confirm_own_funds`; a new-key
    write is refused while the key of its planning state lies at or above its m_i (31.2 rule 5), and `current_key` may be
    a key that only MATCH_ABOVE_BOUND finds, for the same-key writes of the range repair.
    Under §43.2, enrollment of a key with no known disclosure requires `knowingly_enroll=True`
    after showing its public-key exposure risk; the default is seed proof."""
    _require_tracker(store, tracker)
    _require_head_for_state(head, state)
    if not isinstance(domain_tag, bytes) or len(domain_tag) != 32:
        raise ValueError("DOMAIN_TAG must be the configured 32-byte value")
    acts = tuple(a if isinstance(a, PlannedAct) else PlannedAct(a) for a in acts)
    if len(acts) < 2:
        raise ValueError("PAYLOAD_PLAN_NEEDS_A_PRECURSOR_AND_ITS_ACTS: a payload of 34.2 rule 1 (c) holds two or more "
                         "acts; a lone write is prepare_recovery's plan")
    link_recorded_epochs(scope, seed64, crypto, store, tracker)
    recorded = set(store.security(scope).compromised_epochs)
    t = head.timestamp + tracker.slot
    si = replace(head, timestamp=t)              # S_0: B's state at the earliest timestamp of a block after B
    keys = {}                                    # commitment -> epoch, for keys that the plan knows
    if current_key is not None:
        if not isinstance(current_key, CurrentKey) or not (current_key.matches(scope, state)
                                                           or _above_bound(scope, state, current_key)):
            raise ValueError("STALE_OR_UNVERIFIED_CURRENT_KEY")
        keys[state.commitment] = current_key.epoch
    else:
        # (31.2 rule 5): a current key that an earlier above-bound scan found is known to the plan as well.
        remembered = store.above_bound_key(scope, state)
        if remembered is not None:
            keys[state.commitment] = remembered.epoch
    elements, warnings = [], []
    for index, act in enumerate(acts):
        ps = _planning_tuple(si)
        if act.kind in ("WRITE_NEW_KEY", "WRITE_SAME_KEY"):
            if state_gate(si) is None or (index == 0 and check5_gate(state)[0] is None):
                raise ValueError(f"PLANNING_STATE_GATE_CLOSED: act {index} is a write, and no gate of check 5 is open "
                                 f"in its planning state S_{index} (35.2 rule 1 (b); l. 1159-1161)")
            if type(expiry) is not int or expiry < t:
                raise ValueError(f"PLANNED_WRITE_EXPIRES_BEFORE_ITS_BLOCK: act {index}'s PI expiry is below "
                                 "head.timestamp + SLOT, the earliest timestamp of a block after B (check 4, l. 259)")
            m = si.migration_nonce
            if act.kind == "WRITE_NEW_KEY":
                if m > UINT32_MAX:
                    raise ValueError("EPOCH_EXHAUSTED")
                current = keys.get(si.commitment) if si.commitment is not None else None
                if current is not None and current >= m and current not in recorded:
                    # (31.2 rule 5, l. 8957): the key of S_i lies at or above m_i, outside U; a selection at m_i
                    # gives that key itself or an epoch below it from which a later selection reaches it again.
                    raise ValueError(f"CURRENT_KEY_ABOVE_U_SAME_KEY_REPAIR_BEFORE_ANY_NEW_SELECTION: act {index} would "
                                     f"select epoch {m} = m_{index} while the key of S_{index} is the key of epoch "
                                     f"{current}; the {current - m + 1} same-key writes of 31.2 rule 8 (a) come first "
                                     "(31.2 rule 5)")
                if m in recorded:
                    raise ValueError(f"EPOCH_COMPROMISED: act {index} would select epoch {m} = m_{index}, which is "
                                     "recorded; 31.2 rule 8 (a): a same-key step first, then the selection at the "
                                     "planning state that the step leaves (35.2 rule 1 (c); 36.2)")
                key = derive_key(scope, seed64, m, crypto)
                if tracker.link_key(scope, key.commitment, m, reason="planned key whose commitment is known exposed"):
                    raise ValueError("EPOCH_COMPROMISED")
                commitment, epoch, role = key.commitment, m, "NEW_KEY"
            else:
                if si.mode not in ("PQ_BY_ENROLL", "PQ_BY_PROOF") or si.commitment not in keys:
                    raise ValueError(f"SAME_KEY_NEEDS_THE_KEY_OF_ITS_PLANNING_STATE: act {index} re-commits the key of "
                                     f"S_{index}, which the plan does not know; it is a key that an earlier act of the "
                                     "plan wrote or the verified current key of B (current_key from a scan of B; "
                                     "31.2 rules 2 and 8 (a))")
                commitment, epoch, role = si.commitment, keys[si.commitment], "SAME_KEY"
                _require_key_usable(scope, store, tracker, commitment, epoch, index)
            choice = PlanChoice(domain_tag, verifier_version, expiry, max_account_fee, act.fee)
            _check_fee_choice(choice, state)
            if (index == 0 and not act.fee.is_sponsored
                    and _others_can_send_from_a(scope, state, seed64, crypto, tracker, check5_gate(state)[0])):
                token = own_funds_warning(legacy_address=state.legacy_address, max_account_fee=max_account_fee,
                                          verifier_version=verifier_version)["token"]
                warnings.extend(_resolve_fee(act.fee, True, no_sponsored_path=no_sponsored_path,
                                             confirmed=confirm_own_funds, token=token)[1])
            pi = _planned_pi(state, m, commitment, domain_tag, verifier_version, expiry, max_account_fee, act.fee)
            elements.append(PlannedElement(index, "WRITE", role, ps, m, None, epoch, commitment,
                                           act.fee.fee_mode, pi, act.fee))
            keys[commitment] = epoch
            si = replace(si, mode="PQ_BY_PROOF", migration_nonce=m + 1, commitment=commitment,
                         activated=False, code_kind="EMPTY")
        elif act.kind == "ENROLL":
            if not legacy_before_T(si):
                raise ValueError(f"ENROLLMENT_NEEDS_A_LEGACY_PLANNING_STATE_BEFORE_T: act {index} (l. 181-186)")
            if head.legacy_seed_proof_from_t0:
                if tracker.migration_choice(scope, head, knowingly_enroll=knowingly_enroll) != "ENROLL":
                    raise ValueError("UNPUBLISHED_KEY_USE_SEED_PROOF_OR_CONFIRM_ENROLLMENT")
                if (knowingly_enroll
                        and tracker.migration_choice(scope, head, knowingly_enroll=False) == "SEED_PROOF"):
                    warnings.append(ENROLLMENT_EXPOSURE_WARNING)
            if 0 in recorded:
                raise ValueError("EPOCH_COMPROMISED: a 0x7d commits the key of epoch 0, which is recorded")
            key = derive_key(scope, seed64, 0, crypto)
            if tracker.link_key(scope, key.commitment, 0, reason="planned key whose commitment is known exposed"):
                raise ValueError("EPOCH_COMPROMISED")
            elements.append(PlannedElement(index, "ENROLL", "NEW_KEY", ps, None, si.account_nonce, 0, key.commitment))
            keys[key.commitment] = 0
            si = replace(si, mode="PQ_BY_ENROLL", migration_nonce=si.migration_nonce + 1,
                         account_nonce=si.account_nonce + 1, commitment=key.commitment, activated=False,
                         enrolled_at=t, code_kind="EMPTY")
        else:
            if act.kind == "ACTIVATION" and activation_preview(si) is None:
                raise ValueError(f"ACTIVATION_CONDITION_FAILS_IN_ITS_PLANNING_STATE: act {index} (l. 315)")
            if act.kind == "TRANSACTION" and not si.activated:
                raise ValueError(f"SENDER_CLASS_IN_ITS_PLANNING_STATE: act {index} is an ordinary 0x7c, which needs an "
                                 "activated account in S_i (l. 313-318)")
            if si.commitment not in keys:
                raise ValueError(f"SIGNER_KEY_OF_ITS_PLANNING_STATE_UNKNOWN: act {index} is signed by the key of "
                                 f"S_{index}, which the plan does not know (pass current_key from a scan of B)")
            commitment, epoch = si.commitment, keys[si.commitment]
            _require_key_usable(scope, store, tracker, commitment, epoch, index)
            elements.append(PlannedElement(index, act.kind, "KEY_OF_THE_PLANNING_STATE", ps, None, si.account_nonce,
                                           epoch, commitment))
            si = replace(si, activated=True, account_nonce=si.account_nonce + 1, code_kind="PQ_MARKER")
    return PayloadPlan(scope.key, state.anchor, head, acts, tuple(elements), t,
                       (domain_tag.hex(), verifier_version, expiry, max_account_fee), tuple(warnings))


def validate_payload_plan(plan, scope, state, head):
    """31.2 rule 3 with 35.2 rule 1 (a), (d): a payload plan is used only at its anchor B; at another head it is
    STALE until replan_payload has re-planned it as a whole."""
    if not isinstance(plan, PayloadPlan):
        raise ValueError("PayloadPlan required")
    _require_head_for_state(head, state)
    if plan.scope_key != scope.key or plan.anchor != state.anchor or plan.head.to_dict() != head.to_dict():
        raise ValueError("STALE_PAYLOAD_PLAN: a payload plan is bound to one canonical block B; at another head it is "
                         "re-planned as a whole (replan_payload) and rebound unchanged or void, never rebound by "
                         "relabelling (spec 35.2 rule 1 (a), (d); 31.2 rule 3)")
    return True


def replan_payload(plan, scope, state, store, seed64, crypto, *, tracker, head, current_key=None):
    """Spec 35.2 rule 1 (d): re-plan a payload at a later canonical head B2 as a whole.

    The planning states are recomputed at B2 (S_0 is B2's state, each element taken as valid), and every element's
    bound values are compared with its recomputed planning state: a write's PI.migration_nonce with m_i, its key
    with the key of S_i (a same-key write) or the key of epoch m_i (a new key), a 0x7d's or 0x7c's account nonce
    with nonce(a) in S_i, the gate, a PI's expiry (at head.timestamp + SLOT), the activation condition and the
    sender class there, and no key that it uses may be known exposed since. Where every element is the same and every condition holds, the plan is REBOUND to
    B2 unchanged: its PIs, proofs and signatures are used as they are. Otherwise it is VOID: each element's verdict
    says whether its PI changed (a new proof with fresh coins, 22.2) or not (it keeps its proof); no bytes are
    edited, and a predecessor that a reorganization removed is met by re-planning, never by sending the remaining
    elements. The same acts are prepared again at B2 where they can be (the result's `plan`); the act list itself
    follows the offers at B2. (spec 38.3 rule 1): a plan whose first write the owner chose to pay from a
    after the displayed warning (its `warnings` hold OWN_FUNDS_WARNING) is prepared again on that same choice, for the
    same account, cap and version."""
    if not isinstance(plan, PayloadPlan):
        raise ValueError("PayloadPlan required")
    _require_tracker(store, tracker)
    _require_head_for_state(head, state)
    if plan.scope_key != scope.key or plan.head.account != head.account:
        raise ValueError("payload plan of another scope or account")
    link_recorded_epochs(scope, seed64, crypto, store, tracker)
    recorded = set(store.security(scope).compromised_epochs)
    t = head.timestamp + tracker.slot
    si = replace(head, timestamp=t)
    verdicts, rebound = [], []
    for e in plan.elements:
        changes = []
        if e.kind == "WRITE":
            if e.migration_nonce != si.migration_nonce:
                changes.append("PI_MIGRATION_NONCE")
            if e.role == "SAME_KEY" and e.commitment != si.commitment:
                changes.append("SAME_KEY_MATCH")
            if e.role == "NEW_KEY" and e.epoch != si.migration_nonce:
                changes.append("SELECTED_EPOCH")
            if state_gate(si) is None or (e.index == 0 and check5_gate(state)[0] is None):
                changes.append("GATE")
            if t > int.from_bytes(e.pi[129:137], "big"):
                changes.append("EXPIRY")
        elif e.kind == "ENROLL":
            if e.account_nonce != si.account_nonce:
                changes.append("ACCOUNT_NONCE")
            if not legacy_before_T(si):
                changes.append("ENROLLMENT_CONDITION")
        else:
            if e.account_nonce != si.account_nonce:
                changes.append("ACCOUNT_NONCE")
            if e.commitment != si.commitment:
                changes.append("KEY_OF_THE_PLANNING_STATE")
            if e.kind == "ACTIVATION" and activation_preview(si) is None:
                changes.append("ACTIVATION_CONDITION")
            if e.kind == "TRANSACTION" and not si.activated:
                changes.append("SENDER_CLASS")
        if e.epoch in recorded or tracker.key_exposed(scope, e.commitment):
            changes.append("KEY_KNOWN_EXPOSED")
        kept = {"WRITE": "KEEPS_ITS_PROOF", "ENROLL": "KEEPS_ITS_CARRIER"}.get(e.kind, "KEEPS_ITS_SIGNATURE")
        renew = {"WRITE": "NEW_PROOF_WITH_FRESH_COINS", "ENROLL": "SIGN_AGAIN"}.get(e.kind, "SIGN_AGAIN")
        verdicts.append({"index": e.index, "kind": e.kind, "changed": changes,
                         "verdict": "UNCHANGED_" + kept if not changes else "CHANGED_" + renew})
        rebound.append(replace(e, planning_state=_planning_tuple(si)))
        if e.kind == "WRITE":
            si = replace(si, mode="PQ_BY_PROOF", migration_nonce=si.migration_nonce + 1, commitment=e.commitment,
                         activated=False, code_kind="EMPTY")
        elif e.kind == "ENROLL":
            si = replace(si, mode="PQ_BY_ENROLL", migration_nonce=si.migration_nonce + 1,
                         account_nonce=si.account_nonce + 1, commitment=e.commitment, activated=False,
                         enrolled_at=t, code_kind="EMPTY")
        else:
            si = replace(si, activated=True, account_nonce=si.account_nonce + 1, code_kind="PQ_MARKER")
    if all(not v["changed"] for v in verdicts):
        return PayloadReplan("REBOUND", replace(plan, anchor=state.anchor, head=head, elements=tuple(rebound),
                                                planned_at=t), tuple(verdicts))
    domain, version, expiry, fee = plan.choices
    try:
        own = OWN_FUNDS_WARNING in plan.warnings
        again = plan_payload(scope, state, store, seed64, crypto, tracker=tracker, head=head, acts=plan.acts,
                             domain_tag=bytes.fromhex(domain), verifier_version=version, expiry=expiry,
                             max_account_fee=fee, current_key=current_key, no_sponsored_path=own,
                             knowingly_enroll=ENROLLMENT_EXPOSURE_WARNING in plan.warnings,
                             confirm_own_funds=own_funds_warning(legacy_address=state.legacy_address,
                                                                 max_account_fee=fee,
                                                                 verifier_version=version)["token"] if own else None)
        error = None
    except ValueError as exc:
        again, error = None, str(exc)
    if again is not None:
        old = {e.index: e for e in plan.elements}
        for v, e in zip(verdicts, again.elements):
            if e.kind == "WRITE":
                v["prepared_again"] = ("UNCHANGED_PI_KEEPS_ITS_PROOF" if e.pi == old[e.index].pi
                                       else "CHANGED_PI_NEW_PROOF_WITH_FRESH_COINS")
    return PayloadReplan("VOID", again, tuple(verdicts), error)


def _mode0_carrier(state, nonce, pi, proof, config):
    """The existing layout-2 mode-0 0x7e of a planned write (the encoding of _verified_carrier, at PI nonce m_i).
    _encode_0x7e with the self-pay choice (check 7 included)."""
    return _encode_0x7e(state, nonce, pi, proof, config, SELF_PAY)


def build_payload(plan, scope, state, store, tracker, *, head, proofs, verify_proof, config, activation_config,
                  seed64, crypto, carriers=None, fee_path=None, balance_covers_acts=False, sponsor=None):
    """Spec 35.2 rule 1: turn a payload plan into one OnePayloadBundle at its anchor B, every element in order.

    `proofs` maps each write's index to the proof of its own PI (verified here by `verify_proof`, as
    export_recovery does); a write paid by a (fee mode 0, or an unsponsored layout-1 choice) is encoded as the
    unsponsored 0x7e at its PI.migration_nonce; a 0x7d's carrier is the caller's (`carriers` by index: this adapter
    holds no secp256k1 key); an activation or a transaction is signed with the key of its planning state at its
    planning-state account nonce. (31.2 rule 10 (e)): a sponsored write (fee mode 1-3, or a sponsored
    layout-1 choice), such as the sponsored writes past PI.migration_nonce that 34.2 rule 1 (f) makes the act, is
    built here as the sponsored 0x7e of its PI and its layout, with `sponsor`'s signature (Sponsor); without a
    `sponsor`, a carrier built by a sponsor service may still be passed in `carriers`. The plan
    must be anchored at `head` (STALE_PAYLOAD_PLAN otherwise: replan_payload first), and the bundle is checked by
    tracker.bundle_preview, which recomputes the planning states at B and judges 34.2 rule 1 (a). Nothing is
    recorded or delivered here: tracker.export_bundle does both."""
    validate_payload_plan(plan, scope, state, head)
    _require_tracker(store, tracker)
    if type(balance_covers_acts) is not bool:
        raise ValueError("balance_covers_acts must be boolean")
    if not callable(verify_proof):
        raise ValueError("verification callback required")
    if activation_config["chain_id"] != state.chain_id:
        raise ValueError("activation chain differs from canonical state")
    if sponsor is not None and not isinstance(sponsor, Sponsor):
        raise ValueError("Sponsor required")
    link_recorded_epochs(scope, seed64, crypto, store, tracker)
    carriers = dict(carriers or {})
    account = Account(state.chain_id, state.genesis_hash, state.legacy_address)
    address = bytes.fromhex(state.legacy_address)
    elements = []
    for e in plan.elements:
        if e.kind == "WRITE":
            fee = e.fee if e.fee is not None else FeeChoice(fee_mode=e.fee_mode)
            proof = proofs.get(e.index)
            if not isinstance(proof, bytes) or not proof:
                raise ValueError(f"PROOF_REQUIRED: element {e.index} needs a proof of its own PI (a changed PI gets a new "
                                 "proof with fresh coins, 22.2)")
            if (config["chain_id"] != state.chain_id
                    or bytes.fromhex(config["domain_tag"].removeprefix("0x")) != e.pi[32:64]
                    or config["verifier_version"] != int.from_bytes(e.pi[125:129], "big")
                    or config.get("pi_layout", fee.layout) != fee.layout):
                raise ValueError("STALE_PROOF_CONFIGURATION")
            if verify_proof(proof, e.pi) is not True:
                raise ValueError("INVALID_PROOF")
            if not fee.is_sponsored or sponsor is not None:
                raw = _encode_0x7e(state, e.migration_nonce, e.pi, proof, config, fee, sponsor=sponsor, crypto=crypto)
            else:
                raw = carriers.get(e.index)
                if not isinstance(raw, bytes) or not raw:
                    raise ValueError(f"SPONSOR_REQUIRED: element {e.index} is a sponsored write (fee mode {e.fee_mode}); "
                                     "the adapter builds its sponsored 0x7e with the sponsor's signature (sponsor=Sponsor; "
                                     "31.2 rule 10 (e))")
            elements.append(PayloadElement("WRITE", raw, authorization=Authorization.from_pi(account, e.pi,
                                                                                            epoch=e.epoch),
                                           sponsored=fee.is_sponsored))
        elif e.kind == "ENROLL":
            raw = carriers.get(e.index)
            if not isinstance(raw, bytes) or not raw:
                raise ValueError(f"ENROLLMENT_CARRIER_REQUIRED: element {e.index} is a 0x7d, signed with a's secp256k1 "
                                 "key, which this adapter does not hold")
            elements.append(PayloadElement("WRITE", raw, authorization=Authorization(
                account, "ENROLL", e.account_nonce, e.commitment, epoch=e.epoch)))
        else:
            key = derive_key(scope, seed64, e.epoch, crypto)
            if key.commitment != e.commitment:
                raise ValueError("derived key does not match the planned key")
            _require_key_usable(scope, store, tracker, e.commitment, e.epoch, e.index)
            raw, _ = wire.signed_pq(crypto, activation_config, address, _signing_record(key), e.account_nonce, 0,
                                    e.kind == "ACTIVATION")
            elements.append(PayloadElement(e.kind, raw, commitment=e.commitment, account_nonce=e.account_nonce))
    validate_payload_plan(plan, scope, state, head)    # again after the proofs were verified
    bundle = OnePayloadBundle(head, tuple(elements), fee_path=fee_path)
    try:
        tracker.bundle_preview(scope, bundle, balance_covers_acts=balance_covers_acts)
    except ValueError as exc:
        if str(exc).startswith("BUNDLE_ACT_PREEMPTIBLE") and any(
                not (e.fee or FeeChoice(fee_mode=e.fee_mode)).is_sponsored for e in plan.elements[1:]
                if e.kind == "WRITE"):
            raise ValueError(f"{exc}; a write after the precursor is paid by a: {SPONSORED_ACT_ROUTE}") from exc
        raise
    return bundle


def acts_from_offer(offer, *, sponsored=None, self_pay=SELF_PAY):
    """Map an offer's payload plan to PlannedActs (31.2 rule 10 (e)).

    `offer` is an offer of observe_head, its `payload`, or a RevivalWarning's payload, each carrying `plan` (34.2 rule 1
    (c) with 35.2 rule 1). A write marked SPONSORED takes the owner's sponsored FeeChoice `sponsored` (mode 1, 2 or 3,
    or a sponsored layout-1 choice; required where the plan has one, since the owner chooses it, l. 417), a write paid
    by a takes `self_pay`; a write that re-commits the key of its planning state is WRITE_SAME_KEY, one that commits
    the key that 31.2 rule 2 selects there is WRITE_NEW_KEY; ENROLL, ACTIVATION and TRANSACTION map to themselves. A
    write of a key not derived from the seed (C_IND) or of a key that the device does not know, a tracked carrier
    that commits another key, an ECDSA transaction and a rotate are not planned by this adapter (NOT_PLANNABLE)."""
    from authorization_tracking import KEY_NEW, KEY_SAME
    payload = offer.get("payload", offer) if isinstance(offer, dict) else None
    plan = (payload or {}).get("plan")
    if not isinstance(plan, dict) or not isinstance(plan.get("acts"), list):
        raise ValueError("the offer names no payload plan")
    if sponsored is not None and (not isinstance(sponsored, FeeChoice) or not sponsored.is_sponsored):
        raise ValueError("`sponsored` is the owner's FeeChoice of a sponsored carrier")
    out = []
    for act in plan["acts"]:
        kind = act.get("kind")
        if kind == "WRITE":
            role = {KEY_SAME: "WRITE_SAME_KEY", KEY_NEW: "WRITE_NEW_KEY"}.get(act.get("key"))
            if role is None:
                raise ValueError(f"NOT_PLANNABLE: act {act.get('index')} writes {act.get('key')}; the adapter prepares "
                                 "seed keys at their planning states only (a key not derived from the seed and its "
                                 "warning and backup, 31.2 rule 8 (b), stay open)")
            if act.get("fee") == "SPONSORED":
                if sponsored is None:
                    raise ValueError(f"SPONSORED_FEE_CHOICE_REQUIRED: act {act.get('index')} is a sponsored write; the "
                                     "owner chooses its fee mode (l. 417; section 19.2)")
                out.append(PlannedAct(role, fee=sponsored))
            else:
                out.append(PlannedAct(role, fee=self_pay))
        elif kind in ("ENROLL", "ACTIVATION", "TRANSACTION"):
            out.append(PlannedAct(kind))
        else:
            raise ValueError(f"NOT_PLANNABLE: act {act.get('index')} is {kind}, which this adapter does not plan")
    return tuple(out)


# ---------------------------------------------------------------------------------------------------------------
# (spec 31.2 rule 10 (d), rule 8 (a)): the same-key step as a rotate to the current key.

ROTATE_SELECTOR = bytes.fromhex("262f8ae0")    # keccak256(ASCII("rotate(uint8,bytes,bytes)"))[0:4] (24.2 rule 2)
ROTATE_POP_TAG = b"ETH-PQ-ROTATE-POP/v1"       # 16.4 signing preimages; 24.2 rule 3 (d)
PQ_TX_TAG = b"ETH-PQ-TX/v1"


def _ceil32(n):
    return (n + 31) // 32 * 32


def rotate_calldata(new_alg_id, new_pk, pop_sig):
    """The strict canonical ABI of rotate(uint8 new_alg_id, bytes new_pk, bytes pop_sig) behind ROTATE_SELECTOR
    (24.2 rule 2): the selector, the alg word, the head offsets 0x60 and 0x80 + P1, then each byte string with its
    length word and zero padding to a multiple of 32; 3,908 bytes for ML-DSA-44."""
    if type(new_alg_id) is not int or not 0 <= new_alg_id <= 255:
        raise ValueError("new_alg_id is a uint8")
    p1, p2 = _ceil32(len(new_pk)), _ceil32(len(pop_sig))

    def word(value):
        return value.to_bytes(32, "big")
    return (ROTATE_SELECTOR + word(new_alg_id) + word(0x60) + word(0x80 + p1) + word(len(new_pk)) + new_pk
            + bytes(p1 - len(new_pk)) + word(len(pop_sig)) + pop_sig + bytes(p2 - len(pop_sig)))


def rotate_pop_preimage(chain_id, account, account_nonce, new_alg_id, new_pk):
    """The proof-of-possession preimage of 16.4 and 24.2 rule 3 (d): ASCII("PQ-ROTATE") || u256(chain_id) ||
    account(20) || u64(account_nonce) || u8(new_alg_id) || new_pk, where account_nonce is the nonce field of the
    0x7c that carries the rotate (24.2 rule 7)."""
    return (b"PQ-ROTATE" + chain_id.to_bytes(32, "big") + account + account_nonce.to_bytes(8, "big")
            + bytes([new_alg_id]) + new_pk)


@dataclass(frozen=True)
class SameKeyRotate:
    """The same-key step of 31.2 rule 8 (a) as a 0x7c that calls rotate to the current key.

    `raw` is the signed 0x7c (to PQ_REGISTRY, value 0, the strict rotate calldata; pq_pk revealed where it activates);
    `authorization` the binding authorization that the tracker tracks for it (a ROTATE at its account nonce, signed
    by and binding the current key, its epoch kept, l. 328); `form` the step's form (wallet_epochs
    STEP_ROTATE or STEP_ACTIVATING_ROTATE); `row` the signing record without any secret."""
    raw: bytes
    authorization: Authorization
    form: str
    account_nonce: int
    row: dict


def _signed_rotate_0x7c(crypto, config, sender, key, nonce, activating):
    """Sign the proof of possession with the new key (here the current key) over the 0x7c's nonce, encode the
    calldata, then sign the 0x7c with the current key (the order of 24.2 rule 7); both signatures are verified."""
    registry = config.get("registry")
    if not isinstance(registry, str) or len(registry.removeprefix("0x")) != 40:
        raise ValueError("the configuration names PQ_REGISTRY's 20-byte address (`registry`)")
    pop_digest = crypto("hash", rotate_pop_preimage(config["chain_id"], sender, nonce, 1, key.public_key))
    pop_message = ROTATE_POP_TAG + pop_digest
    pop_sig = crypto("sign", key.xi, pop_message, ROTATE_POP_TAG)
    if crypto.text("verify", key.public_key, pop_message, ROTATE_POP_TAG, pop_sig) != "true":
        raise ValueError("BAD_POP: the proof of possession does not verify")
    data = rotate_calldata(1, key.public_key, pop_sig)
    tx = [config["chain_id"], sender, nonce, config["max_priority_fee_per_gas"], config["max_fee_per_gas"],
          config["pq_transaction_gas_limit"], bytes.fromhex(registry.removeprefix("0x")), 0, data, [], 1,
          [key.public_key] if activating else [], b""]
    preimage = b"\x7c" + wire.rlp(tx)
    message = PQ_TX_TAG + crypto("hash", preimage)
    tx[12] = crypto("sign", key.xi, message, PQ_TX_TAG)
    if crypto.text("verify", key.public_key, message, PQ_TX_TAG, tx[12]) != "true":
        raise ValueError("the 0x7c signature does not verify")
    raw = b"\x7c" + wire.rlp(tx)
    return raw, {"type": 0x7C, "to": registry.removeprefix("0x"), "nonce": nonce, "value": 0, "activating": activating,
                 "calldata_bytes": len(data), "selector": data[:4].hex(), "pop_message": pop_message.hex(),
                 "pop_signature": pop_sig.hex(), "pop_signature_verified": True, "message": message.hex(),
                 "ctx": PQ_TX_TAG.hex(), "signature": tx[12].hex(), "signature_verified": True,
                 "raw_sha256": hashlib.sha256(raw).hexdigest()}


def _same_key_rotate_form(scope, state, store, current_key, tracker):
    """The rotate form of the same-key step that the selection offers at B, or a refusal. (31.2 rule 5): also a
    step of the range repair of a key that only MATCH_ABOVE_BOUND finds (OFFER_RANGE_REPAIR)."""
    repair = _above_bound(scope, state, current_key)
    _refuse_exposed_current_key(scope, state, store, tracker, current_key, repair=repair)
    selected = select_new_key_epoch(scope, state, store, current_key=current_key)
    forms = [f for f in selected.steps if f in ROTATE_STEP_FORMS]
    if selected.status not in ("OFFER_SAME_KEY_RECOMMIT", "OFFER_SAME_KEY_ROTATE", "OFFER_RANGE_REPAIR") or not forms:
        raise ValueError("SAFE_SAME_KEY_ROTATE_UNAVAILABLE: the selection offers no rotate to the current key at B "
                         f"({selected.status}, {selected.reason}; 31.2 rule 8 (a))")
    decision = revalidate_key_use(scope, state, store, current_key, for_range_repair=repair)
    if not decision.allowed:
        raise ValueError(decision.reason)
    return forms[0]


def prepare_same_key_rotate(scope, state, store, current_key, seed64, crypto, config, *, tracker, head,
                            confirm_extra_transaction_and_fee):
    """(31.2 rule 10 (d), rule 8 (a)): the same-key step as a rotate to the current key; nothing is sent.

    With e = m recorded and the current key's epoch not recorded, an account that is binding-final and activated
    takes a 0x7c that calls rotate to the current key, with pop_sig by that key (vector ROT-D2); a PQ_BY_PROOF
    account that is not activated, or a binding-final PQ_BY_ENROLL one that is not, an activating 0x7c that carries
    that rotate (14.4 rule 6, 14.8 item 9): no proof, two code deposits, and the account activated and binding-final
    under the current key. The owner approves the extra transaction and its fee
    (`confirm_extra_transaction_and_fee`). The 0x7c is at the head's account nonce, the proof of possession binds
    that nonce (24.2 rule 7), and the returned SameKeyRotate goes to export_same_key_rotate, which lets the tracker
    judge it (34.2 rule 1 (a)) and record it before delivery. Once the step's block is canonical, the wallet reads
    the state again and selects again (31.2 rule 8 (a)).
    """
    _require_tracker(store, tracker)
    if state.alg_id != 1 or state.alg_name != "ML-DSA-44":
        raise ValueError("adapter supports ML-DSA-44 only")
    link_recorded_epochs(scope, seed64, crypto, store, tracker)
    if confirm_extra_transaction_and_fee is not True:
        raise ValueError("explicit approval of the extra transaction and its fee is required (31.2 rule 8 (a))")
    form = _same_key_rotate_form(scope, state, store, current_key, tracker)
    _require_head_for_state(head, state)
    key = derive_key(scope, seed64, current_key.epoch, crypto)
    if key.commitment != state.commitment:
        raise ValueError("current key does not match the state commitment")
    if config["chain_id"] != state.chain_id:
        raise ValueError("rotate chain differs from canonical state")
    activating = form == STEP_ACTIVATING_ROTATE
    n = head.account_nonce
    raw, row = _signed_rotate_0x7c(crypto, config, bytes.fromhex(state.legacy_address), key, n, activating)
    account = Account(state.chain_id, state.genesis_hash, state.legacy_address)
    auth = Authorization(account, "ROTATE", n, key.commitment, activating=activating,
                         signer_commitment=key.commitment, epoch=key.epoch)
    return SameKeyRotate(raw, auth, form, n, row)


def export_same_key_rotate(step, scope, state, store, current_key, seed64, crypto, *, tracker, head, deliver,
                           confirm_revival=None, no_one_payload_path=False):
    """(31.2 rule 10 (d)): re-check that the selection still offers this rotate at B, then let the tracker
    judge it under 34.2 rule 1 (a), record it (EXPORTING, then EXPORTED) and deliver it (AuthorizationTracker.export,
    with its confirmation routes)."""
    if not isinstance(step, SameKeyRotate):
        raise ValueError("SameKeyRotate required")
    _require_tracker(store, tracker)
    _require_head_for_state(head, state)
    link_recorded_epochs(scope, seed64, crypto, store, tracker)
    if _same_key_rotate_form(scope, state, store, current_key, tracker) != step.form \
            or step.account_nonce != head.account_nonce or step.authorization.commitment != state.commitment:
        raise ValueError("STALE_SAME_KEY_ROTATE: prepare it again at the bound block")
    return tracker.export(scope, step.authorization, step.raw, deliver, head=head, confirm_revival=confirm_revival,
                          no_one_payload_path=no_one_payload_path)
