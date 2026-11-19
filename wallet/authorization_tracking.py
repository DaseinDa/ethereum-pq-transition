"""Public-test migration wallet: authorization tracking and monotonic key-exposure state."""
from __future__ import annotations

from dataclasses import asdict, dataclass, replace
import hashlib
import json
from pathlib import Path

from wallet_epochs import (
    DerivationScope, MetadataError, UINT32_MAX, UINT64_MAX, WalletEpochStore,
    CODE_KINDS, _atomic_json, _hex, _locked, _uint,
)
from reachability import (
    A_KEY, IND_KEY, FRESH_KEY, SLOT_DEFAULT, Config, Problem, Step, Verdict, a_moves, apply as model_apply,
    binds, critical_times, deadline as model_deadline, ecdsa_alive, final as model_final,
    gate as model_gate, planning_states as model_planning_states, search, state_of, valid as model_valid,
)

# Offer labels returned by observe_head. They are offers to the owner, never sends.
WAIT_FINALITY_WATCH_REORG = "WAIT_FINALITY_WATCH_REORG"
OFFER_AT_HEAD_NONCE = "OFFER_FINALIZING_ACTIVATION_OR_ADVANCE_PAST_PI_NONCE"
OFFER_ADVANCE_PAST_PI_NONCE = "OFFER_ADVANCE_PAST_PI_NONCE"
OFFER_ACTIVATION_ONLY = "OFFER_CURRENT_KEY_ACTIVATION_DO_NOT_ADVANCE_MIGRATION_NONCE"
OFFER_ONE_PAYLOAD_BUNDLE = "OFFER_ONE_PAYLOAD_BUNDLE"
# (spec 39.2 rule 1 (c)): in the re-commit gate, where a member placed before the activation can make it
# fail while the PI is includable after it, the act is sponsored same-key writes through PI.migration_nonce.
OFFER_SPONSORED_WRITES = "OFFER_SPONSORED_WRITES_PAST_PI_NONCE"
OFFER_RANGE_REPAIR = "OFFER_RANGE_REPAIR"                               # 31.2 rule 5 (also MATCH_ABOVE_BOUND)
FOLLOW_RULE_7B_8B = "FOLLOW_RULE_7B_8B_PATH_WITH_WARNING"
OFFER_ACCOUNT_NONCE_CONSUMPTION = "OFFER_ACCOUNT_NONCE_CONSUMPTION"
REPORT_STEALTH_OFFER_OVERRIDE = "REPORT_STEALTH_ENROLLMENT_OFFER_OVERRIDE"
REPORT_STEALTH_WINDOW_CLOSED = "REPORT_STEALTH_ENROLLMENT_WINDOW_CLOSED"
WAIT_FRESH_PRECURSOR = "WAIT_FRESH_PRECURSOR_HELD_UNTIL_RULE_2"     # 34.2 rule 1 (g)
# Remedies named by RevivalWarning.
ONE_PAYLOAD_BUNDLE = "ONE_PAYLOAD_BUNDLE"
ACTIVATE_CURRENT_KEY_FIRST = "ACTIVATE_CURRENT_KEY_FIRST"
ACCOUNT_NONCE_ACT_FIRST = "TRANSACTION_AT_THE_ACCOUNT_NONCE_FIRST"    # 34.2 rule 1 (e) for a rotate
FOLLOW_RULE_7B_8B_PATH = "FOLLOW_RULE_7B_8B_PATH"
HOLD_FRESH_PRECURSOR = "HOLD_FRESH_PRECURSOR_UNTIL_RULE_2"          # 34.2 rule 1 (g)
HOLD_WRITE_WAIT_FINALITY = "HOLD_WRITE_WAIT_FINALITY_WATCH_REORG"   # revived only off the head's branch
# The answer that an offer gives: which part of 34.2 rule 1 decides it.
ANSWER_ACT_WITHOUT_PRECURSOR = "ACT_WITHOUT_PRECURSOR"              # 34.2 rule 1 (e)
ANSWER_PRECURSOR_WITH_ITS_ACTS = "PRECURSOR_WITH_ITS_ACTS"          # 34.2 rule 1 (b), (c), (f)
ANSWER_WAIT = "WAIT"                                                # 32.2 rule 3 (c); 34.2 rule 1 (g)
ANSWER_RULE_7B_8B = "RULE_7B_8B"
# 34.2 rule 1 (g): the margin of l. 1765 that the override gate keeps before deadline(a)
# for a chain-finalized block after the tracked PI's expiry and for the override to land. The spec
# fixes no value (section 18.18 (b), ledger D18-TIMING): this default is a placeholder of the
# component, and a deployment sets its own (AuthorizationTracker(..., override_margin=)).
OVERRIDE_MARGIN_DEFAULT = 30 * 24 * 3600
# l. 259: expiry <= now + PROOF_MAX_LIFETIME (7 days); the expiry of a modelled fresh write.
PROOF_MAX_LIFETIME = 7 * 24 * 3600
# Commitment of a model 0x7d of A. A's own keys are modelled as
# reachability.A_KEY.
PREEMPTING_ENROLLMENT = hashlib.sha256(b"model: a 0x7d of A at the account nonce (l. 45)").digest()

FEE_PATHS = ("SPONSOR", "OWN_FUNDS", "MIXED")
# (31.2 rule 10 (e); section 19.2): PI_bytes is 169 bytes under PI_LAYOUT_1 (16.3) and 198 under PI_LAYOUT_2.
PI_LAYOUT_BYTES = {1: 169, 2: 198}
ONE_PAYLOAD_ROUTES = ("PRIVATE_RELAY",)
DELIVERIES = ("ONE_PAYLOAD", "SPLIT")
# (34.2 rule 1 (g)): where a carrier is. A carrier is A's only once it is in a
# block of any branch or in a pool, or has been handed to a relay, a builder, a sponsor or an
# aggregator (l. 47, l. 9929); a write that the device has only prepared, recorded or had proved is
# not. Every tracked carrier is a member of K whatever its custody (34.2 rule 1 (a)), which can only
# add runs to the condition.
CUSTODY_HELD_BY_A = ("IN_BLOCK", "IN_POOL", "BROADCAST", "RELAY", "BUILDER", "SPONSOR", "AGGREGATOR",
                     "EXPORTED")
CUSTODY_OTHER_HANDS = ("PROVING_SERVICE",)
CUSTODY_NOT_OUT = ("UNSTATED", "PREPARED", "SIGNED", "EXPORTING")
CUSTODIES = CUSTODY_HELD_BY_A + CUSTODY_OTHER_HANDS + CUSTODY_NOT_OUT
TRANSACTION_KINDS = ("ACTIVATION", "ORDINARY", "ECDSA")
RACE_WARNING = ("A private relay only reduces front-running: a builder that holds the exposed key "
                "can still include the tracked authorization first, or build a payload without the "
                "act that follows the write (l. 47, l. 252). The wallet prepares the payload again "
                "after every change of the head (32.2 rule 3 (b)).")
GAP_STATEMENT = ("NO_ONE_PAYLOAD_PATH: the caller states that no path gives one payload. Delivered "
                 "apart, the elements leave {count} tracked authorization(s) with an exposed key "
                 "includable between them, until the act that follows the {what} lands; anyone who "
                 "holds the carriers, A as a builder included, can include them first (spec "
                 "34.2 rule 1 (c); l. 47)")
NO_PAYLOAD_MEETS = ("No payload that the component can name meets 34.2 rule 1 (a) for this authorization: it "
                    "stays includable to A; the wallet sends a precursor that A already holds with its act "
                    "(34.2 rule 1 (b), last sentence), and a precursor that A does not hold waits as (g) states")
# (34.2 rule 1 (b), (e), (f); 37.3 rule 4; V25-W-1 (ii)).
NO_ROBUST_ACT = ("Every act of the owner's that the component can name for this authorization can be made to fail by a "
                 "member of K or O placed before it, after which the authorization stays includable to A (34.2 rule 1 "
                 "(e), (f)): no payload can meet rule 1 (a) (rule 1 (b)), and the wallet says so; the act named here is "
                 "the first that meets (a) and discharges the authorization when nothing pre-empts it")
# (spec 39.2 rule 1, the case of 38.3 'Recorded as open').
ACTIVATION_PREEMPTED = ("a member of K or O placed before the activation makes it fail -- by the account nonce, the "
                        "balance or a change of the commitment that it needs (BAD_ACTIVATION, l. 315) -- while the "
                        "tracked PI is includable after it, so the activation is no act for that PI (spec 39.2 "
                        "rule 1 (a), (b)); a sponsored write needs neither the account nonce, nor a's balance, nor a "
                        "commitment, and the writes through PI.migration_nonce apply after such a member (rule 1 (c))")
DISPLACED_PRECURSOR = ("a write at the precursor's migration_nonce that commits another key, which A holds, placed "
                       "before the payload displaces the precursor (check 6, l. 265) and makes the activation fail "
                       "(BAD_ACTIVATION, l. 315) while the PI is includable after it; the sponsored writes after the "
                       "precursor still apply (spec 39.2 rule 1 (b), (c))")
NO_SPONSORED_PATH = ("where the wallet has no sponsored path to offer, the writes are paid by a (fee mode 0) and are "
                     "the act only where a can pay each of them after every carrier of K or of the payload that can "
                     "take from a's balance has taken all that it allows, the writes' own carriers re-priced to their "
                     "caps included (l. 285, l. 3070; 37.3 rule 2; the caller's balance_covers_acts); otherwise every "
                     "act can be made to fail: the wallet says so, asks the owner for a sponsored fee choice and offers "
                     "the activation meanwhile (spec 39.2 rule 1 (d))")
# (spec 35.2 rule 1): the key of a write of a payload plan, read against its planning state S_i.
PLAN_RULE = "spec 35.2 rule 1"
KEY_SAME = "SAME_KEY_AS_ITS_PLANNING_STATE"          # a same-key write matches the pq_pk_commit of S_i (35.2 (b))
KEY_NEW = "NEW_KEY_SELECTED_AT_ITS_PLANNING_STATE"   # a key that x_i newly selects: e = m_i (35.2 (c))
KEY_IND = "KEY_NOT_DERIVED_FROM_THE_SEED"            # 31.2 rule 8 (b): C_ind
KEY_TRACKED = "KEY_OF_A_TRACKED_CARRIER"             # a carrier that exists already, with its own key and epoch
KEY_UNKNOWN = "KEY_NOT_KNOWN_AS_A_SEED_KEY"          # the device knows no epoch for it (the caller's key)
PREPARED_LATER = ("PREPARED_AGAINST_A_LATER_PLANNING_STATE: this write's nonce is above the head's, so it was "
                  "prepared against a state that acts before it in a payload leave, or against an anchor that a "
                  "reorganization removed; it leaves the device only in the payload with the acts before it, and "
                  "at a changed head that payload is re-planned as a whole, never sent from its remaining elements "
                  "(spec 35.2 rule 1 (d), (e); 31.2 rule 3)")


def _above_the_head(auth, head):
    """(35.2 rule 1 (e)): a write that only a later planning state (or a stale anchor) can carry: a PI
    above the head's migration_nonce, a 0x7d or a rotate above its account nonce."""
    return auth.nonce > (head.migration_nonce if auth.kind == "PI" else head.account_nonce)


def _digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def _bytes32(value, name):
    if not isinstance(value, bytes) or len(value) != 32:
        raise ValueError(f"{name} must contain 32 bytes")


def _custody_rank(custody):
    return 2 if custody in CUSTODY_HELD_BY_A else 1 if custody in CUSTODY_OTHER_HANDS else 0


def _merge_custody(old, new):
    """A carrier that was in other hands stays so: the custody only rises (or changes within a rank)."""
    return new if old is None or _custody_rank(new) >= _custody_rank(old) else old


def _held_by_a(record):
    return any(c in CUSTODY_HELD_BY_A for c in record.get("custody", {}).values())


def bundle_payload(case, *, kind="PI", activation_as_act=None, others_can_send=True, act=None, **extra):
    """What a one-payload remedy consists of, for the offer shown to the owner.

    Spec section 34.2 rule 1. FROZEN and OVERRIDE, case (a) (i): the write at the current
    migration_nonce first. For a PI, (f) chooses the act: the activation of the key the write
    commits where it meets (a) (decided by the search, `activation_as_act`), otherwise
    sponsored writes past PI.migration_nonce, with the activation once the writes are in a block.
    For a rotate (kind ROTATE), the activation of the key the write commits at the account nonce,
    then transactions through the rotate's account nonce, or (act
    WRITE_COMMITTING_C_IND) a write that commits a key other than the one that signs the rotate,
    then the activation of that key (34.2 rule 1 (f); 31.2 rule 8 (b)). LEGACY_BEFORE_T, case (a)
    (ii): a 0x7d first, then a sponsored 0x7e at migration_nonce 1 through the override gate (an
    activation after a 0x7d discharges nothing while the window is open, l. 113, l. 1160).
    ACCOUNT_NONCE, case (a) (iii) and (e): the activation (or an activating rotate, or, for an
    activated account, a transaction) at the account nonce first, then ordinary transactions through
    a tracked rotate's account nonce. RECOMMIT (spec 39.2 rule 1 (c)): no precursor;
    where a member placed before the activation of the current key can make it fail, the sponsored
    same-key writes through PI.migration_nonce, with the activation once they are in a block.
    """
    if activation_as_act is None:
        activation_as_act = case in ("PRE_T_LEGACY", "FROZEN") or (case == "OVERRIDE" and not others_can_send)
    if case in ("PRE_T_LEGACY", "FROZEN", "OVERRIDE", "LEGACY_BEFORE_T") and kind == "ROTATE":
        first = ("ENROLLMENT_0x7D_AT_ACCOUNT_NONCE" if case == "LEGACY_BEFORE_T"
                 else "WRITE_AT_CURRENT_MIGRATION_NONCE")
        if act == "WRITE_COMMITTING_C_IND":
            first = "WRITE_COMMITTING_A_KEY_NOT_DERIVED_FROM_THE_SEED_AT_THE_CURRENT_MIGRATION_NONCE"
            act = "ACTIVATION_OF_THE_KEY_NOT_DERIVED_FROM_THE_SEED"
            extra.setdefault("why", "the key that the write at the current migration_nonce commits signs this rotate, "
                                    "and a member of K or O, or a builder that splits the payload, carries a to its "
                                    "account nonce first; a write of another key keeps it unincludable "
                                    "(34.2 rule 1 (f); 31.2 rule 8 (b), with its warning and backup)")
            extra.setdefault("precursor_commits", "C_IND")
        else:
            act = "ACTIVATION_OF_THE_KEY_THE_WRITE_COMMITS_AT_THE_ACCOUNT_NONCE"
        then = [act, "TRANSACTIONS_THROUGH_THE_TRACKED_ACCOUNT_NONCE"]
        fee_path = "SPONSOR_WHERE_THE_FEE_PATH_ALLOWS"
        extra.setdefault("owner_can_send_before_the_write", False)
        extra.setdefault("time_bound", None)            # a rotate has none (32.2 rule 6)
    elif case in ("PRE_T_LEGACY", "FROZEN", "OVERRIDE") and activation_as_act:
        first = "WRITE_AT_CURRENT_MIGRATION_NONCE"
        act = "ACTIVATION_OF_THE_KEY_THE_WRITE_COMMITS"
        then = [act, "SPONSORED_WRITES_PAST_PI_MIGRATION_NONCE"]
        fee_path = "SPONSOR_WHERE_THE_FEE_PATH_ALLOWS"
        extra.setdefault("act_where", "a can pay the activation's gas after the precursor has taken all that its "
                                      "carrier allows; no member of K or O placed before the payload takes the "
                                      "account nonce or the balance (34.2 rule 1 (f))")
        extra.setdefault("otherwise", "SPONSORED_WRITES_PAST_PI_MIGRATION_NONCE")
    elif case in ("PRE_T_LEGACY", "FROZEN", "OVERRIDE"):
        first = "WRITE_AT_CURRENT_MIGRATION_NONCE"
        act = "SPONSORED_WRITES_PAST_PI_MIGRATION_NONCE"
        then = [act]
        fee_path = "SPONSOR"
        extra.setdefault("activation_as_act", False)
        extra.setdefault("why", "a member of K or O placed before the payload can take the account nonce or the balance "
                                "that an activation needs while the write still applies, and a builder then pops the "
                                "activation (l. 252, l. 314-315, l. 1232); a sponsored write depends on neither "
                                "(34.2 rule 1 (a) (v), (f))")
        extra.setdefault("then_once_in_a_block", "ACTIVATION_OF_THE_KEY_THE_WRITES_COMMIT")
    elif case == "RECOMMIT":
        # (spec 39.2 rule 1 (c)): no precursor; a member placed before the activation can make it fail
        # while the PI is includable after it, so the act is the sponsored same-key writes past PI.migration_nonce.
        first = "SPONSORED_SAME_KEY_WRITE_AT_THE_CURRENT_MIGRATION_NONCE"
        act = "SPONSORED_WRITES_PAST_PI_MIGRATION_NONCE"
        then = [act]
        fee_path = "SPONSOR"
        extra.setdefault("activation_as_act", False)
        extra.setdefault("why", ACTIVATION_PREEMPTED)
        extra.setdefault("then_once_in_a_block", "ACTIVATION_OF_THE_KEY_THE_WRITES_COMMIT")
    elif case == "LEGACY_BEFORE_T":
        first = "ENROLLMENT_0x7D_AT_ACCOUNT_NONCE"
        act = "SPONSORED_WRITES_PAST_PI_MIGRATION_NONCE"
        then = [act]
        fee_path = "SPONSOR"
        extra.setdefault("activation_discharges", False)
        extra.setdefault("act_starts_with", "0x7E_AT_MIGRATION_NONCE_1_THROUGH_THE_OVERRIDE_GATE")
        extra.setdefault("example", "the same-key early finalisation of l. 327 (31.2 rule 8 (a))")
        extra.setdefault("why", "the holder of a's exposed secp256k1 key can send a transaction of a, or its own "
                                "0x7d, until the 0x7d lands (l. 45, l. 1213); a sponsored 0x7e applies after "
                                "either (34.2 rule 1 (f))")
        extra.setdefault("then_once_in_a_block", "ACTIVATION_OF_THE_KEY_THE_WRITES_COMMIT")
    elif case == "ACCOUNT_NONCE":
        first = {"ACTIVATED": "TRANSACTION_AT_ACCOUNT_NONCE",
                 "UNACTIVATED_PQ": "ACTIVATION_OR_ACTIVATING_ROTATE_AT_ACCOUNT_NONCE",
                 # Before T an ECDSA transaction; a frozen account sends none until a recovery
                 # write and the activation have landed.
                 "LEGACY": "TRANSACTION_OF_THE_LEGACY_ACCOUNT_AT_ITS_NONCE"}[extra.pop("sender")]
        act = "TRANSACTIONS_THROUGH_THE_TRACKED_ACCOUNT_NONCE"
        then = [act]
        fee_path = "OWN_FUNDS"
        kind = "ROTATE"                                 # the acts answer a tracked rotate
        extra.setdefault("time_bound", None)            # a rotate has none (32.2 rule 6)
    else:
        raise ValueError("unknown bundle case")
    return {"one_payload": True, "case": case, "kind": kind, "first": first, "act": act, "then_one_of": then,
            "route": "PRIVATE_RELAY", "fee_path": fee_path, "race": True, "warning": RACE_WARNING,
            "derived_by": "spec 34.2 rule 1 (a): the search of reachability.py", **extra}


@dataclass(frozen=True)
class Account:
    chain_id: int
    genesis_hash: str
    address: str

    def __post_init__(self):
        _uint(self.chain_id, (1 << 256) - 1, "chain ID")
        for name, size in (("genesis_hash", 32), ("address", 20)):
            object.__setattr__(self, name, _hex(getattr(self, name), size, name))

    @property
    def key(self):
        return _digest(asdict(self))


@dataclass(frozen=True)
class AccountState:
    account: Account
    block_hash: str
    number: int
    timestamp: int
    migration_nonce: int
    account_nonce: int
    mode: str
    activated: bool
    commitment: bytes | None
    fork_time: int | None
    override_window: int
    enrolled_at: int = 0
    protocol_time: int | None = None
    legacy_seed_proof_from_t0: bool = False
    code_kind: str | None = None

    def __post_init__(self):
        if not isinstance(self.account, Account):
            raise ValueError("account required")
        object.__setattr__(self, "block_hash", _hex(self.block_hash, 32, "block hash"))
        for name in ("number", "timestamp", "migration_nonce", "account_nonce", "override_window", "enrolled_at"):
            _uint(getattr(self, name), UINT64_MAX, name)
        if self.fork_time is not None:
            _uint(self.fork_time, UINT64_MAX, "fork time")
        if self.protocol_time is not None:
            _uint(self.protocol_time, UINT64_MAX, "protocol time")
        if type(self.legacy_seed_proof_from_t0) is not bool:
            raise ValueError("legacy seed-proof configuration must be boolean")
        if self.code_kind is not None and self.code_kind not in CODE_KINDS:
            raise ValueError("invalid account code metadata")
        if self.mode not in ("LEGACY", "PQ_BY_ENROLL", "PQ_BY_PROOF", "PQ_NATIVE"):
            raise ValueError("unknown account mode")
        if type(self.activated) is not bool or (self.mode == "LEGACY" and self.activated):
            raise ValueError("invalid activation state")
        if self.commitment is not None:
            _bytes32(self.commitment, "commitment")
        if self.mode != "LEGACY" and self.commitment is None:
            raise ValueError("PQ state needs its commitment")

    @property
    def effective_code_kind(self):
        return self.code_kind if self.code_kind is not None else ("PQ_MARKER" if self.activated else "EMPTY")

    @property
    def deadline(self):
        # None is unscheduled, not zero. The addition is a mathematical integer.
        return None if self.fork_time is None else max(self.enrolled_at, self.fork_time) + self.override_window

    @property
    def binding_final(self):
        return ((self.mode == "PQ_BY_PROOF" and self.activated) or self.mode == "PQ_NATIVE"
                or (self.mode == "PQ_BY_ENROLL" and self.deadline is not None
                    and self.timestamp >= self.deadline))

    def to_dict(self):
        d = asdict(self)
        d["commitment"] = None if self.commitment is None else self.commitment.hex()
        d["code_kind"] = self.effective_code_kind
        return d

    @classmethod
    def from_dict(cls, d):
        d = dict(d)
        d["account"] = Account(**d["account"])
        d["commitment"] = None if d["commitment"] is None else bytes.fromhex(d["commitment"])
        return cls(**d)


def state_gate(state: AccountState):
    """The gate of check 5 open at `state` (l. 260-263, l. 1159-1161), or None.

    An unscheduled T leaves the override deadline infinite. The v1.31 LEGACY
    gate requires its configuration flag and an authenticated T0 (§43.2).
    """
    return model_gate(state_of(state), state.timestamp,
                      Config(state.fork_time, state.override_window, state.protocol_time,
                             state.legacy_seed_proof_from_t0))


def legacy_before_T(state: AccountState):
    """A LEGACY head where ECDSA enrollment remains possible, independently of the seed-proof gate."""
    if ((state.legacy_seed_proof_from_t0 and state.protocol_time is None)
            or (state.protocol_time is not None and state.timestamp < state.protocol_time)):
        return False
    return state.mode == "LEGACY" and (state.fork_time is None or state.timestamp < state.fork_time)


def sender_class(state: AccountState):
    """Which transaction the account can send at its account nonce (l. 313-317)."""
    if state.activated:
        return "ACTIVATED"
    return "LEGACY" if state.mode == "LEGACY" else "UNACTIVATED_PQ"


@dataclass(frozen=True)
class FinalizedView:
    state: AccountState
    previous_finalized_hash: str | None = None


@dataclass(frozen=True)
class Authorization:
    account: Account
    kind: str
    nonce: int
    commitment: bytes
    pi: bytes | None = None
    expiry: int | None = None
    activating: bool = False
    signer_commitment: bytes | None = None
    epoch: int | None = None

    def __post_init__(self):
        if not isinstance(self.account, Account) or self.kind not in ("PI", "ROTATE", "ENROLL"):
            raise ValueError("invalid authorization type/account")
        _uint(self.nonce, UINT64_MAX, "authorization nonce")
        _bytes32(self.commitment, "target commitment")
        if type(self.activating) is not bool:
            raise ValueError("activating must be boolean")
        if self.epoch is not None:
            _uint(self.epoch, UINT32_MAX, "epoch")
        if self.kind == "PI":
            # (31.2 rule 10 (e)): a PI follows the layout of its named version, 169 or 198 bytes.
            if not isinstance(self.pi, bytes) or len(self.pi) not in PI_LAYOUT_BYTES.values():
                raise ValueError("complete PI of layout 1 (169 bytes) or layout 2 (198 bytes) required")
            expected = (int.from_bytes(self.pi[:32], "big"), self.pi[64:84].hex(),
                        int.from_bytes(self.pi[84:92], "big"), self.pi[93:125],
                        int.from_bytes(self.pi[129:137], "big"))
            if expected != (self.account.chain_id, self.account.address, self.nonce, self.commitment, self.expiry):
                raise ValueError("PI/account/nonce/expiry binding mismatch")
            if self.activating or self.signer_commitment is not None:
                raise ValueError("PI has no activation signer")
        else:
            if self.pi is not None or self.expiry is not None:
                raise ValueError("signed authorization has no PI/expiry")
            if self.kind == "ROTATE":
                _bytes32(self.signer_commitment, "rotate signer commitment")
            elif self.activating or self.signer_commitment is not None:
                raise ValueError("enrollment has no PQ activation signer")

    @classmethod
    def from_pi(cls, account, pi, *, epoch=None):
        if not isinstance(pi, bytes) or len(pi) not in PI_LAYOUT_BYTES.values():
            raise ValueError("complete PI of layout 1 (169 bytes) or layout 2 (198 bytes) required")
        return cls(account, "PI", int.from_bytes(pi[84:92], "big"), pi[93:125],
                   pi=pi, expiry=int.from_bytes(pi[129:137], "big"), epoch=epoch)

    @property
    def layout(self):
        """The PI's layout (1: 169 bytes, 16.3; 2: 198 bytes, section 19.2), None for a 0x7c or 0x7d."""
        return None if self.kind != "PI" else (1 if len(self.pi) == 169 else 2)

    @property
    def fee_mode(self):
        """A PI's own fee_mode (byte 169, section 19.2), None for a 0x7c or 0x7d.

        Mode 0 is carried only by an unsponsored single paid by a (l. 266); modes 1-3 only by a
        sponsored carrier or a 0x7f entry; modes 0, 1 and 3 can take up to max_account_fee (l. 273,
        l. 3070, l. 3045-3047). A layout-1 PI has no fee mode (None); any carrier of its version can
        carry it and any sponsor can collect up to max_account_fee from it (section 18.24 rows 1-6, l. 285).
        """
        return None if self.kind != "PI" or self.layout == 1 else self.pi[169]

    @property
    def group_id(self):
        return _digest([asdict(self.account), self.kind, self.pi.hex() if self.pi is not None else self.nonce])

    @property
    def variant_id(self):
        d = self.to_dict()
        d.pop("epoch")  # Learning the derivation epoch does not create a new authorization.
        return _digest(d)

    def to_dict(self):
        d = asdict(self)
        for name in ("commitment", "pi", "signer_commitment"):
            d[name] = None if getattr(self, name) is None else getattr(self, name).hex()
        return d

    @classmethod
    def from_dict(cls, d):
        d = dict(d)
        d["account"] = Account(**d["account"])
        for name in ("commitment", "pi", "signer_commitment"):
            d[name] = None if d[name] is None else bytes.fromhex(d[name])
        return cls(**d)


@dataclass(frozen=True)
class Transaction:
    """A transaction of `a` that is no binding authorization, as a member of K (34.2 rule 1 (a)).

    ACTIVATION: an activating 0x7c without rotate, revealing the key of `commitment` at
    `account_nonce`; ORDINARY: a 0x7c of an activated account signed by the key of `commitment`;
    ECDSA: a secp256k1 transaction of a LEGACY account. Once one has left a device (sent, exported,
    handed to a relay) or been seen in a block or pool, anyone who holds it can include it again
    (l. 47, l. 9929): the owner's activation A0 of vectors V22-W-5 and V22-W-6 is one.
    """
    account: Account
    kind: str
    account_nonce: int
    commitment: bytes | None = None

    def __post_init__(self):
        if not isinstance(self.account, Account) or self.kind not in TRANSACTION_KINDS:
            raise ValueError("invalid transaction type/account")
        _uint(self.account_nonce, UINT64_MAX, "transaction account nonce")
        if self.kind == "ECDSA":
            if self.commitment is not None:
                raise ValueError("an ECDSA transaction names no PQ key")
        else:
            _bytes32(self.commitment, "transaction key commitment")

    @property
    def tx_id(self):
        return _digest(["transaction", self.to_dict()])

    def to_dict(self):
        d = asdict(self)
        d["commitment"] = None if self.commitment is None else self.commitment.hex()
        return d

    @classmethod
    def from_dict(cls, d):
        d = dict(d)
        d["account"] = Account(**d["account"])
        d["commitment"] = None if d["commitment"] is None else bytes.fromhex(d["commitment"])
        return cls(**d)

    def step(self, label, ident):
        return Step(self.kind, self.account_nonce, self.commitment, label=label, ident=ident)


def end_reason(auth: Authorization, state: AccountState):
    """Evaluate section 32.2 rule 2; only a finalized caller may persist this."""
    if auth.account != state.account:
        raise ValueError("authorization/state account mismatch")
    if auth.kind == "PI":
        if state.migration_nonce > auth.nonce:
            return "MIGRATION_NONCE_CONSUMED"
        if state.binding_final:
            return "BINDING_FINAL"
        if state.timestamp > auth.expiry:
            return "PI_EXPIRED"
    else:
        if state.account_nonce > auth.nonce:
            return "ACCOUNT_NONCE_CONSUMED"
        if auth.kind == "ROTATE" and auth.activating and state.binding_final and state.activated:
            return "FINAL_AND_ACTIVATED"
        if auth.kind == "ENROLL":
            if state.mode != "LEGACY":
                return "NO_LONGER_LEGACY"
            if state.fork_time is not None and state.timestamp >= state.fork_time:
                return "ENROLLMENT_CLOSED"
    return None


def binding_conditions_allow(auth: Authorization, state: AccountState):
    """Necessary binding conditions only; NOT signature/proof/fee admission.

    Used conservatively to withhold automatic resubmission or export that could
    revive a known dangerous authorization. The normal client validator is still
    required. A PI needs its own nonce, an unexpired expiry and an open gate of
    check 5 (state_gate; an unscheduled T leaves the override gate open). A rotate binds its key only where final(a) and activated(a) hold after the 0x7c's
    activation, else its frame reverts with NOT_FINAL (l. 328), for a non-activating
    rotate as for an activating one.
    """
    if auth.account != state.account:
        raise ValueError("authorization/state account mismatch")
    if auth.kind == "PI":
        return (state.migration_nonce == auth.nonce and state.timestamp <= auth.expiry
                and state_gate(state) is not None)
    if state.account_nonce != auth.nonce:
        return False
    if auth.kind == "ENROLL":
        return legacy_before_T(state)
    if state.commitment != auth.signer_commitment:
        return False
    return ((not state.activated and (state.mode == "PQ_BY_PROOF" or state.binding_final))
            if auth.activating else (state.activated and state.binding_final))


def single_write_preview(auth: Authorization, state: AccountState) -> AccountState:
    """The state after `auth` alone, applied at `state`; `state` itself if it cannot apply.

    Guard gap (b): the guard evaluates this preview, which it computes itself, so a
    caller cannot submit the end state of a write together with the act that follows
    it as the preview of the write alone. The transitions are those of l. 191-194
    (0x7d), l. 272-276 (0x7e or applied 0x7f entry) and l. 321/l. 328 (a 0x7c that
    calls rotate, activating or not). The timestamp stays the head's: an included
    0x7d's enrolled_at is a later timestamp, which only moves deadline(a) later.
    """
    if auth.account != state.account:
        raise ValueError("authorization/state account mismatch")
    if not binding_conditions_allow(auth, state):
        return state
    if auth.kind == "PI":
        return replace(state, mode="PQ_BY_PROOF", migration_nonce=state.migration_nonce + 1,
                       commitment=auth.commitment, activated=False, code_kind="EMPTY")
    if auth.kind == "ENROLL":
        return replace(state, mode="PQ_BY_ENROLL", migration_nonce=state.migration_nonce + 1,
                       commitment=auth.commitment, activated=False, code_kind="EMPTY",
                       account_nonce=state.account_nonce + 1, enrolled_at=state.timestamp)
    return replace(state, migration_nonce=state.migration_nonce + 1, commitment=auth.commitment,
                   activated=True, account_nonce=state.account_nonce + 1, code_kind="PQ_MARKER")


def activation_preview(state: AccountState):
    """The state after a lone activation (an activating 0x7c without rotate) at `state`, or None.

    l. 315, l. 321: a PQ account whose code is empty reveals the key of its commitment,
    and its account nonce advances. The override gate has no code condition (l. 1160),
    so the activation of a PQ_BY_ENROLL account leaves that gate open.
    """
    if state.mode not in ("PQ_BY_PROOF", "PQ_BY_ENROLL") or state.activated:
        return None
    return replace(state, activated=True, account_nonce=state.account_nonce + 1, code_kind="PQ_MARKER")


def _lone_preview(auth, head, after):
    if not isinstance(head, AccountState):
        raise ValueError("head AccountState required")
    if not isinstance(auth, Authorization) or auth.account != head.account:
        raise ValueError("preview account mismatch")
    preview = single_write_preview(auth, head)
    if after is not None:
        if not isinstance(after, AccountState) or after.account != head.account:
            raise ValueError("preview account mismatch")
        for name in ("block_hash", "number", "timestamp", "fork_time", "override_window",
                     "protocol_time", "legacy_seed_proof_from_t0"):
            if getattr(head, name) != getattr(after, name):
                raise ValueError("preview must use the same head and active configuration")
        if after.to_dict() != preview.to_dict():
            raise ValueError("PREVIEW_NOT_CANDIDATE_ALONE: the guard evaluates the state after this "
                             "write alone; a write with the act that follows it is a OnePayloadBundle")
    return preview


class RevivalWarning(ValueError):
    """A write or an activation would make a tracked authorization with an exposed key includable.

    32.2 rule 3 (e). Nothing was recorded, signed
    or delivered. `remedy` names the first act to take instead and `payload` describes a
    one-payload remedy. Where the remedy is not a bundle, `token`, passed back as
    confirm_revival after the owner's explicit confirmation, lets the write leave alone.
    Where it is ONE_PAYLOAD_BUNDLE (spec 34.2 rule 1 (c)), no token is issued until
    the caller states that no path gives one payload (no_one_payload_path=True); the
    warning then states the gap (`gap`), and only its token confirms a lone delivery.
    Where it is HOLD_FRESH_PRECURSOR (34.2 rule 1 (g)), no token is ever issued:
    the fresh write leaves neither alone nor in a bundle until the tracked authorization
    meets a condition of 32.2 rule 2, and `payload` shows the time left. `witness`
    is a run of 34.2 rule 1 (a) in which the write makes the first revived authorization
    includable (the labels of the members and the payload, in order).
    """

    def __init__(self, revived, token, remedy, *, payload=None, gap=None, what="write", witness=None):
        self.revived = revived
        self.token = token
        self.remedy = remedy
        self.payload = payload
        self.gap = gap
        self.witness = witness
        head = (f"REVIVES_EXPOSED_AUTHORIZATION: this {what} alone would make {len(revived)} tracked "
                f"authorization(s) with an exposed key includable; remedy {remedy}")
        if remedy == HOLD_FRESH_PRECURSOR:
            message = (f"{head}: no carrier of a write at this migration_nonce that A holds can be included after the "
                       "head, and A's members reach no state in which the tracked PI is includable, so this write "
                       "would give A, as a builder that receives it, the one piece that it lacks; the wallet holds it "
                       "back until a chain-finalized block meets a condition of 32.2 rule 2 (spec 34.2 rule 1 "
                       "(g)); no confirmation sends it")
        elif gap is not None:
            message = f"{head}; {gap}; explicit owner confirmation of this gap required"
        elif remedy == ONE_PAYLOAD_BUNDLE:
            message = (f"{head}: offer it with the act that follows it as one payload; it leaves alone "
                       "only where no path gives one payload (no_one_payload_path=True), after the "
                       "owner confirms the gap that the wallet then states")
        else:
            message = f"{head}; explicit owner confirmation required"
        super().__init__(message)


class SplitDeliveryWarning(ValueError):
    """A bundle delivered split would leave a tracked exposed authorization includable between its elements.

    Raised by export_bundle(no_one_payload_path=True) (spec 34.2 rule 1 (c)).
    `token`, bound to the bundle and its head, confirms the split
    after the owner has seen the stated gap.
    """

    def __init__(self, revived_between, token, gap):
        self.revived_between = revived_between
        self.token = token
        self.gap = gap
        super().__init__(f"{gap}; explicit owner confirmation of this gap required")


class MoveAwayWarning(ValueError):
    """A rotate signed by a key known exposed: a move away from it needs the owner's explicit confirmation.

    31.2 rule 7 (b): the wallet signs with a recorded key only for a write that moves the
    account away from that key, and only on the owner's explicit confirmation.
    `token` binds the head and the rotate.
    """

    def __init__(self, token):
        self.token = token
        super().__init__("SIGNER_KEY_EXPOSED: this rotate is signed by a key known exposed; it moves the "
                         "account away from that key only on the owner's explicit confirmation "
                         "(31.2 rule 7 (b)); pass the token as confirm_move_away")


class EndedTrackings(list):
    """observe_finalized's result: the (group, variant, reason) triples whose tracking ended.

    It compares equal to the plain list. `notices` holds what the chain-finalized state
    revealed: a stealth enrollment (spec 34.2 rule 2). (spec 35.3 rule 1): each triple is one carrier of its authorization, and `indexes_ended`
    lists the rotate authorizations (a, n) whose every known carrier has ended at this block
    ({"group", "account_nonce", "carriers"}); one whose carriers have not all ended stays tracked.
    """

    def __init__(self, items=(), notices=(), indexes_ended=()):
        super().__init__(items)
        self.notices = list(notices)
        self.indexes_ended = list(indexes_ended)


@dataclass(frozen=True)
class PayloadElement:
    """One transaction of a one-payload bundle, in payload order.

    WRITE carries a binding authorization (a PI's 0x7e, a 0x7d, or a 0x7c that calls
    rotate). ACTIVATION is a 0x7c that reveals the key of `commitment` at account nonce
    `account_nonce` (l. 315); TRANSACTION is an ordinary 0x7c of an activated account at
    `account_nonce`, signed by the key of `commitment`
    (when it is None, by the key that the payload's earlier elements leave current). Neither
    writes a binding; both are recorded as members of K once they leave the device.
    (31.2 rule 10 (e)): `sponsored` says whether a PI's carrier is a sponsored one. Under layout 2 the PI's
    fee mode says it (mode 0 unsponsored, 1-3 sponsored; a value that disagrees is refused, section 19.2 table);
    under layout 1 the PI does not, and an element whose carrier class is unstated (None) counts as paid by a.
    """
    kind: str
    carrier: bytes
    authorization: Authorization | None = None
    commitment: bytes | None = None
    account_nonce: int | None = None
    sponsored: bool | None = None

    def __post_init__(self):
        if self.kind not in ("WRITE", "ACTIVATION", "TRANSACTION"):
            raise ValueError("payload element kind is WRITE, ACTIVATION or TRANSACTION")
        if not isinstance(self.carrier, bytes) or not self.carrier:
            raise ValueError("nonempty raw carrier bytes required")
        if self.kind == "WRITE":
            if not isinstance(self.authorization, Authorization) or self.commitment is not None \
                    or self.account_nonce is not None:
                raise ValueError("a WRITE element carries its authorization only")
            if self.sponsored is not None:
                if type(self.sponsored) is not bool or self.authorization.kind != "PI":
                    raise ValueError("only a PI's carrier is sponsored or not")
                mode = self.authorization.fee_mode
                if mode is not None and self.sponsored != (mode != 0):
                    raise ValueError("NON_CANONICAL_ENCODING: a mode-0 PI is carried only unsponsored and a mode 1-3 PI "
                                     "only sponsored (section 19.2 table)")
            return
        if self.sponsored is not None:
            raise ValueError("only a PI's carrier is sponsored or not")
        if self.authorization is not None:
            raise ValueError(f"an {self.kind} element carries no binding authorization")
        if self.kind == "ACTIVATION" or self.commitment is not None:
            _bytes32(self.commitment, "element key commitment")
        _uint(self.account_nonce, UINT64_MAX, "element account nonce")

    @property
    def is_0x7c(self):
        return self.kind in ("ACTIVATION", "TRANSACTION") or (
            self.kind == "WRITE" and self.authorization.kind == "ROTATE")

    @property
    def paid_by_a(self):
        """A PI's carrier that a pays (an unsponsored single): its fee mode 0, or, under layout 1, a carrier
        not stated to be sponsored."""
        mode = self.authorization.fee_mode
        return mode == 0 if mode is not None else self.sponsored is not True

    @property
    def identity(self):
        if self.kind == "WRITE":
            return ["WRITE", self.authorization.group_id, self.authorization.variant_id]
        return [self.kind, hashlib.sha256(self.carrier).hexdigest()]


@dataclass(frozen=True)
class OnePayloadBundle:
    """Review item 3.1: an act that needs a precursor, travelling with that precursor.

    The elements travel as ONE payload, in order, through a private relay (a builder
    bundle interface): the public pool would split them, and its nonce-ordered subpool
    rejects a 0x7c whose sender class does not yet hold at the head (l. 4130), while a
    builder evaluates each element against the in-payload post-state (l. 1232).
    Shapes: a binding write first (a 0x7e at the current migration_nonce, a 0x7d, or a
    0x7c that calls rotate, activating or not), then the act that follows it; or
    an activation first, followed only by 0x7c elements
    (ordinary transactions or rotates) through a tracked rotate's account nonce.
    Who pays a 0x7e is its PI's fee_mode (section 19.2), never this
    label. The default label is derived from the PIs (SPONSOR when every PI has fee mode 1-3,
    OWN_FUNDS when every one has mode 0 or the bundle carries none, MIXED otherwise); a caller's
    label is kept for the report, and the analysis reads each PI's own fee_mode whatever it says
    (fee_mode 0: an unsponsored single, paid by a; `fee_path_from_fee_modes` in the analysis).
    """
    head: AccountState
    elements: tuple
    fee_path: str | None = None
    route: str = "PRIVATE_RELAY"

    def __post_init__(self):
        if not isinstance(self.head, AccountState):
            raise ValueError("bundle head AccountState required")
        object.__setattr__(self, "elements", tuple(self.elements))
        if len(self.elements) < 2 or not all(isinstance(e, PayloadElement) for e in self.elements):
            raise ValueError("a one-payload bundle is a precursor and the act that follows it")
        first = self.elements[0]
        if first.kind == "TRANSACTION":
            raise ValueError("a one-payload bundle starts with its binding write, or with the activation "
                             "at the account nonce")
        if first.kind == "ACTIVATION" and not all(e.is_0x7c for e in self.elements[1:]):
            raise ValueError("an activation-first bundle carries only 0x7c transactions after the activation")
        if self.fee_path is None:
            object.__setattr__(self, "fee_path", self.fee_path_from_fee_modes)
        if self.fee_path not in FEE_PATHS:
            raise ValueError("unknown fee path")
        if self.fee_path == "SPONSOR" and not any(e.kind == "WRITE" and e.authorization.kind == "PI"
                                                  for e in self.elements):
            raise ValueError("a sponsor pays only a 0x7e; a bundle of 0x7c and 0x7d transactions is OWN_FUNDS")
        if self.route not in ONE_PAYLOAD_ROUTES:
            raise ValueError("SPLIT_ROUTE_REFUSED: a one-payload bundle needs a private relay or builder "
                             "interface; the public mempool delivers its elements separately. Where no "
                             "path gives one payload, export_bundle(no_one_payload_path=True) states the "
                             "gap and asks the owner to confirm a split delivery")

    @property
    def fee_path_from_fee_modes(self):
        paid = [e.paid_by_a for e in self.elements if e.kind == "WRITE" and e.authorization.kind == "PI"]
        return ("OWN_FUNDS" if not paid or all(paid)
                else "SPONSOR" if not any(paid) else "MIXED")

    @property
    def bundle_id(self):
        return _digest(["one-payload-bundle", [e.identity for e in self.elements]])


class _Model:
    """Spec 34.2 rule 1 (a)-(g) at one observed head, decided by reachability.search.

    K: every carrier of each tracked live binding authorization (whatever its custody; an extra
    member can only add runs to the condition) and every recorded live transaction of `a`. K_A, the
    members that A holds: those with a carrier whose custody is CUSTODY_HELD_BY_A. O: a 0x7c or
    rotate signed by a key of `a` that A holds (a key known exposed, the key of an enrollment that
    the device did not create, A's own key), ECDSA and A's own 0x7d while A holds a's secp256k1 key,
    and the carriers formed from the payload's 0x7e. Starts: the head, F and every seen block above
    F. Targets: the tracked live authorizations whose key is exposed.
    """

    def __init__(self, tracker, s, epochs, head):
        self.tracker, self.s, self.epochs, self.head = tracker, s, epochs, head
        self.cfg = Config(head.fork_time, head.override_window, head.protocol_time, head.legacy_seed_proof_from_t0)
        self.t0 = head.timestamp + tracker.slot
        self.hs = state_of(head)
        account = head.account
        f = s["finalized"].get(account.key)
        self.f = None if f is None else AccountState.from_dict(f)
        starts = [self.hs]
        if self.f is not None:
            starts.append(state_of(self.f))
        for raw in s["seen"].get(account.key, {}).values():
            seen = AccountState.from_dict(raw)
            if self.f is None or seen.number > self.f.number:
                starts.append(state_of(seen))
        self.starts = tuple(dict.fromkeys(starts))
        self.k, self.targets, self.auths, self.order = [], {}, {}, []
        for gid, vid, a, r in tracker._live_records(s, account):
            key = (gid, vid)
            # (35.3 rule 1): each carrier of a rotate index (a, n) is its own member, labelled as such, and a
            # target only where the key that it binds is exposed; an ended carrier is no member.
            label = f"TRACKED_{a.kind}_{gid[:12]}" + (f"_CARRIER_{vid[:8]}" if a.kind == "ROTATE" else "")
            step = self.step_of(a, label, f"K:{gid}:{vid}")
            self.k.append((key, step, _held_by_a(r)))
            self.auths[key] = a
            if tracker._binds_exposed_key(s, a, epochs):
                self.targets[key] = step
                self.order.append(key)
        for txid, r in s["transactions"].items():
            tx = Transaction.from_dict(r["transaction"])
            if tx.account != account or r["ended"] is not None:
                continue
            self.k.append((("TX", txid), tx.step(f"KNOWN_{tx.kind}_AT_ACCOUNT_NONCE_{tx.account_nonce}", f"T:{txid}"),
                           _held_by_a(r)))
        candidates = {st.commitment for st in self.starts}
        for _, step, _ in self.k:
            candidates.update((step.commitment, step.signer))
        candidates.update(bytes.fromhex(h) for h in s["links"])
        candidates.update(bytes.fromhex(h) for h in s["exposed"].get(account.key, {}))
        candidates.discard(None)
        self.exposed = {c for c in candidates if tracker._key_exposed(s, c, epochs)}
        self.a_signs = {c: "EXPOSED_KEY_0x7C_AT_THE_ACCOUNT_NONCE" for c in self.exposed}
        stealth = [st.commitment for st in self.starts if st.mode == "PQ_BY_ENROLL"]
        stealth += [step.commitment for _, step, _ in self.k if step.cls == "ENROLL"]
        for c in stealth:
            if c is not None and not tracker._own_commitment(s, c):
                self.a_signs.setdefault(c, "ENROLLED_KEY_0x7C_AT_THE_ACCOUNT_NONCE")
        self.a_signs[A_KEY] = "A_KEY_0x7C_AT_THE_ACCOUNT_NONCE"
        # Whether A holds a's secp256k1 key, by evidence (34.2 rule 1 (g)): a tracked 0x7d or a known
        # ECDSA transaction of a, a LEGACY state with a nonzero nonce, or the caller's statement. The
        # condition of (a) assumes it held in every case (it can only add runs).
        self.published = (account.key in s["published"]
                          or any(step.cls in ("ENROLL", "ECDSA") for _, step, _ in self.k)
                          or any(st.mode == "LEGACY" and st.an > 0 for st in self.starts))
        signers = {step.signer for _, step, _ in self.k if step.cls == "ROTATE"}
        signers |= {step.commitment for _, step, _ in self.k if step.cls in ("ACTIVATION", "ORDINARY")}
        self.rotate_targets = (A_KEY,) + tuple(sorted(c for c in signers if c in self.a_signs and c != A_KEY))
        nonces = [st.an for st in self.starts] + [step.nonce for _, step, _ in self.k if step.cls != "WRITE"]
        self.max_an = max(nonces) + 1
        self._cache = {}

    # ------------------------------------------------------------------ building blocks
    @staticmethod
    def step_of(a, label="", ident="", sponsored=None):
        if a.kind == "PI":
            mode = a.fee_mode
            if a.layout == 1:
                # (31.2 rule 10 (e)): a layout-1 PI names no fee mode. Any carrier of its version can carry it
                # and any sponsor can collect up to max_account_fee from it (section 18.24 rows 1-6, l. 285), so every
                # one of its carriers can take balance; a payload's own carrier is paid by a unless it is stated to
                # be sponsored (PayloadElement.sponsored).
                a_paid, takes = sponsored is not True, True
            else:
                a_paid, takes = mode == 0, mode in (0, 1, 3)
            return Step("WRITE", a.nonce, a.commitment, expiry=a.expiry, a_paid=a_paid,
                        takes_balance=takes, version=int.from_bytes(a.pi[125:129], "big"),
                        label=label, ident=ident)
        if a.kind == "ENROLL":
            return Step("ENROLL", a.nonce, a.commitment, label=label, ident=ident)
        return Step("ROTATE", a.nonce, a.commitment, signer=a.signer_commitment, activating=a.activating,
                    label=label, ident=ident)

    def element_steps(self, bundle):
        """The bundle's elements as steps; a TRANSACTION without a key is signed by the key current there."""
        steps, st = [], self.hs
        for index, e in enumerate(bundle.elements):
            if e.kind == "WRITE":
                step = self.step_of(e.authorization, f"PAYLOAD_{index}_{e.authorization.kind}", f"E:{index}",
                                    sponsored=e.sponsored)
            elif e.kind == "ACTIVATION":
                step = Step("ACTIVATION", e.account_nonce, e.commitment, label=f"PAYLOAD_{index}_ACTIVATION",
                            ident=f"E:{index}")
            else:
                signer = e.commitment if e.commitment is not None else st.commitment
                step = Step("ORDINARY", e.account_nonce, signer, label=f"PAYLOAD_{index}_TRANSACTION", ident=f"E:{index}")
            steps.append(step)
            if model_valid(step, st, self.t0, self.cfg):
                st = model_apply(step, st, self.t0, self.cfg)
        return steps

    def problem(self, payload=(), *, held_only=False, starts=None):
        members = [step for _, step, held in self.k if held or not held_only]
        if not held_only:
            members += [replace(x, label="CARRIER_FORMED_FROM_THE_PAYLOAD_0x7E", ident=f"P:{i}", by_a=False)
                        for i, x in enumerate(payload) if x.cls == "WRITE"]
        starts = self.starts if starts is None else starts
        steps = members + list(self.targets.values()) + list(payload)
        max_an = max([self.max_an] + [x.nonce + 1 for x in payload if x.cls != "WRITE"])
        return Problem(self.cfg, critical_times(self.t0, self.cfg, starts, steps), tuple(starts), tuple(members),
                       self.a_signs, self.published if held_only else True, self.rotate_targets, self.targets,
                       max_an)

    def judge(self, payload, *, balance_stated=False, between=()):
        """34.2 rule 1 (a) for `payload` (a list of Steps): Verdict(made, reach, preempted, nodes).

        Whether A holds a's secp256k1 key is not known without evidence (an off-chain signature
        publishes it too, l. 45), so the condition is judged where A holds it in both runs, and,
        where there is no evidence and the payload carries an element signed with that key (an ECDSA
        transaction or a 0x7d, whose signature reveals the public key to whoever receives the
        payload), also where A learns it only from the payload.
        """
        key = ("judge", tuple(payload), bool(balance_stated), tuple(between))
        if key not in self._cache:
            p = self.problem(payload)
            verdict = search(p, tuple(payload), balance_stated=balance_stated, between=tuple(between))
            if not self.published and any(x.cls in ("ECDSA", "ENROLL") for x in payload):
                p.a_ecdsa_without = False
                learned = search(p, tuple(payload), balance_stated=balance_stated, between=tuple(between))
                verdict = Verdict({**learned.made, **verdict.made}, {}, {**learned.preempted, **verdict.preempted},
                                  verdict.nodes + learned.nodes)
            self._cache[key] = verdict
        return self._cache[key]

    def reach(self, start=None):
        """34.2 rule 1 (g): the targets that K_A and O_A make includable in blocks after the head (or `start`)."""
        start = self.hs if start is None else start
        key = ("reach", start)
        if key not in self._cache:
            self._cache[key] = search(self.problem(held_only=True, starts=(start,)), None).reach
        return self._cache[key]

    def run(self, payload, st=None):
        st = self.hs if st is None else st
        for step in payload:
            if model_valid(step, st, self.t0, self.cfg):
                st = model_apply(step, st, self.t0, self.cfg)
        return st

    def ended(self, step, st):
        """A condition of 32.2 rule 2 holds at (st, head.timestamp + SLOT)."""
        t, cfg = self.t0, self.cfg
        if step.cls == "WRITE":
            return st.mn > step.nonce or model_final(st, t, cfg) or t > step.expiry
        if step.cls == "ROTATE":
            return st.an > step.nonce or (step.activating and model_final(st, t, cfg) and st.activated)
        return (st.an > step.nonce or st.mode != "LEGACY"
                or (cfg.fork_time is not None and t >= cfg.fork_time))

    def as_state(self, st):
        return replace(self.head, mode=st.mode, migration_nonce=st.mn, account_nonce=st.an,
                       activated=st.activated, commitment=st.commitment, enrolled_at=st.enrolled_at,
                       code_kind=st.code_kind)

    def own(self, c):
        return c is not None and self.tracker._own_commitment(self.s, c)

    def owner_can_send(self):
        """The owner can send a transaction of a at the head (34.2 rule 1 (a) (i), (e)): a PQ_BY_PROOF key
        that is not exposed (only the seed's holder writes one), an enrollment key that the device created
        and that is not exposed, or a's secp256k1 key while a is LEGACY before T (l. 360-361)."""
        hs = self.hs
        if hs.mode == "PQ_BY_PROOF":
            return hs.commitment not in self.exposed
        if hs.mode == "PQ_BY_ENROLL":
            return self.own(hs.commitment) and hs.commitment not in self.exposed
        if hs.mode == "LEGACY":
            return ecdsa_alive(hs, self.t0, self.cfg)
        return False

    def first_owner_act(self):
        hs = self.hs
        if hs.mode == "LEGACY":
            return Step("ECDSA", hs.an, label="OWN_ECDSA_TRANSACTION", ident="O:first")
        cls = "ORDINARY" if hs.activated else "ACTIVATION"
        return Step(cls, hs.an, hs.commitment, label=f"OWN_{cls}_OF_THE_CURRENT_KEY", ident="O:first")

    def owner_act_candidates(self):
        """(34.2 rule 1 (e), (f); 37.3 rule 4; V25-W-1 (ii)): the owner's own acts at the
        head's account nonce, in the order tried: a transaction of a (an ECDSA one while LEGACY before T, otherwise
        the activation or a transaction of the current key); then, for a LEGACY account before T, each tracked 0x7d
        of the owner's at that nonce whose key is not exposed, with the activation of the key that it commits at the
        next account nonce right after it (an activating 0x7c that calls no rotate)."""
        out = [{"kind": "OWNER_TRANSACTION", "prefix": [self.first_owner_act()]}]
        hs = self.hs
        if hs.mode == "LEGACY" and ecdsa_alive(hs, self.t0, self.cfg):
            for key, step, _held in self.k:
                a = self.auths.get(key)
                if (a is None or a.kind != "ENROLL" or step.nonce != hs.an or not self.own(a.commitment)
                        or a.commitment in self.exposed or not model_valid(step, hs, self.t0, self.cfg)):
                    continue
                activation = Step("ACTIVATION", hs.an + 1, a.commitment, label="OWN_ACTIVATION_OF_THE_ENROLLED_KEY",
                                  ident="O:activation-after-0x7d")
                out.append({"kind": "TRACKED_0x7D", "prefix": [step, activation], "carrier": list(key)})
        return out

    @staticmethod
    def _mark_preemptible(notice, failed):
        """No act that the component can name for this authorization is safe from a member of K or O placed
        before it (34.2 rule 1 (b), last sentences, with (f)); the offer says so and names a run."""
        extra = {"meets_rule_1_a": False, "act_preemptible": True, "statement": NO_ROBUST_ACT,
                 "preempted_run": next(iter(failed.values()))}
        notice.update(extra)
        if notice.get("payload") is not None:
            notice["payload"].update(extra)

    def _plan_rotate_with_the_0x7d(self, notice, key, a, picked, fallback, robust):
        """(V25-W-1 (ii); 37.3 rule 4): the owner's own tracked 0x7d at the head's account nonce, then the
        activation of the key it commits at the next account nonce, for one payload, after which the rotate is
        invalid at every later position (l. 318). The owner's ECDSA transactions are no such act where the 0x7d,
        which A holds, placed before them makes them fail and the rotate binds from deadline(a) (l. 113, l. 328)."""
        candidate, through, steps, failed = picked
        precursor = bool(self.judge([steps[0]]).made)
        payload = bundle_payload(
            "LEGACY_BEFORE_T", kind="ROTATE", through_account_nonce=through if through is not None else a.nonce,
            plan=self.plan_of(steps), precursor_carriers=[candidate["carrier"]], fresh_precursor=False,
            time_left=self.time_left(a), owner_can_send_before_the_write=True, fee_path="OWN_FUNDS",
            why=("an ECDSA transaction of the owner's at the account nonce can be made to fail by a member of K or O "
                 "placed before it, such as the tracked 0x7d, which A holds (the stock nonce check; R1 before T, "
                 "l. 361), after which the rotate stays includable; the 0x7d with the activation of its key right "
                 "after it leaves the rotate invalid at every later position (l. 318; 34.2 rule 1 (e), (f); "
                 "37.3 rule 4; V25-W-1 (ii))"))
        if fallback is not None and fallback[0]["kind"] == "OWNER_TRANSACTION":
            payload["rejected_act"] = {"first": "TRANSACTION_OF_THE_LEGACY_ACCOUNT_AT_ITS_NONCE",
                                       "made_fail_by_a_member_placed_before": True,
                                       "run": next(iter(fallback[3].values()))}
        notice.update(action=OFFER_ONE_PAYLOAD_BUNDLE, precursors=a.nonce - self.hs.an, payload=payload,
                      owner_can_send=True,
                      answer=ANSWER_PRECURSOR_WITH_ITS_ACTS if precursor else ANSWER_ACT_WITHOUT_PRECURSOR)
        if not robust:
            self._mark_preemptible(notice, failed)
        return notice

    def filler(self, j, end):
        if end.mode == "LEGACY":
            return Step("ECDSA", j, label=f"OWN_ECDSA_AT_{j}", ident=f"O:{j}")
        return Step("ORDINARY", j, end.commitment, label=f"OWN_TRANSACTION_AT_{j}", ident=f"O:{j}")

    def between(self, payload):
        """The targets that a proper prefix of the payload makes includable (a split delivery exposes them)."""
        out = []
        for i in range(1, len(payload)):
            for key in self.judge(list(payload[:i])).made:
                if key not in out:
                    out.append(key)
        return out

    def robust(self, payload, need, *, balance_stated=True):
        """(34.2 rule 1 (e), (f) with V25-W-1 (ii); 37.3 rule 4): the runs from the head in which members of K
        or O placed before the payload make an act of it fail and a target in `need` is includable after it
        ({target: witness}; empty when no member can). 'Its own transactions of a ... that no member of K or O
        placed before them can make fail' (V25-W-1 (ii)): an act judged from the head, where the wallet plans it,
        with the balance condition of (f) stated, as acts_through judges it (37.3 rule 2; reading R4-2)."""
        key = ("robust", tuple(payload), tuple(need), bool(balance_stated))
        if key not in self._cache:
            p = self.problem(payload, starts=(self.hs,))
            self._cache[key] = search(p, tuple(payload), balance_stated=balance_stated, need=tuple(need)).failed
        return self._cache[key]

    def admissible(self, payload, need=(), *, balance_stated=True):
        """The payload meets (a), no act of it is pre-empted ((f)), and each authorization that it answers or
        that its precursor makes includable meets a condition of 32.2 rule 2 at its end ((b)). (37.3 rule
        7, S-11): every act is valid in its own planning state, at head.timestamp + SLOT; a payload with an act
        that is not is never offered."""
        states = model_planning_states(self.hs, list(payload), self.t0, self.cfg)
        if any(not model_valid(step, states[i], self.t0, self.cfg) for i, step in enumerate(payload)):
            return False
        between = self.judge(list(payload[:1])).made if len(payload) > 1 else {}
        between = list(between)
        verdict = self.judge(list(payload), balance_stated=balance_stated, between=between)
        if verdict.made or verdict.preempted:
            return False
        end = self.run(payload)
        return all(self.ended(self.targets[key], end) for key in list(need) + between)

    def acts_through(self, prefix, need=(), *, balance_stated=True):
        """The shortest payload: `prefix`, then transactions of a at the following account nonces, that is
        admissible (34.2 rule 1 (b), (e)); returns (ok, through, payload) with through None if none follow."""
        end = self.run(prefix)
        start = end.an
        for k in [None] + list(range(start, max(self.max_an, start) + 2)):
            payload = list(prefix) + ([] if k is None else [self.filler(j, end) for j in range(start, k + 1)])
            if self.admissible(payload, need, balance_stated=balance_stated):
                return True, k, payload
        return False, None, list(prefix)

    # ------------------------------------------------------------- spec 39.2 rule 1
    def writes_route(self, prefix, commitment, first_mn, a, key, *, sponsored=True):
        """Spec 39.2 rule 1 (c), (d): the writes past PI.migration_nonce that are the act where the activation is
        not: after `prefix` (a precursor, or nothing in the re-commit gate), a same-key write of `commitment` through
        the re-commit gate at each migration_nonce from `first_mn` through PI.migration_nonce (31.2 rule 8 (a); each
        prepared against its planning state, 35.2 rule 1 (b)), sponsored (no account nonce, no balance of a, no
        commitment needed; 3.2.6), or, with sponsored False, paid by a under the balance condition that the offers state
        (37.3 rule 2). Candidates in order: the writes alone, with the activation once they are in a block; the writes
        and, right after them, the activation of that key (and transactions as far as (a) requires), where rule 1 (a)
        needs it; each again through the highest PI.migration_nonce of the tracked exposed PIs at or above `first_mn`.
        Returns (steps, through) of the first candidate that meets (a), discharges the PI and that no member of K or O
        placed before it can make fail (robust), or None."""
        highest = max([a.nonce] + [self.auths[k].nonce for k in self.targets
                                   if self.auths[k].kind == "PI" and self.auths[k].nonce >= first_mn])
        end = self.run(prefix)
        for last in dict.fromkeys((a.nonce, highest)):
            writes = [Step("WRITE", m, commitment, expiry=self.t0 + PROOF_MAX_LIFETIME, a_paid=not sponsored,
                           takes_balance=not sponsored,
                           label=f"{'SPONSORED' if sponsored else 'A_PAID'}_SAME_KEY_WRITE_AT_{m}", ident=f"S:{m}")
                      for m in range(first_mn, last + 1)]
            for with_activation in (False, True):
                if with_activation:
                    activation = Step("ACTIVATION", end.an, commitment, label="ACTIVATION_AFTER_THE_WRITES",
                                      ident="A:after-writes")
                    ok, through, steps = self.acts_through(list(prefix) + writes + [activation], [key])
                else:
                    steps, through = list(prefix) + writes, None
                    ok = self.admissible(steps, [key])
                if ok and not self.robust(steps, [key]):
                    return steps, through
        return None

    def writes_payload(self, case, steps, through, a, *, rejected=None, why=None, **extra):
        """The offer's payload for the writes route (spec 39.2 rule 1 (c)), with its plan (35.2 rule 1)."""
        payload = bundle_payload(case, activation_as_act=False, past_pi_migration_nonce=a.nonce, plan=self.plan_of(steps),
                                 time_left=self.time_left(a), **extra)
        if why is not None:
            payload["why"] = why
        if any(x.cls == "ACTIVATION" for x in steps):
            payload["then_once_in_a_block"] = None
            payload["activation_in_the_payload"] = True       # rule 1 (a) needs it there (a tracked rotate)
        if through is not None:
            payload["through_account_nonce"] = through
        if rejected:
            payload["activation_rejected"] = {"made_fail_by_a_member_placed_before": True,
                                              "run": next(iter(rejected.values()))}
        return payload

    def no_sponsored_path(self, prefix, commitment, first_mn, a, key, activation_offered):
        """Spec 39.2 rule 1 (d): what the offer names where the wallet has no sponsored path."""
        route = self.writes_route(prefix, commitment, first_mn, a, key, sponsored=False)
        out = {"rule": "spec 39.2 rule 1 (d)", "statement": NO_SPONSORED_PATH,
               "act": "WRITES_PAID_BY_A_PAST_PI_MIGRATION_NONCE" if route is not None else None,
               "where": "BALANCE_COVERS_EVERY_TAKE (the caller's balance_covers_acts; l. 285, l. 3070; 37.3 rule 2)",
               "otherwise": {"act_preemptible": True, "statement": NO_ROBUST_ACT,
                             "asks_for": "A_SPONSORED_FEE_CHOICE (mode 1 or 2; l. 417)",
                             "offers_meanwhile": "ACTIVATION_OF_THE_CURRENT_KEY" if activation_offered else None}}
        if route is not None:
            out["plan"] = self.plan_of(route[0])
        return out

    # ------------------------------------------------------------- spec 35.2: the payload plan
    @staticmethod
    def name(c):
        symbolic = {A_KEY: "A_KEY", IND_KEY: "C_IND", FRESH_KEY: "THE_KEY_THAT_31_2_RULE_2_SELECTS"}
        return None if c is None else symbolic.get(c, c.hex())

    def epoch_of(self, c):
        """The epoch of the seed key of `c` where the device knows it (a link, or a tracked authorization with it)."""
        if c is None or c in (A_KEY, IND_KEY, FRESH_KEY):
            return None
        linked = self.s["links"].get(c.hex())
        if linked is not None:
            return linked
        return next((a.epoch for a in self.auths.values() if a.commitment == c and a.epoch is not None), None)

    def state_dict(self, st):
        return {"mode": st.mode, "migration_nonce": st.mn, "account_nonce": st.an, "activated": st.activated,
                "commitment": self.name(st.commitment)}

    def key_of(self, step, si):
        """The key of a write against its planning state S_i (35.2 rule 1 (b), (c))."""
        c = step.commitment
        if si.commitment is not None and c == si.commitment:
            return {"key": KEY_SAME, "commitment": self.name(c), "epoch": self.epoch_of(c)}
        if c == IND_KEY:
            return {"key": KEY_IND, "commitment": self.name(c), "epoch": None}
        if c == FRESH_KEY:
            return {"key": KEY_NEW, "commitment": self.name(c), "epoch": si.mn}
        e = self.epoch_of(c)
        tracked = step.ident.startswith("K:")
        return {"key": KEY_NEW if e == si.mn else KEY_TRACKED if tracked else KEY_UNKNOWN,
                "commitment": self.name(c), "epoch": e}

    def plan_of(self, steps):
        """Spec 35.2 rule 1: the payload as one plan anchored at the observed head B. S_0 is B's state and S_i
        the state that the acts before x_i leave, each taken as valid (reachability.planning_states, at
        head.timestamp + SLOT); each act takes its values from its own S_i: a write's PI.migration_nonce and its key
        (the same key as S_i, or a new key at e = m_i), a 0x7d's or 0x7c's account nonce, an activation's key and
        condition, a transaction's sender class. No planning state is a canonical block (35.2 rule 1 (a))."""
        states = model_planning_states(self.hs, list(steps), self.t0, self.cfg)
        acts = []
        for i, step in enumerate(steps):
            si = states[i]
            act = {"index": i, "kind": {"ORDINARY": "TRANSACTION"}.get(step.cls, step.cls),
                   "planning_state": self.state_dict(si)}
            if step.cls == "WRITE":
                tracked = self.auths.get(tuple(step.ident[2:].split(":"))) if step.ident.startswith("K:") else None
                if tracked is not None and tracked.layout == 1:
                    fee = "LAYOUT_1_ANY_CARRIER"       # a layout-1 PI names no fee mode (section 18.24)
                else:
                    paid = step.a_paid if tracked is None else tracked.fee_mode == 0  # a tracked carrier: its PI's mode
                    fee = "PAID_BY_A" if paid else "SPONSORED"
                act.update(migration_nonce=si.mn, fee=fee, **self.key_of(step, si))
            elif step.cls == "ENROLL":
                act.update(account_nonce=si.an, **self.key_of(step, si))
            elif step.cls == "ACTIVATION":
                act.update(account_nonce=si.an, reveals=self.name(si.commitment),
                           activation_condition=si.mode in ("PQ_BY_ENROLL", "PQ_BY_PROOF") and not si.activated)
            elif step.cls == "ORDINARY":
                act.update(account_nonce=si.an, signed_by=self.name(si.commitment), sender_class=(
                    "ACTIVATED" if si.activated else "LEGACY" if si.mode == "LEGACY" else "UNACTIVATED_PQ"))
            elif step.cls == "ECDSA":
                act.update(account_nonce=si.an, sender_class="LEGACY")
            else:
                act.update(account_nonce=si.an, signed_by=self.name(si.commitment), binds=self.name(step.commitment))
            acts.append(act)
        return {"rule": PLAN_RULE, "anchor": {"block_hash": self.head.block_hash, "number": self.head.number},
                "planned_at_timestamp": self.t0, "acts": acts, "end": self.state_dict(states[-1]),
                "after_the_first": "LEAVES_ONLY_IN_THIS_PAYLOAD (35.2 rule 1 (e))",
                "at_a_new_head": "RE_PLANNED_AS_A_WHOLE: REBOUND_UNCHANGED_OR_VOID (35.2 rule 1 (d))"}

    # ------------------------------------------------------------- 34.2 rule 1 (b), (e)-(g)
    def selected_key(self, role, nonce):
        """The commitment that 31.2 rule 2 selects for the precursor, where the device knows it."""
        epoch = nonce if role == "WRITE" else 0
        for h, e in self.s["links"].items():
            if e == epoch and e not in self.epochs:
                return bytes.fromhex(h)
        for key, step, _held in self.k:
            a = self.auths.get(key)
            if a is not None and a.epoch == epoch and a.epoch not in self.epochs and step.cls == role \
                    and step.nonce == nonce:
                return a.commitment
        return FRESH_KEY

    def precursor(self):
        """Where every first act needs a write first (34.2 rule 1 (a) (i), (ii)): its role and its carriers."""
        if "precursor" in self._cache:
            return self._cache["precursor"]
        hs, t0, cfg = self.hs, self.t0, self.cfg
        g = model_gate(hs, t0, cfg)
        if g in ("FROZEN", "OVERRIDE") or (g == "PRE_T_LEGACY" and not self.published):
            role, nonce, case = "WRITE", hs.mn, g
        elif hs.mode == "LEGACY" and ecdsa_alive(hs, t0, cfg) and legacy_before_T(replace(self.head, timestamp=t0)):
            role, nonce, case = "ENROLL", hs.an, "LEGACY_BEFORE_T"
        else:
            self._cache["precursor"] = None
            return None
        carriers = [(key, step) for key, step, held in self.k
                    if held and key[0] != "TX" and step.cls == role and step.nonce == nonce
                    and model_valid(step, hs, t0, cfg)]
        commitment = self.selected_key(role, nonce)
        if carriers:
            step = max(carriers, key=lambda c: c[1].expiry or 0)[1]
        elif role == "WRITE":
            step = Step("WRITE", nonce, commitment, expiry=t0 + PROOF_MAX_LIFETIME,
                        a_paid=(g in ("PRE_T_LEGACY", "FROZEN")),
                        takes_balance=(g in ("PRE_T_LEGACY", "FROZEN")), label="FRESH_WRITE_AT_THE_CURRENT_MIGRATION_NONCE",
                        ident="P:fresh")
        else:
            step = Step("ENROLL", nonce, commitment, label="FRESH_0x7D_AT_THE_ACCOUNT_NONCE", ident="P:fresh")
        out = {"role": role, "case": case, "nonce": nonce, "carriers": carriers, "step": step,
               "fresh": not carriers, "commitment": commitment}
        self._cache["precursor"] = out
        return out

    def bounded(self, a):
        """Whether the wait of 34.2 rule 1 (g) is bounded for the tracked PI `a`."""
        pre = self.precursor()
        if pre["case"] in ("PRE_T_LEGACY", "FROZEN", "LEGACY_BEFORE_T"):
            return True     # no deadline (l. 261); a LEGACY account's wait continues in the frozen gate from T (l. 111)
        c = self.hs.commitment
        if self.own(c) and c not in self.exposed:
            return True     # the owner's own enrollment: a chain-finalized block past deadline(a) ends the tracking
        d = model_deadline(self.hs, self.cfg)
        return d is None or a.expiry + self.tracker.override_margin < d

    def handoff(self, step):
        """The tracked rotates whose key is exposed that A reaches from the state after `step` but not from the
        head: a fresh precursor that a builder splits off hands them to A (34.2 rule 1 (f), (g); V22-W-5 (vii))."""
        if not model_valid(step, self.hs, self.t0, self.cfg):
            return []
        after = model_apply(step, self.hs, self.t0, self.cfg)
        before, later = self.reach(), self.reach(after)
        return [key for key in self.order if self.auths[key].kind == "ROTATE" and key not in before and key in later]

    def hold(self):
        """34.2 rule 1 (g): the fresh precursor is held back, or None."""
        if "hold" in self._cache:
            return self._cache["hold"]
        out = None
        pre = self.precursor()
        if pre is not None and pre["fresh"]:
            # Every tracked exposed PI above the head's migration_nonce, expired at the head or not: only a
            # chain-finalized block ends the wait (32.2 rule 2 (e)).
            waiting = [key for key in self.order if self.auths[key].kind == "PI"
                       and self.auths[key].nonce > self.hs.mn]
            reach = self.reach()
            lacking = [key for key in waiting if key not in reach]
            if lacking and all(self.bounded(self.auths[key]) for key in lacking):
                made = self.judge([pre["step"]]).made
                lifting = [key for key in self.order if self.auths[key].kind == "ROTATE" and key in made
                           and not self.owner_can_send()]
                if not lifting:
                    out = {"pis": lacking, "precursor": pre}
        self._cache["hold"] = out
        return out

    def time_left(self, a=None):
        """Rule 1 (d): the tracked PI's expiry, the latest expiry of a carrier of the precursor that A holds,
        in the override gate deadline(a) (None while T is unscheduled) and before T T itself; a rotate has no
        time bound (32.2 rule 6)."""
        out = {}
        if a is not None:
            if a.kind == "PI":
                out["pi_expiry"] = a.expiry
            else:
                out["no_time_bound"] = True
        pre = self.precursor()
        expiries = sorted(step.expiry for _, step in (pre["carriers"] if pre else []) if step.cls == "WRITE")
        if expiries:
            out["precursor_expiry"] = expiries[-1]
        if state_gate(self.head) == "OVERRIDE":
            out["override_deadline"] = self.head.deadline
        if legacy_before_T(self.head):
            out["fork_time"] = self.head.fork_time
        return out

    def hold_payload(self, hold):
        gate = state_gate(self.head)
        meanwhile = ["SHOW_THE_TIME_LEFT",
                     "OFFER_A_TRACKED_WRITE_WITH_ITS_ACTS_AT_ONCE_IF_A_REORGANIZATION_MAKES_ONE_INCLUDABLE"]
        if gate == "OVERRIDE":
            meanwhile.insert(1, "KEEP_THE_STEALTH_ENROLLMENT_REPORTED (34.2 rule 2)")
        pis = [self.auths[key] for key in hold["pis"]]
        return {"hold": True, "rule": "spec 34.2 rule 1 (g)", "gate": gate or hold["precursor"]["case"],
                "why": ("no carrier of the precursor that A holds can be included after the head (judged at "
                        "head.timestamp + SLOT), and the members of K that A holds and of O that A can sign reach "
                        "no state in which the tracked PI is includable; a write at that nonce needs the seed "
                        "(l. 46), so a fresh one would give A, as a builder that receives it, the one piece that "
                        "it lacks (l. 47, l. 252)"),
                "until": ("a chain-finalized block meets a condition of 32.2 rule 2 for every tracked PI it waits "
                          "for, not a head past its expiry (32.2 rule 2 (e))"),
                "time_left": {**self.time_left(), "pi_expiries": sorted(p.expiry for p in pis)},
                "override_margin": self.tracker.override_margin if gate == "OVERRIDE" else None,
                "meanwhile": meanwhile,
                "then": "a fresh write with its acts as one payload (34.2 rule 1 (b)-(f))",
                "sends_transaction": False}

    def pi_payload(self, key, a, pre, time_left):
        """The one payload for a tracked exposed PI above the head's migration_nonce (34.2 rule 1 (a) (i),
        (ii), (b), (f)): the act is the activation of the key the precursor commits where that payload is
        admissible, otherwise sponsored writes past PI.migration_nonce."""
        hs = self.hs
        w = pre["step"]
        handed = self.handoff(w) if pre["fresh"] else []
        precursor = replace(w, commitment=IND_KEY, label="WRITE_COMMITTING_C_IND", ident="P:ind") if handed else w
        c = precursor.commitment
        sponsored = replace(precursor, a_paid=False, takes_balance=False) if precursor.cls == "WRITE" else precursor
        first_mn = hs.mn + 1 if pre["role"] == "WRITE" else 1
        writes = [Step("WRITE", m, c, expiry=self.t0 + PROOF_MAX_LIFETIME, a_paid=False, label=f"SPONSORED_WRITE_AT_{m}",
                       ident=f"S:{m}") for m in range(first_mn, a.nonce + 1)]
        act_at = hs.an if pre["role"] == "WRITE" else hs.an + 1
        activation_ok, through, act_steps = self.acts_through(
            [precursor, Step("ACTIVATION", act_at, c, label="ACTIVATION_OF_THE_PRECURSORS_KEY", ident="A:act")], [key])
        case = pre["case"]
        # (spec 39.2 rule 1 (a), (b)): the activation is the act only where no member of K or O placed
        # before the payload can make it fail while the PI is includable after them; a write of another key at the
        # precursor's migration_nonce, which displaces the precursor, is such a member.
        displaced = self.robust(act_steps, [key]) if activation_ok and case != "LEGACY_BEFORE_T" else {}
        if displaced:
            activation_ok = False
        # The sponsored writes need no account nonce, balance of a or commitment (3.2.6); a member that makes their
        # precursor fail without displacing it by a write, as A's ECDSA transaction before T does (V22-W-7), is A's race
        # (34.2 residual risk 5), which no payload survives, so (a) and the discharge decide here.
        sponsored_ok = self.admissible([sponsored] + writes, [key])
        payload = bundle_payload(case, activation_as_act=activation_ok and case != "LEGACY_BEFORE_T",
                                 precursor_carriers=[[g, v] for (g, v), _ in pre["carriers"]],
                                 fresh_precursor=pre["fresh"], time_left=time_left, past_pi_migration_nonce=a.nonce)
        if displaced:
            payload["why"] = DISPLACED_PRECURSOR
            payload["activation_rejected"] = {"made_fail_by_a_member_placed_before": True,
                                              "run": next(iter(displaced.values()))}
        if activation_ok and through is not None and case != "LEGACY_BEFORE_T":
            payload["through_account_nonce"] = through
        # (35.2 rule 1): the plan of the payload that the act chooses, each act against its planning state.
        if activation_ok and case != "LEGACY_BEFORE_T":
            payload["plan"] = self.plan_of(act_steps)
        elif sponsored_ok:
            payload["plan"] = self.plan_of([sponsored] + writes)
        if handed:
            payload.update(first="WRITE_COMMITTING_A_KEY_NOT_DERIVED_FROM_THE_SEED_AT_THE_CURRENT_MIGRATION_NONCE",
                           precursor_commits="C_IND",
                           handed_rotates=[[g, v] for g, v in handed])
        if not activation_ok and not sponsored_ok:
            payload.update(meets_rule_1_a=False, statement=NO_PAYLOAD_MEETS)
        return payload

    def plan(self, key):
        """The offer for one tracked live authorization whose key is exposed (32.2 rule 3; 34.2 rule 1)."""
        gid, vid = key
        a = self.auths[key]
        notice = {"group": gid, "variant": vid, "pi_expiry": a.expiry, "nonce": a.nonce}
        if a.kind == "ENROLL":
            return self._plan_enroll(notice, a)
        if a.kind == "ROTATE":
            # (spec 35.3 rule 1): this offer answers one carrier of the index (a, n), the one that binds
            # an exposed key; the other carriers of (a, n) are tracked and judged on their own.
            variants = self.s["groups"].get(gid, {})
            notice["index"] = {"rule": "spec 35.3 rule 1", "account_nonce": a.nonce,
                               "carrier_variants_known": len(variants),
                               "carrier_variants_live": sum(1 for r in variants.values() if r["ended"] is None),
                               "this_carrier": {"activating": a.activating, "binds": a.commitment.hex(),
                                                "key_exposed": True}}
            return self._plan_rotate(notice, key, a)
        return self._plan_pi(notice, key, a)

    def _plan_enroll(self, notice, a):
        hs = self.hs
        position = "BELOW_HEAD" if a.nonce < hs.an else "AT_HEAD" if a.nonce == hs.an else "ABOVE_HEAD"
        notice["account_nonce_position"] = position
        if not ecdsa_alive(hs, self.t0, self.cfg) or position == "BELOW_HEAD":
            notice.update(action=WAIT_FINALITY_WATCH_REORG, answer=ANSWER_WAIT)
        else:
            notice.update(action=OFFER_ACCOUNT_NONCE_CONSUMPTION, answer=ANSWER_ACT_WITHOUT_PRECURSOR)
            if position == "ABOVE_HEAD":
                notice.update(precursors=a.nonce - hs.an, one_payload=True)
        return notice

    def _plan_rotate(self, notice, key, a):
        hs, t0, cfg = self.hs, self.t0, self.cfg
        position = "BELOW_HEAD" if a.nonce < hs.an else "AT_HEAD" if a.nonce == hs.an else "ABOVE_HEAD"
        notice["account_nonce_position"] = position
        notice["time_left"] = self.time_left(a)
        if position == "BELOW_HEAD" or (a.activating and hs.activated and model_final(hs, t0, cfg)):
            # A rotate never applies again on this branch once its account nonce is consumed, or, if
            # activating, once the account is binding-final and activated (l. 314-315).
            notice.update(action=WAIT_FINALITY_WATCH_REORG, answer=ANSWER_WAIT)
            return notice
        if self.owner_can_send():
            # 34.2 rule 1 (e): a transaction that the owner can send at the rotate's account nonce, with those
            # before it, the activation first while a PQ account is not activated, as far as (a) requires.
            # ((e) with (f), 37.3 rule 4, V25-W-1 (ii)): an act that a member of K or O placed before it can
            # make fail, leaving the rotate includable, is no such act; the candidates are tried in turn.
            chosen, fallback = None, None
            for candidate in self.owner_act_candidates():
                ok, through, steps = self.acts_through(candidate["prefix"], [key])
                if not ok:
                    continue
                failed = self.robust(steps, [key])
                if not failed:
                    chosen = (candidate, through, steps, None)
                    break
                if fallback is None:
                    fallback = (candidate, through, steps, failed)
            picked = chosen or fallback
            if picked is not None and picked[0]["kind"] == "TRACKED_0x7D":
                return self._plan_rotate_with_the_0x7d(notice, key, a, picked, fallback, chosen is not None)
            ok = picked is not None
            candidate, through, steps, failed = picked if ok else (None, None, [], None)
            sender = sender_class(self.head)
            if position == "AT_HEAD":
                notice["action"] = OFFER_ACCOUNT_NONCE_CONSUMPTION
                notice["first"] = {"ACTIVATED": "ANY_TRANSACTION",
                                   "UNACTIVATED_PQ": "ACTIVATION_OF_THE_CURRENT_KEY",
                                   "LEGACY": "A_TRANSACTION_OF_THE_LEGACY_ACCOUNT"}[sender]
                if ok and through is not None:
                    notice.update(one_payload=True, payload=bundle_payload("ACCOUNT_NONCE", sender=sender,
                                                                           through_account_nonce=through,
                                                                           plan=self.plan_of(steps)))
            else:
                notice.update(action=OFFER_ONE_PAYLOAD_BUNDLE, precursors=a.nonce - hs.an,
                              payload=bundle_payload("ACCOUNT_NONCE", sender=sender,
                                                     through_account_nonce=through if ok and through is not None
                                                     else a.nonce))
                if ok:
                    notice["payload"]["plan"] = self.plan_of(steps)
            notice["answer"] = ANSWER_ACT_WITHOUT_PRECURSOR
            if not ok:
                notice.update(meets_rule_1_a=False, statement=NO_PAYLOAD_MEETS)
                if notice.get("payload") is not None:
                    notice["payload"].update(meets_rule_1_a=False, statement=NO_PAYLOAD_MEETS)
            elif failed:
                self._mark_preemptible(notice, failed)
            return notice
        pre = self.precursor()
        if pre is None:
            if key not in self.reach():
                # Nothing that A holds or signs reaches it and no write at the head opens a gate: it cannot be
                # included on this branch (32.2 rule 3 (c)); watch for a reorganization.
                notice.update(action=WAIT_FINALITY_WATCH_REORG, answer=ANSWER_WAIT)
                return notice
            notice.update(action=FOLLOW_RULE_7B_8B, answer=ANSWER_RULE_7B_8B, reason="NO_ACT_THE_OWNER_CAN_SEND",
                          warning=("The owner can send no transaction of a and no write at the head precedes one; "
                                   "31.2 rule 7 (b) / 8 (b) applies, and the race with the key's holder is stated."))
            return notice
        w = pre["step"]
        if key not in self.judge([w]).made:
            # No write at the current migration_nonce makes it includable (34.2 rule 1 (a) (i)).
            notice.update(action=WAIT_FINALITY_WATCH_REORG, answer=ANSWER_WAIT,
                          no_write_at_the_head_makes_it_includable=True)
            return notice
        act_at = hs.an if pre["role"] == "WRITE" else hs.an + 1
        ok1, through1, steps1 = self.acts_through(
            [w, Step("ACTIVATION", act_at, w.commitment, label="ACTIVATION_OF_THE_PRECURSORS_KEY", ident="A:act")], [key])
        if ok1 and pre["fresh"] and key in self.handoff(w):
            ok1 = False                  # V22-W-5 (vii): the fresh precursor hands A this rotate
        common = dict(kind="ROTATE", precursor_carriers=[[g, v] for (g, v), _ in pre["carriers"]],
                      fresh_precursor=pre["fresh"], time_left=self.time_left(a))
        if ok1:
            payload = bundle_payload(pre["case"], through_account_nonce=through1 if through1 is not None else a.nonce,
                                     plan=self.plan_of(steps1), **common)
        else:
            # 34.2 rule 1 (f): a write that commits a key other than the one that signs the rotate, in the
            # precursor's place; where members of K commit the signing key at a later migration_nonce, sponsored
            # writes of the new key through the highest such nonce; then the activation of the new key.
            w_ind = replace(w, commitment=IND_KEY, label="WRITE_COMMITTING_C_IND", ident="P:ind")
            later = [step.nonce for _, step, _ in self.k if step.cls == "WRITE" and step.commitment == a.signer_commitment
                     and step.nonce > w.nonce]
            past = [Step("WRITE", m, IND_KEY, expiry=self.t0 + PROOF_MAX_LIFETIME, a_paid=False,
                         label=f"SPONSORED_WRITE_OF_C_IND_AT_{m}", ident=f"S:ind:{m}")
                    for m in range(w.nonce + 1, max(later) + 1)] if later and pre["role"] == "WRITE" else []
            ok2, through2, steps2 = self.acts_through(
                [w_ind] + past + [Step("ACTIVATION", act_at, IND_KEY, label="ACTIVATION_OF_C_IND", ident="A:ind")], [key])
            payload = bundle_payload(pre["case"], act="WRITE_COMMITTING_C_IND",
                                     through_account_nonce=through2 if through2 is not None else None, **common)
            if past:
                payload["sponsored_writes_of_c_ind_through_migration_nonce"] = max(later)
            if not ok2:
                payload.update(meets_rule_1_a=False, statement=NO_PAYLOAD_MEETS)
            else:
                payload["plan"] = self.plan_of(steps2)
        notice.update(action=OFFER_ONE_PAYLOAD_BUNDLE, owner_can_send=False, answer=ANSWER_PRECURSOR_WITH_ITS_ACTS,
                      applies_when="a write at the current migration_nonce makes this rotate includable (checked)",
                      payload=payload)
        return notice

    def _plan_pi(self, notice, key, a):
        hs, t0, cfg = self.hs, self.t0, self.cfg
        position = ("BELOW_HEAD" if a.nonce < hs.mn else "AT_HEAD" if a.nonce == hs.mn else "ABOVE_HEAD")
        notice.update(pi_nonce_position=position, head_gate=state_gate(self.head))
        g = model_gate(hs, t0, cfg)
        if position == "BELOW_HEAD" or t0 > a.expiry or model_final(hs, t0, cfg):
            # No block after the head can include it on this branch (nonce consumed, expired at head.timestamp
            # + SLOT, or every gate closed for good): 32.2 rule 3 (c); respond at once if a reorg revives it.
            notice.update(action=WAIT_FINALITY_WATCH_REORG, answer=ANSWER_WAIT)
            return notice
        if position == "AT_HEAD":
            if not binds(self.targets[key], hs, t0, cfg):
                notice.update(action=WAIT_FINALITY_WATCH_REORG, answer=ANSWER_WAIT)
            elif g == "RECOMMIT":
                notice.update(action=OFFER_AT_HEAD_NONCE, answer=ANSWER_ACT_WITHOUT_PRECURSOR)
            else:
                # In the frozen and override gates the activation discharges nothing here (l. 113,
                # l. 1160); the act is a write at PI.migration_nonce that commits an unexposed key of the seed.
                notice.update(action=OFFER_ADVANCE_PAST_PI_NONCE, answer=ANSWER_ACT_WITHOUT_PRECURSOR,
                              act="WRITE_AT_THE_PI_MIGRATION_NONCE_COMMITTING_AN_UNEXPOSED_KEY_OF_THE_SEED",
                              activation_discharges=False,
                              fee_path=("SPONSOR" if g == "OVERRIDE" and not self.owner_can_send()
                                        else "SPONSOR_WHERE_THE_FEE_PATH_ALLOWS"),
                              time_left=self.time_left(a))
            return notice
        if g == "RECOMMIT" and self.owner_can_send():
            # WE-16 (iii): the activation closes the re-commit gate at every nonce; a write at the current
            # nonce would make the PI includable (32.2 rule 3 (a)). 34.2 rule 1 (e): as far as (a) requires.
            ok, through, steps = self.acts_through([self.first_owner_act()], [key])
            # (spec 39.2 rule 1 (a), (b)): the activation is the act only where no member of K or O placed
            # before it can make it fail -- by the account nonce, the balance or a change of the commitment, as a write
            # of another key at the current migration_nonce does -- while the PI is includable after them.
            failed = self.robust(steps, [key]) if ok else {}
            if ok and not failed:
                notice.update(action=OFFER_ACTIVATION_ONLY, advance_migration_nonce=False,
                              answer=ANSWER_ACT_WITHOUT_PRECURSOR)
                if through is not None:
                    notice.update(one_payload=True, payload=bundle_payload("ACCOUNT_NONCE", sender="UNACTIVATED_PQ",
                                                                           through_account_nonce=through,
                                                                           plan=self.plan_of(steps)))
                return notice
            # Rule 1 (c): otherwise the act is the sponsored same-key writes through PI.migration_nonce, with the
            # activation once they are in a block; rule 1 (d): what the offer names where no sponsored path exists.
            route = self.writes_route([], hs.commitment, hs.mn, a, key)
            fallback = self.no_sponsored_path([], hs.commitment, hs.mn, a, key, activation_offered=ok)
            if route is not None:
                payload = self.writes_payload("RECOMMIT", route[0], route[1], a, rejected=failed)
                if not ok:
                    payload["activation_rejected"] = {"meets_rule_1_a": False}
                payload["where_no_sponsored_path"] = fallback
                notice.update(action=OFFER_SPONSORED_WRITES, advance_migration_nonce=True, one_payload=True,
                              answer=ANSWER_ACT_WITHOUT_PRECURSOR, time_left=self.time_left(a), payload=payload)
                return notice
            if ok:
                # Rule 1 (d) with 34.2 rule 1 (b): no act that the component can name is safe from every member; the
                # activation still meets (a) and is offered, and the offer says so.
                notice.update(action=OFFER_ACTIVATION_ONLY, advance_migration_nonce=False,
                              answer=ANSWER_ACT_WITHOUT_PRECURSOR, where_no_sponsored_path=fallback)
                if through is not None:
                    notice.update(one_payload=True, payload=bundle_payload("ACCOUNT_NONCE", sender="UNACTIVATED_PQ",
                                                                           through_account_nonce=through,
                                                                           plan=self.plan_of(steps)))
                self._mark_preemptible(notice, failed)
                return notice
            notice.update(action=FOLLOW_RULE_7B_8B, advance_migration_nonce=False, answer=ANSWER_RULE_7B_8B,
                          reason="NO_ACTIVATION_PAYLOAD_MEETS_RULE_1_A", statement=NO_PAYLOAD_MEETS)
            return notice
        pre = self.precursor()
        if pre is not None:
            time_left = self.time_left(a)
            hold = self.hold()
            if hold is not None:
                notice.update(action=WAIT_FRESH_PRECURSOR, advance_migration_nonce_alone=False, fresh_precursor=True,
                              time_left=time_left, hold=self.hold_payload(hold), answer=ANSWER_WAIT)
            else:
                notice.update(action=OFFER_ONE_PAYLOAD_BUNDLE, advance_migration_nonce_alone=False, time_left=time_left,
                              payload=self.pi_payload(key, a, pre, time_left), answer=ANSWER_PRECURSOR_WITH_ITS_ACTS)
            return notice
        reason = "CURRENT_KEY_EXPOSED" if g == "RECOMMIT" else "NO_STATE_GATE_OPEN"
        notice.update(action=FOLLOW_RULE_7B_8B, advance_migration_nonce=False, reason=reason, answer=ANSWER_RULE_7B_8B,
                      warning=("No lone write at the current migration_nonce: it would bring the "
                               "exposed PI's nonce within reach. Follow 31.2 rule 7 (b) / 8 (b); "
                               "the race with the key's holder is stated."))
        return notice

    def write_remedy(self, step, made):
        """The first act that a write failing (a) gives way to, and its payload (32.2 rule 3 (e); 34.2 rule 1)."""
        pre = self.precursor()
        is_precursor = pre is not None and step.cls == pre["role"] and step.nonce == pre["nonce"]
        plans = [self.plan(key) for key in made]
        for p in plans:
            if p.get("action") == OFFER_SPONSORED_WRITES:
                # (spec 39.2 rule 1 (c)): the writes through PI.migration_nonce, for one payload.
                return ONE_PAYLOAD_BUNDLE, p.get("payload")
            if p.get("answer") == ANSWER_ACT_WITHOUT_PRECURSOR:
                activation = (p.get("action") == OFFER_ACTIVATION_ONLY
                              or p.get("first") == "ACTIVATION_OF_THE_CURRENT_KEY"
                              or (p.get("payload") or {}).get("first") == "ACTIVATION_OR_ACTIVATING_ROTATE_AT_ACCOUNT_NONCE")
                return (ACTIVATE_CURRENT_KEY_FIRST if activation else ACCOUNT_NONCE_ACT_FIRST), p.get("payload")
        if is_precursor and plans and all(p.get("answer") == ANSWER_PRECURSOR_WITH_ITS_ACTS for p in plans):
            payloads = [p["payload"] for p in plans]
            if len(payloads) == 1:
                payload = dict(payloads[0])
            else:
                kinds = sorted({x["kind"] for x in payloads})
                payload = {**payloads[0], "kind": "_AND_".join(kinds), "parts": payloads}
            if any(x["kind"] == "ROTATE" for x in payloads):
                rotates = [self.auths[key].nonce for key in made if self.auths[key].kind == "ROTATE"]
                payload.setdefault("rotate_through_account_nonce", max(rotates))
            return ONE_PAYLOAD_BUNDLE, payload
        if plans and all(p.get("answer") == ANSWER_WAIT for p in plans):
            return HOLD_WRITE_WAIT_FINALITY, None
        return FOLLOW_RULE_7B_8B_PATH, None

    def override_as(self):
        """How the override at the head is offered (spec 34.2 rule 2, last sentences)."""
        if state_gate(self.head) != "OVERRIDE":
            return None
        pre = self.precursor()
        if pre is None:
            return "ALONE_NOT_A_PRECURSOR"
        above = [key for key in self.order if self.auths[key].kind == "PI" and self.auths[key].nonce > self.hs.mn]
        if not above and not self.judge([pre["step"]]).made:
            return "ALONE_NOT_A_PRECURSOR"
        if self.hold() is not None:
            return "AFTER_THE_WAIT_OF_34_2_RULE_1_G"
        return "WITH_ITS_ACTS_AS_ONE_PAYLOAD_34_2_RULE_1"

    def preemption_report(self, steps, between, balance_stated):
        """Each single member of K or O at the account nonce placed before the payload: the end it leaves."""
        hs, t0, cfg = self.hs, self.t0, self.cfg
        p = self.problem(steps)
        moves = [m for m in a_moves(p, hs, t0) if m.cls in ("ACTIVATION", "ORDINARY", "ECDSA", "ENROLL")]
        moves += [step for key, step, _ in self.k if key[0] == "TX"]
        out, seen = [], set()
        for m in moves:
            if not model_valid(m, hs, t0, cfg):
                continue
            # The precursor lands where it still applies (A, which wants it to land, leaves the balance it
            # needs); after a member that A signs, every later element paid by a is popped (34.2 rule 1 (f)).
            end = model_apply(m, hs, t0, cfg)
            for index, step in enumerate(steps):
                if not model_valid(step, end, t0, cfg) or (index and m.by_a and step.a_paid):
                    continue
                end = model_apply(step, end, t0, cfg)
            entry_key = (m.label, end)
            if entry_key in seen:
                continue
            seen.add(entry_key)
            left = [list(key) for key in between if binds(self.targets[key], end, t0, cfg)]
            out.append({"by": m.label, "end_state": self.as_state(end).to_dict(),
                        "left_includable": [x for x in left if self.auths[tuple(x)].kind == "PI"],
                        "rotates_left_includable_race_stated": [x for x in left
                                                                if self.auths[tuple(x)].kind != "PI"]})
        return out


class AuthorizationTracker:
    """Append-only authorization/carrier history, with per-variant retirement.

    Finished records are retained for inspection and for late carrier discovery.
    Losing the entire metadata file is indistinguishable from D-1 first use; it
    cannot reconstruct unknown authorizations. Corrupt existing files raise.
    `override_margin` (seconds) is the margin of l. 1765 that spec 34.2
    rule 1 (g) keeps before deadline(a); it is configuration, not stored metadata.
    `slot` (seconds) is the chain's SLOT (12 s on mainnet, l. 1230): a carrier counts
    as one that a block after the head can include only at head.timestamp + slot or later.
    """
    def __init__(self, directory, *, override_margin=OVERRIDE_MARGIN_DEFAULT, slot=SLOT_DEFAULT):
        _uint(override_margin, UINT64_MAX, "override margin")
        _uint(slot, UINT64_MAX, "slot")
        if slot == 0:
            raise ValueError("slot must be positive")
        self.override_margin = override_margin
        self.slot = slot
        self.directory = Path(directory)
        self.directory.mkdir(parents=True, exist_ok=True)
        self.path = self.directory / "authorizations.json"
        self.lock_path = self.directory / "authorizations.lock"
        self.epochs = WalletEpochStore(directory)

    def _read(self):
        if not self.path.exists():
            return {"schema": 1, "scopes": {}}
        try:
            d = json.loads(self.path.read_text(encoding="utf-8"))
            if d["schema"] != 1 or not isinstance(d["scopes"], dict):
                raise ValueError("schema")
            for key, s in d["scopes"].items():
                _hex(key, 32, "scope")
                for name in ("groups", "exposed", "heads", "finalized"):
                    if not isinstance(s[name], dict):
                        raise ValueError(name)
                for gid, variants in s["groups"].items():
                    if not isinstance(variants, dict) or not variants:
                        raise ValueError("variants")
                    for vid, record in variants.items():
                        a = Authorization.from_dict(record["authorization"])
                        if gid != a.group_id or vid != a.variant_id:
                            raise ValueError("authorization identity")
                        if not isinstance(record["observations"], list) or not record["carriers"]:
                            raise ValueError("carrier history")
                        for h, raw in record["carriers"].items():
                            if hashlib.sha256(bytes.fromhex(raw)).hexdigest() != h:
                                raise ValueError("carrier hash")
                        # Where each carrier is (absent from older files: UNSTATED).
                        custody = record.setdefault("custody", {})
                        if not isinstance(custody, dict) or any(h not in record["carriers"] or c not in CUSTODIES
                                                                for h, c in custody.items()):
                            raise ValueError("carrier custody")
                        if record["ended"] is not None:
                            f = AccountState.from_dict(record["ended"]["state"])
                            if end_reason(a, f) != record["ended"]["reason"] or end_reason(a, f) is None:
                                raise ValueError("retirement condition")
                for states in (s["heads"], s["finalized"]):
                    for key, raw in states.items():
                        if AccountState.from_dict(raw).account.key != key:
                            raise ValueError("state identity")
                for key, exposures in s["exposed"].items():
                    _hex(key, 32, "account key")
                    for commitment, reason in exposures.items():
                        _hex(commitment, 32, "exposed commitment")
                        if not isinstance(reason, str) or not reason:
                            raise ValueError("exposure reason")
                # Commitments linked to their derivation epoch (absent from older files).
                links = s.setdefault("links", {})
                if not isinstance(links, dict):
                    raise ValueError("links")
                for commitment, epoch in links.items():
                    _hex(commitment, 32, "linked commitment")
                    _uint(epoch, UINT32_MAX, "linked epoch")
                # Stealth enrollments found at chain-finalized blocks.
                stealth = s.setdefault("stealth", {})
                if not isinstance(stealth, dict):
                    raise ValueError("stealth")
                for key, found in stealth.items():
                    _hex(found["commitment"], 32, "stealth commitment")
                    if AccountState.from_dict(found["state"]).account.key != key:
                        raise ValueError("stealth state identity")
                # One-payload bundles (item 3.1); optional in older metadata.
                bundles = s.setdefault("bundles", {})
                if not isinstance(bundles, dict):
                    raise ValueError("bundles")
                for bid, b in bundles.items():
                    _hex(bid, 32, "bundle id")
                    if not isinstance(b["members"], list):
                        raise ValueError("bundle members")
                    for gid, vid in b["members"]:
                        if vid not in s["groups"].get(gid, {}):
                            raise ValueError("bundle member is not a tracked authorization")
                    others = b["activations"] + b.get("transactions", [])
                    for h in others:
                        _hex(h, 32, "carrier hash")
                    if len(b["members"]) + len(others) < 2:
                        raise ValueError("bundle size")
                    if (b["fee_path"] not in FEE_PATHS or b["route"] not in ONE_PAYLOAD_ROUTES
                            or b.get("delivery", "ONE_PAYLOAD") not in DELIVERIES):
                        raise ValueError("bundle route")
                    _hex(b["last_head"], 32, "bundle head")
                # Transactions of a that are no binding authorization (members of K).
                transactions = s.setdefault("transactions", {})
                if not isinstance(transactions, dict):
                    raise ValueError("transactions")
                for txid, r in transactions.items():
                    tx = Transaction.from_dict(r["transaction"])
                    if tx.tx_id != txid or not r["carriers"]:
                        raise ValueError("transaction identity")
                    for h, raw in r["carriers"].items():
                        if hashlib.sha256(bytes.fromhex(raw)).hexdigest() != h:
                            raise ValueError("transaction carrier hash")
                    if any(h not in r["carriers"] or c not in CUSTODIES for h, c in r["custody"].items()):
                        raise ValueError("transaction custody")
                    if r["ended"] is not None and AccountState.from_dict(r["ended"]["state"]).account_nonce \
                            <= tx.account_nonce:
                        raise ValueError("transaction retirement")
                # Blocks seen above F (starts of 34.2 rule 1 (a)), and a's published secp256k1 key.
                seen = s.setdefault("seen", {})
                if not isinstance(seen, dict):
                    raise ValueError("seen")
                for key, blocks in seen.items():
                    for block_hash, raw in blocks.items():
                        state = AccountState.from_dict(raw)
                        if state.account.key != key or state.block_hash != block_hash:
                            raise ValueError("seen state identity")
                published = s.setdefault("published", {})
                if not isinstance(published, dict) or any(not isinstance(v, str) or not v
                                                          for v in published.values()):
                    raise ValueError("published")
            return d
        except (OSError, KeyError, ValueError, TypeError, AttributeError) as exc:
            raise MetadataError("invalid authorization metadata; not reset") from exc

    @staticmethod
    def _scope(d, scope):
        if not isinstance(scope, DerivationScope):
            raise ValueError("derivation scope required")
        return d["scopes"].setdefault(scope.key, {"groups": {}, "exposed": {}, "heads": {},
                                                  "finalized": {}, "bundles": {}, "links": {},
                                                  "stealth": {}, "transactions": {}, "seen": {},
                                                  "published": {}})

    # ----------------------------------------------------------------- exposure
    @staticmethod
    def _key_exposed(s, commitment, epochs):
        """The key of `commitment` is known exposed: by commitment, or through a recorded
        epoch linked to it (a link, or a tracked authorization that commits it with its epoch)."""
        h = commitment.hex()
        if any(h in values for values in s["exposed"].values()):
            return True
        if s["links"].get(h) in epochs:
            return True
        for variants in s["groups"].values():
            for record in variants.values():
                a = Authorization.from_dict(record["authorization"])
                if a.commitment == commitment and a.epoch is not None and a.epoch in epochs:
                    return True
        return False

    @staticmethod
    def _exposed(s, auth, epochs):
        """The one exposure predicate of a tracked authorization.

        Its own recorded epoch, or its key known exposed by any record (_key_exposed), so
        that a record by epoch reaches an authorization learned without its epoch.
        """
        return ((auth.epoch is not None and auth.epoch in epochs)
                or AuthorizationTracker._key_exposed(s, auth.commitment, epochs))

    @staticmethod
    def _binds_exposed_key(s, auth, epochs):
        """(spec 35.3 rule 1): 'a tracked authorization whose key is exposed' in 34.2 rule 1 (a) is a
        carrier that binds an exposed key. A tracked variant is one carrier effect (for a rotate of (a, n): its
        activating flag, the commitment it binds and its signer), so the predicate is _exposed of that carrier's
        own authorization, never of its index (a, n)."""
        return AuthorizationTracker._exposed(s, auth, epochs)

    @staticmethod
    def _key_epoch(s, auth):
        """The epoch of the key that `auth` commits where the device knows it (its own field, a link, or
        a tracked authorization that commits the same key with its epoch); None otherwise."""
        if auth.epoch is not None:
            return auth.epoch
        linked = s["links"].get(auth.commitment.hex())
        if linked is not None:
            return linked
        for variants in s["groups"].values():
            for record in variants.values():
                known = record["authorization"]
                if known["commitment"] == auth.commitment.hex() and known["epoch"] is not None:
                    return known["epoch"]
        return None

    @staticmethod
    def _plan_key_check(s, index, auth, anchor, si):
        """(spec 35.2 rule 1 (b), (c)): the key of the write x_index of a payload plan anchored at
        `anchor` (B), read against its planning state `si` (S_index). A same-key write matches the commitment of
        S_i, not that of B; a key that x_i newly selects uses e = m_i, the migration_nonce of S_i. A rotate binds
        the account nonce instead (31.2 rule 2, a case that rule 5 treats), and a key whose epoch the device does
        not know (a key not derived from the seed, 31.2 rule 8 (b)) is the caller's. Returns the key's role."""
        if auth.kind == "ROTATE":
            return "ROTATE_BINDS_THE_ACCOUNT_NONCE"
        if si.commitment is not None and auth.commitment == si.commitment:
            return KEY_SAME
        if index and anchor.commitment is not None and auth.commitment == anchor.commitment:
            raise ValueError(
                f"PAYLOAD_ELEMENT_NOT_PREPARED_AGAINST_ITS_PLANNING_STATE: element {index} commits the key that is "
                f"current at the anchor B, not the key of its planning state S_{index} (migration_nonce {si.migration_nonce}); "
                "a same-key write matches the pq_pk_commit of S_i, not that of B, and a key that x_i newly selects "
                "is the key of epoch m_i (spec 35.2 rule 1 (b), (c); vector V23-W-1)")
        epoch = AuthorizationTracker._key_epoch(s, auth)
        if epoch is not None and epoch != si.migration_nonce:
            raise ValueError(
                f"PAYLOAD_KEY_NOT_SELECTED_AT_ITS_PLANNING_STATE: element {index} commits the seed key of epoch {epoch}, "
                f"which is neither the key of its planning state S_{index} nor the key that it newly selects there: a key "
                f"that x_i newly selects uses e = m_i = {si.migration_nonce} (spec 35.2 rule 1 (c), 36.2; 31.2 "
                "rule 2; vector V24-W-1)")
        return KEY_NEW if epoch is not None else KEY_UNKNOWN

    @staticmethod
    def _own_commitment(s, commitment):
        """The device knows `commitment` as a key of its seed: linked to an epoch, or committed by a
        tracked authorization that carries its epoch (only a derivation gives one)."""
        h = commitment.hex()
        if h in s["links"]:
            return True
        return any(Authorization.from_dict(r["authorization"]).commitment == commitment
                   and r["authorization"]["epoch"] is not None
                   for variants in s["groups"].values() for r in variants.values())

    def _link_locked(self, s, scope, commitment, epoch, epochs, reason):
        """Persist that `commitment` is the key of `epoch`; returns True if the file changed.

        A tracked authorization that commits it without an epoch learns that epoch, and an
        exposure known by commitment reaches the epoch ledger at once (31.2 rule 9, 'known
        otherwise, in which case a wallet that keeps records adds it'). A commitment linked
        to two epochs is conflicting metadata.
        """
        h = commitment.hex()
        old = s["links"].get(h)
        if old is not None and old != epoch:
            raise ValueError("conflicting derivation metadata: a commitment linked to two epochs")
        changed = old is None
        for variants in s["groups"].values():
            for record in variants.values():
                a = Authorization.from_dict(record["authorization"])
                if a.commitment != commitment:
                    continue
                if a.epoch is not None and a.epoch != epoch:
                    raise ValueError("conflicting derivation metadata")
                if a.epoch is None:
                    record["authorization"] = replace(a, epoch=epoch).to_dict()
                    changed = True
        s["links"][h] = epoch
        if any(h in values for values in s["exposed"].values()) and epoch not in epochs:
            self.epochs.mark_compromised(scope, epoch, reason)
            epochs.add(epoch)
        return changed

    def link_key(self, scope, commitment, epoch,
                 reason="verified key whose commitment is known exposed"):
        """Link `commitment` to its verified derivation epoch; report whether that key is exposed.

        `epoch` must come from a commitment-matching scan, or from the
        adapter's derivation from the seed. The link is persisted, so that a later record of
        that epoch reaches every tracked authorization that commits the key; when the key is
        known exposed, its epoch is persisted in the epoch ledger (union-only) before this
        returns True, and the caller then refuses to use the key.
        """
        _bytes32(commitment, "linked commitment")
        _uint(epoch, UINT32_MAX, "linked epoch")
        epochs = set(self.epochs.security(scope).compromised_epochs)
        with _locked(self.lock_path):
            d = self._read(); s = self._scope(d, scope)
            changed = self._link_locked(s, scope, commitment, epoch, epochs, reason)
            exposed = self._key_exposed(s, commitment, epochs)
            if exposed and epoch not in epochs:
                self.epochs.mark_compromised(scope, epoch, reason)
            if changed:
                _atomic_json(self.path, d)
        return exposed

    def link_current_key(self, scope, commitment, epoch,
                         reason="verified current key whose commitment is known exposed"):
        """Link the verified current key to its derivation epoch."""
        return self.link_key(scope, commitment, epoch, reason)

    def linked_epochs(self, scope):
        """The epochs that some commitment is linked to in this scope."""
        with _locked(self.lock_path):
            return set(self._scope(self._read(), scope)["links"].values())

    def key_exposed(self, scope, commitment):
        """Whether the key of `commitment` is known exposed in this scope (read-only)."""
        _bytes32(commitment, "commitment")
        epochs = set(self.epochs.security(scope).compromised_epochs)
        with _locked(self.lock_path):
            return self._key_exposed(self._scope(self._read(), scope), commitment, epochs)

    def own_commitment(self, scope, commitment):
        """Whether the device knows `commitment` as a key of its seed (linked to an epoch, or committed by a
        tracked authorization that carries its epoch); the predicate of l. 420 'a commitment the wallet created'.
        Read-only."""
        _bytes32(commitment, "commitment")
        with _locked(self.lock_path):
            return self._own_commitment(self._scope(self._read(), scope), commitment)

    @staticmethod
    def _require_observed_head(s, head, what):
        if not isinstance(head, AccountState):
            raise ValueError("head AccountState required")
        if s["heads"].get(head.account.key) != head.to_dict():
            raise ValueError(f"stale or unobserved {what} head")

    @staticmethod
    def _live_records(s, account):
        out = []
        for gid, variants in s["groups"].items():
            for vid, record in variants.items():
                a = Authorization.from_dict(record["authorization"])
                if a.account == account and record["ended"] is None:
                    out.append((gid, vid, a, record))
        return out

    @staticmethod
    def _require_confirmation(head, identity, revived, remedy, payload, confirm, no_one_payload_path, what,
                              witness=None):
        """Raise RevivalWarning unless the owner's confirmation `confirm` matches this revival.

        Not a bundle remedy: the token binds the head, the candidate and the revived
        set. A bundle remedy (spec 34.2 rule 1 (c)): no lone route without the caller's
        statement that no path gives one payload; then the gap is stated, and only the token
        of that statement confirms it. A held fresh precursor (34.2 rule 1 (g)) has
        no token at all.
        """
        if remedy == HOLD_FRESH_PRECURSOR:
            raise RevivalWarning(revived, None, remedy, payload=payload, what=what, witness=witness)
        if remedy != ONE_PAYLOAD_BUNDLE:
            token = _digest(["confirm-revival", head.to_dict(), *identity, revived])
            if confirm != token:
                raise RevivalWarning(revived, token, remedy, payload=payload, what=what, witness=witness)
            return
        if no_one_payload_path is not True:
            raise RevivalWarning(revived, None, remedy, payload=payload, what=what, witness=witness)
        gap = GAP_STATEMENT.format(count=len(revived), what=what)
        token = _digest(["confirm-split", head.to_dict(), *identity, revived, "NO_ONE_PAYLOAD_PATH"])
        if confirm != token:
            raise RevivalWarning(revived, token, remedy, payload=payload, gap=gap, what=what, witness=witness)

    # -------------------------------------------------------------- recording
    def _record_locked(self, s, scope, auth, carrier, custody="UNSTATED"):
        if not isinstance(carrier, bytes) or not carrier:
            raise ValueError("nonempty raw carrier/proof bytes required")
        if custody not in CUSTODIES:
            raise ValueError("unknown custody")
        variants = s["groups"].setdefault(auth.group_id, {})
        r = variants.setdefault(auth.variant_id, {"authorization": auth.to_dict(), "carriers": {}, "observations": [],
                                                  "ended": None, "custody": {}})
        previous = Authorization.from_dict(r["authorization"])
        if previous.epoch is not None and auth.epoch is not None and previous.epoch != auth.epoch:
            raise ValueError("conflicting derivation metadata")
        if previous.epoch is None and auth.epoch is not None:
            r["authorization"] = auth.to_dict()
        effective = Authorization.from_dict(r["authorization"])
        linked = s["links"].get(effective.commitment.hex())
        if linked is not None and effective.epoch is not None and linked != effective.epoch:
            raise ValueError("conflicting derivation metadata")
        if linked is not None and effective.epoch is None:
            effective = replace(effective, epoch=linked)   # the link gives the epoch
            r["authorization"] = effective.to_dict()
        if effective.epoch is not None and any(effective.commitment.hex() in values for values in s["exposed"].values()):
            self.epochs.mark_compromised(scope, effective.epoch, "known exposed binding key")
        h = hashlib.sha256(carrier).hexdigest()
        if h in r["carriers"] and r["carriers"][h] != carrier.hex():
            raise MetadataError("carrier hash collision")
        r["carriers"][h] = carrier.hex()
        r.setdefault("custody", {})[h] = _merge_custody(r["custody"].get(h), custody)
        if auth.kind == "ENROLL":
            # A 0x7d carries a's secp256k1 signature (l. 45): the key is published once one exists.
            s["published"].setdefault(auth.account.key, "a 0x7d of a is tracked (l. 45)")
        f = s["finalized"].get(auth.account.key)
        if f is not None and r["ended"] is None:
            reason = end_reason(auth, AccountState.from_dict(f))
            if reason is not None:
                r["ended"] = {"reason": reason, "state": f}

    def record(self, scope, auth: Authorization, carrier: bytes, *, custody="UNSTATED"):
        """Track a binding authorization and one carrier of it (32.2 rule 1).

        (34.2 rule 1 (g)): `custody` says where the carrier is. Only a
        carrier in a block of any branch or in a pool, or handed to a relay, a builder, a sponsor
        or an aggregator (CUSTODY_HELD_BY_A: IN_BLOCK, IN_POOL, BROADCAST, RELAY, BUILDER,
        SPONSOR, AGGREGATOR) counts as one that A holds; PROVING_SERVICE is in other hands but not
        A's; UNSTATED (the default) and PREPARED are not out. Recording alone never makes a write
        one that A holds. export() and export_bundle() record their own writes themselves before
        delivery (EXPORTING, then EXPORTED once delivered); a caller records a carrier that it
        broadcasts itself, hands over, or learns of on chain, with its custody. Every tracked
        carrier is a member of K for 34.2 rule 1 (a), whatever its custody.
        """
        if not isinstance(carrier, bytes) or not carrier:
            raise ValueError("nonempty raw carrier/proof bytes required")
        with _locked(self.lock_path):
            d = self._read(); s = self._scope(d, scope)
            self._record_locked(s, scope, auth, carrier, custody)
            _atomic_json(self.path, d)
        return auth.group_id, auth.variant_id

    def _record_transaction_locked(self, s, tx, carrier, custody):
        if not isinstance(tx, Transaction):
            raise ValueError("Transaction required")
        if not isinstance(carrier, bytes) or not carrier:
            raise ValueError("nonempty raw transaction bytes required")
        if custody not in CUSTODIES:
            raise ValueError("unknown custody")
        r = s["transactions"].setdefault(tx.tx_id, {"transaction": tx.to_dict(), "carriers": {}, "custody": {},
                                                    "ended": None})
        h = hashlib.sha256(carrier).hexdigest()
        if h in r["carriers"] and r["carriers"][h] != carrier.hex():
            raise MetadataError("carrier hash collision")
        r["carriers"][h] = carrier.hex()
        r["custody"][h] = _merge_custody(r["custody"].get(h), custody)
        if tx.kind == "ECDSA":
            s["published"].setdefault(tx.account.key, "an ECDSA transaction of a is known (l. 45)")
        f = s["finalized"].get(tx.account.key)
        if f is not None and r["ended"] is None and AccountState.from_dict(f).account_nonce > tx.account_nonce:
            r["ended"] = {"reason": "ACCOUNT_NONCE_CONSUMED", "state": f}
        return tx.tx_id

    def record_transaction(self, scope, tx: Transaction, carrier: bytes, *, custody="UNSTATED"):
        """A transaction of a that is no binding authorization.

        34.2 rule 1 (a): K holds every transaction of a that has left one of the owner's devices,
        such as an activation or an ordinary 0x7c, and every one seen in a block of any branch or
        in a pool. The wallet records each that it sends, hands over or sees, with its custody (as
        record()); the adapter's signers and export_bundle record theirs. Its tracking ends at a
        chain-finalized block whose account nonce is above its own.
        """
        with _locked(self.lock_path):
            d = self._read(); s = self._scope(d, scope)
            txid = self._record_transaction_locked(s, tx, carrier, custody)
            _atomic_json(self.path, d)
        return txid

    def mark_secp256k1_published(self, scope, account, reason):
        """(34.2 rule 1 (g), reading (h)): the caller knows that a's secp256k1 public key has been
        published (including typed-data signatures, 7702 tuples, co-signatures and off-chain disclosure,
        §43.2 rule 3). The component also infers it from a tracked
        0x7d or ECDSA transaction of a and from a LEGACY state with a nonzero account nonce."""
        if not isinstance(account, Account) or not isinstance(reason, str) or not reason:
            raise ValueError("account and reason required")
        with _locked(self.lock_path):
            d = self._read(); s = self._scope(d, scope)
            s["published"].setdefault(account.key, reason)
            _atomic_json(self.path, d)

    def migration_choice(self, scope, head, *, knowingly_enroll=False):
        """Select the LEGACY migration path from known public-key exposure (§43.2 rule 3).

        Call mark_secp256k1_published for every disclosure the wallet knows about,
        including off-chain signatures. A caller choosing enrollment against the
        seed-proof default must first show its public-key exposure risk to the owner.
        """
        if not isinstance(head, AccountState) or head.mode != "LEGACY":
            raise ValueError("LEGACY_ACCOUNT_STATE_REQUIRED")
        if type(knowingly_enroll) is not bool:
            raise ValueError("explicit enrollment choice must be boolean")
        if head.effective_code_kind not in ("EMPTY", "DELEGATION"):
            raise ValueError("NOT_AN_EOA")
        if head.legacy_seed_proof_from_t0 and head.protocol_time is None:
            raise ValueError("STATE_GATE_UNEVALUATED")
        if head.protocol_time is not None and head.timestamp < head.protocol_time:
            raise ValueError("FORK_NOT_ACTIVE")
        gate = state_gate(head)
        if gate == "FROZEN":
            return "SEED_PROOF"
        epochs = set(self.epochs.security(scope).compromised_epochs)
        with _locked(self.lock_path):
            s = self._scope(self._read(), scope)
            published = _Model(self, s, epochs, head).published
        if gate == "PRE_T_LEGACY" and not published and not knowingly_enroll:
            return "SEED_PROOF"
        return "ENROLL"

    def _set_custody_locked(self, s, auths, transactions, custody):
        for auth, carrier in auths:
            r = s["groups"][auth.group_id][auth.variant_id]
            h = hashlib.sha256(carrier).hexdigest()
            r["custody"][h] = _merge_custody(r["custody"].get(h), custody)
        for tx, carrier in transactions:
            r = s["transactions"][tx.tx_id]
            h = hashlib.sha256(carrier).hexdigest()
            r["custody"][h] = _merge_custody(r["custody"].get(h), custody)

    def _delivered(self, scope, auths, transactions):
        """After a delivery returned: the carriers are with a relay, a builder or a pool (EXPORTED)."""
        with _locked(self.lock_path):
            d = self._read(); s = self._scope(d, scope)
            self._set_custody_locked(s, auths, transactions, "EXPORTED")
            _atomic_json(self.path, d)

    def export(self, scope, auth, carrier, deliver, *, head, after=None, confirm_revival=None,
               no_one_payload_path=False, confirm_move_away=None):
        """Check, persist, then let the caller transmit; failed sends retain the record.

        A write that commits a key known exposed is refused
        (WRITE_KEY_EXPOSED; its epoch is persisted first when its commitment is exposed),
        and a rotate signed by such a key leaves only with confirm_move_away, the token of
        the MoveAwayWarning (31.2 rule 7 (b)). Where its remedy is not a bundle, the
        warning's token, passed back as confirm_revival after the owner's explicit
        confirmation, delivers the write alone. Where it is ONE_PAYLOAD_BUNDLE, the write
        leaves alone only with no_one_payload_path=True and the token of the warning that
        states the gap (spec 34.2 rule 1 (c)); otherwise it goes in a
        OnePayloadBundle. Where it is HOLD_FRESH_PRECURSOR (34.2 rule 1 (g)), the
        write does not leave until the tracked authorization meets a condition of 32.2 rule 2.
        The write is judged by the condition of 34.2 rule 1 (a) (the search over the
        head, F and the seen blocks with K and O), and held by (g) where it is a precursor that A
        does not hold, whether or not it makes anything includable at the head; `after`, if
        given, must still equal the state after the write alone. The carrier is recorded
        EXPORTING before delivery and EXPORTED after it. The calling encoder/decoder must bind
        auth to these carrier bytes; this boundary parses no transaction. (spec
        35.2 rule 1 (e)): a write whose nonce is above the head's (a PI above its migration_nonce,
        a 0x7d or a rotate above its account nonce) was prepared against a later planning state
        or a stale anchor and is refused before anything is recorded
        (PREPARED_AGAINST_A_LATER_PLANNING_STATE); a lone write is a payload of one element whose
        planning state is the head.
        """
        if not callable(deliver):
            raise ValueError("delivery callback required")
        if not isinstance(carrier, bytes) or not carrier:
            raise ValueError("nonempty raw carrier/proof bytes required")
        if type(no_one_payload_path) is not bool:
            raise ValueError("no_one_payload_path must be boolean")
        _lone_preview(auth, head, after)
        epochs = set(self.epochs.security(scope).compromised_epochs)
        with _locked(self.lock_path):
            d = self._read(); s = self._scope(d, scope)
            self._require_observed_head(s, head, "export")
            if self._exposed(s, auth, epochs):
                if auth.epoch is not None and self._link_locked(
                        s, scope, auth.commitment, auth.epoch, epochs, "known exposed binding key"):
                    _atomic_json(self.path, d)
                raise ValueError("WRITE_KEY_EXPOSED: this write commits a key known exposed; it is not "
                                 "sent (31.2 rule 7 (a)-(b)); a move away from that key commits another key")
            if auth.kind == "ROTATE" and self._key_exposed(s, auth.signer_commitment, epochs):
                token = _digest(["confirm-move-away", head.to_dict(), auth.group_id, auth.variant_id])
                if confirm_move_away != token:
                    raise MoveAwayWarning(token)
            if _above_the_head(auth, head):
                # (spec 35.2 rule 1 (e)): preparing an element against a later planning state does not
                # make it sendable alone; nothing is recorded or delivered (V23-W-4).
                raise ValueError(PREPARED_LATER)
            model = _Model(self, s, epochs, head)
            step = model.step_of(auth, "PAYLOAD_WRITE", "W:0")
            identity = [auth.group_id, auth.variant_id]
            pre = model.precursor()
            # A write at the precursor's nonce is held where (g) holds: hold() is None whenever A holds an
            # includable carrier of that nonce, this write's own carrier included.
            hold = (model.hold() if pre is not None and step.cls == pre["role"] and step.nonce == pre["nonce"]
                    else None)
            if hold is not None:
                revived = [list(key) for key in hold["pis"]]
                self._require_confirmation(head, identity, revived, HOLD_FRESH_PRECURSOR, model.hold_payload(hold),
                                           confirm_revival, no_one_payload_path, "write")
            verdict = model.judge([step])
            if verdict.made:
                made = list(verdict.made)
                remedy, payload = model.write_remedy(step, made)
                self._require_confirmation(head, identity, [list(k) for k in made], remedy, payload, confirm_revival,
                                           no_one_payload_path, "write", witness=verdict.made[made[0]])
            self._record_locked(s, scope, auth, carrier, "EXPORTING")
            _atomic_json(self.path, d)
        result = deliver(carrier)
        self._delivered(scope, [(auth, carrier)], [])
        return result

    def check_activation(self, scope, head, commitment, *, confirm_revival=None, no_one_payload_path=False):
        """The revival check of a lone activation at the observed head.

        Returns the state after the activation (activated, account nonce + 1). The
        lone activation is judged by the condition of 34.2 rule 1 (a) (members of K include the
        owner's transactions that have left a device, so a tracked rotate several account nonces
        above is reached through them); where it fails, RevivalWarning names remedy
        ONE_PAYLOAD_BUNDLE with the shortest admissible payload: the activation, then
        transactions of a through `through_account_nonce` (34.2 rule 1 (e): never alone). The lone
        activation is confirmed only as rule 1 (c) states for a write. Nothing is recorded.
        """
        _bytes32(commitment, "activated commitment")
        if type(no_one_payload_path) is not bool:
            raise ValueError("no_one_payload_path must be boolean")
        after = activation_preview(head) if isinstance(head, AccountState) else None
        if after is None or head.commitment != commitment:
            raise ValueError("ACTIVATION_NOT_APPLICABLE_AT_HEAD")
        epochs = set(self.epochs.security(scope).compromised_epochs)
        with _locked(self.lock_path):
            d = self._read(); s = self._scope(d, scope)
            self._require_observed_head(s, head, "activation")
            if self._key_exposed(s, commitment, epochs):
                raise ValueError("CURRENT_KEY_COMPROMISED")
            model = _Model(self, s, epochs, head)
            step = Step("ACTIVATION", head.account_nonce, commitment, label="PAYLOAD_ACTIVATION", ident="W:0")
            verdict = model.judge([step])
            if verdict.made:
                made = list(verdict.made)
                ok, through, steps = model.acts_through([step], made)
                payload = (bundle_payload("ACCOUNT_NONCE", sender="UNACTIVATED_PQ", through_account_nonce=through,
                                          plan=model.plan_of(steps))
                           if ok and through is not None else None)
                self._require_confirmation(head, ["ACTIVATION", head.account_nonce, commitment.hex()],
                                           [list(k) for k in made], ONE_PAYLOAD_BUNDLE if payload else
                                           FOLLOW_RULE_7B_8B_PATH, payload, confirm_revival, no_one_payload_path,
                                           "activation", witness=verdict.made[made[0]])
        return after

    def activation_acts_needed(self, scope, head, commitment):
        """The account nonce through which transactions must follow the activation at the
        head, as the offers name it: the payload meets 34.2 rule 1 (a) and, once in a chain-finalized block,
        discharges what the lone activation makes includable and every tracked rotate whose key is exposed at or
        above the account nonce (its first act is a transaction at its account nonce, 32.2 rule 3; 34.2 rule 1
        (b), (e)). None when the lone activation does all that. Raises ACTIVATION_NO_ADMISSIBLE_PAYLOAD when no
        such payload exists."""
        _bytes32(commitment, "activated commitment")
        epochs = set(self.epochs.security(scope).compromised_epochs)
        with _locked(self.lock_path):
            d = self._read(); s = self._scope(d, scope)
            self._require_observed_head(s, head, "activation")
            model = _Model(self, s, epochs, head)
            step = Step("ACTIVATION", head.account_nonce, commitment, label="PAYLOAD_ACTIVATION", ident="W:0")
            made = list(model.judge([step]).made)
            made += [key for key in model.order if model.auths[key].kind == "ROTATE"
                     and model.auths[key].nonce >= head.account_nonce and key not in made]
            if not made:
                return None
            ok, through, _ = model.acts_through([step], made)
            if not ok:
                raise ValueError("ACTIVATION_NO_ADMISSIBLE_PAYLOAD: " + NO_PAYLOAD_MEETS)
            return through

    def mark_exposed(self, scope, account, commitment, reason):
        _bytes32(commitment, "exposed commitment")
        if not isinstance(reason, str) or not reason:
            raise ValueError("exposure reason required")
        with _locked(self.lock_path):
            d = self._read(); s = self._scope(d, scope)
            # A known derivation's exposure is seed/path-wide, not network-wide.
            # Save the epoch ban before the supplemental commitment observation.
            for variants in s["groups"].values():
                for record in variants.values():
                    auth = Authorization.from_dict(record["authorization"])
                    if auth.commitment == commitment and auth.epoch is not None:
                        self.epochs.mark_compromised(scope, auth.epoch, reason)
            linked = s["links"].get(commitment.hex())
            if linked is not None:
                self.epochs.mark_compromised(scope, linked, reason)
            s["exposed"].setdefault(account.key, {}).setdefault(commitment.hex(), reason)
            _atomic_json(self.path, d)

    def records(self, scope):
        with _locked(self.lock_path):
            return self._scope(self._read(), scope)["groups"]

    def transactions(self, scope):
        """The recorded transactions of a that are no binding authorization."""
        with _locked(self.lock_path):
            return self._scope(self._read(), scope)["transactions"]

    @staticmethod
    def _index_view(s, epochs, gid, variants):
        carriers = []
        for vid, r in sorted(variants.items()):
            a = Authorization.from_dict(r["authorization"])
            exposed = AuthorizationTracker._binds_exposed_key(s, a, epochs)
            for h in sorted(r["carriers"]):
                carriers.append({"carrier": h, "variant": vid, "activating": a.activating,
                                 "binds": a.commitment.hex(), "signer": a.signer_commitment.hex(),
                                 "key_exposed": exposed, "custody": r.get("custody", {}).get(h, "UNSTATED"),
                                 "ended": None if r["ended"] is None else r["ended"]["reason"]})
        return carriers

    def rotate_index(self, scope, account, account_nonce):
        """(spec 35.3 rule 1): the authorization (a, n) of 32.2 rule 1 (b) as an index over the
        0x7cs that call rotate at account nonce n, activating or not. For each carrier the device keeps whether it
        activates, the commitment it binds and whether that key is exposed; each ends on its own (nonce(a) > n at
        F ends every carrier, final(a) and activated(a) at F an activating carrier only), and (a, n) ends when
        every carrier of it that the device knows has ended; a carrier learned later is tracked and judged on its
        own. Read-only."""
        if not isinstance(account, Account):
            raise ValueError("account required")
        _uint(account_nonce, UINT64_MAX, "rotate account nonce")
        gid = _digest([asdict(account), "ROTATE", account_nonce])
        epochs = set(self.epochs.security(scope).compromised_epochs)
        with _locked(self.lock_path):
            s = self._scope(self._read(), scope)
            carriers = self._index_view(s, epochs, gid, s["groups"].get(gid, {}))
        live = [c for c in carriers if c["ended"] is None]
        return {"rule": "spec 35.3 rule 1", "group": gid, "account_nonce": account_nonce,
                "carriers": carriers, "known": len(carriers), "live": len(live),
                "live_binding_an_exposed_key": sum(1 for c in live if c["key_exposed"]),
                "ended": bool(carriers) and not live}

    # ------------------------------------------------------- finality and heads
    @staticmethod
    def _stealth_notice(found, head, reported_at, override_as=None):
        """Spec 34.2 rule 2: report the stealth enrollment, offer the override.

        override_deadline is read from `head` each time (l. 1769), never stored; it is None
        while no release schedules T (l. 524, overrideDeadline null). (rule 2's last
        sentences): where the override is the precursor of a tracked authorization whose key is
        exposed, `override_as` says that it is offered as rule 1 states, with the acts that
        follow it or after the wait of rule 1 (g); the report stands meanwhile.
        """
        open_ = state_gate(head) == "OVERRIDE"
        return {"action": REPORT_STEALTH_OFFER_OVERRIDE if open_ else REPORT_STEALTH_WINDOW_CLOSED,
                "commitment": found["commitment"], "reported_at": reported_at,
                "override_open": open_, "override_deadline": head.deadline,
                "migration_nonce": head.migration_nonce,
                "override": ("0x7e through the override gate at migration_nonce m, committing the key "
                             "that 31.2 rule 2 selects (e = m)") if open_ else None,
                "override_as": override_as if open_ else None,
                "fee_path": "SPONSOR_AND_PRIVATE_RELAY (l. 252)",
                "then": "PERMISSION_REVIEW_18_16_ONCE_THE_OVERRIDE_IS_CHAIN_FINALIZED",
                "race": True, "sends_transaction": False}

    def observe_finalized(self, scope, view: FinalizedView):
        """Persist a chain-finalized state; end trackings by 32.2 rule 2; report a stealth enrollment.

        Returns EndedTrackings (a list of (group, variant, reason)). (spec
        34.2 rule 2): where F holds PQ_BY_ENROLL with a commitment that the device did not
        create (not linked to an epoch, and committed by no tracked authorization that
        carries its epoch), as when another key's 0x7d took the account nonce of a tracked
        0x7d, the stealth enrollment is persisted and reported at once in `notices`, and at
        every head that still holds it (observe_head). A PQ_BY_PROOF binding of another
        device of the owner is no stealth enrollment. A recorded transaction whose
        account nonce F has passed ends; seen blocks at or below F stop being starts of 34.2 rule
        1 (a); a LEGACY F with a nonzero account nonce shows a's secp256k1 key published.
        """
        if not isinstance(view, FinalizedView) or not isinstance(view.state, AccountState):
            raise ValueError("authenticated FinalizedView required, not a head")
        f = view.state
        epochs = set(self.epochs.security(scope).compromised_epochs)
        with _locked(self.lock_path):
            d = self._read(); s = self._scope(d, scope)
            previous = s["finalized"].get(f.account.key)
            if previous is not None:
                old = AccountState.from_dict(previous)
                if f.number == old.number and f.to_dict() == old.to_dict():
                    return EndedTrackings()
                if (f.number <= old.number or f.timestamp <= old.timestamp
                        or view.previous_finalized_hash != old.block_hash
                        or f.migration_nonce < old.migration_nonce or f.account_nonce < old.account_nonce
                        or (old.mode != "LEGACY" and f.mode == "LEGACY")
                        or (old.binding_final and not f.binding_final)):
                    raise MetadataError("conflicting finality/state sequence; N1/provider must be checked")
            elif view.previous_finalized_hash is not None:
                raise ValueError("initial finalized checkpoint must be explicit")
            s["finalized"][f.account.key] = f.to_dict()
            ended = []
            for gid, variants in s["groups"].items():
                for vid, r in variants.items():
                    a = Authorization.from_dict(r["authorization"])
                    if a.account != f.account or r["ended"] is not None:
                        continue
                    reason = end_reason(a, f)
                    if reason is not None:
                        r["ended"] = {"reason": reason, "state": f.to_dict()}
                        ended.append((gid, vid, reason))
            # (spec 35.3 rule 1): each carrier of a rotate index (a, n) ended on its own above; the
            # index ends only when every carrier of it that the device knows has ended.
            indexes_ended = []
            for gid in dict.fromkeys(g for g, _, _ in ended):
                variants = s["groups"][gid]
                first = next(iter(variants.values()))["authorization"]
                if first["kind"] == "ROTATE" and all(r["ended"] is not None for r in variants.values()):
                    indexes_ended.append({"group": gid, "account_nonce": first["nonce"],
                                          "carriers": sum(len(r["carriers"]) for r in variants.values())})
            for r in s["transactions"].values():
                tx = Transaction.from_dict(r["transaction"])
                if tx.account == f.account and r["ended"] is None and f.account_nonce > tx.account_nonce:
                    r["ended"] = {"reason": "ACCOUNT_NONCE_CONSUMED", "state": f.to_dict()}
            blocks = s["seen"].get(f.account.key, {})
            for block_hash in [h for h, raw in blocks.items() if raw["number"] <= f.number]:
                del blocks[block_hash]
            if f.mode == "LEGACY" and f.account_nonce > 0:
                s["published"].setdefault(f.account.key, "a chain-finalized LEGACY state with a nonzero nonce (l. 45)")
            notices = []
            if f.mode == "PQ_BY_ENROLL" and not self._own_commitment(s, f.commitment):
                found = {"commitment": f.commitment.hex(), "state": f.to_dict(),
                         "ended_0x7d": [reason for gid, vid, reason in ended
                                        if s["groups"][gid][vid]["authorization"]["kind"] == "ENROLL"]}
                s["stealth"][f.account.key] = found
                notices.append(self._stealth_notice(found, f, "CHAIN_FINALIZED_BLOCK",
                                                    _Model(self, s, epochs, f).override_as()))
            _atomic_json(self.path, d)
            return EndedTrackings(ended, notices, indexes_ended)

    def observe_head(self, scope, head: AccountState, *, inclusions=(), current_epoch=None):
        """Persist head observations and return offers only; never sends or retires.

        inclusions contains (group_id, variant_id, carrier_sha256, outcome,
        migration_nonce_before); outcome is APPLIED or SKIPPED at that entry.
        Caller authenticates the execution result. Batch status alone is not one.
        current_epoch, if supplied, must come from a commitment-matching key scan;
        it is linked to the head's commitment, and, D-1, when that key is
        known exposed its epoch is persisted in the epoch ledger before this call
        returns ("current_epoch_linked"). A record by epoch reaches only the
        commitments that are linked to it: the adapter (wallet.observe_head) derives
        those of every recorded epoch before it calls this method.
        (spec 34.2 rule 1 as redrafted): an offer that needs a precursor names
        its tracked carriers (payload "precursor_carriers", "fresh_precursor") and the act
        that (f) chooses (payload "act"), shows the time left ("time_left", (d)), and, where
        the wait of (g) applies, is WAIT_FRESH_PRECURSOR ("hold"); the stealth-enrollment
        notice says how the override is offered ("override_as"). Every offer is read
        from the search of 34.2 rule 1 (a) ("answer" names the part of rule 1 that decides it);
        the head is kept as a seen block (a start of the condition until F passes it).
        """
        if not isinstance(head, AccountState):
            raise ValueError("head AccountState required")
        epochs = set(self.epochs.security(scope).compromised_epochs)
        if current_epoch is not None:
            _uint(current_epoch, UINT32_MAX, "verified current epoch")
        with _locked(self.lock_path):
            d = self._read(); s = self._scope(d, scope)
            s["heads"][head.account.key] = head.to_dict()
            f = s["finalized"].get(head.account.key)
            if f is None or head.number > f["number"]:
                s["seen"].setdefault(head.account.key, {})[head.block_hash] = head.to_dict()
            if head.mode == "LEGACY" and head.account_nonce > 0:
                s["published"].setdefault(head.account.key, "a LEGACY state with a nonzero nonce (l. 45)")
            notices = []
            for gid, vid, carrier, outcome, before_nonce in inclusions:
                r = s["groups"][gid][vid]; a = Authorization.from_dict(r["authorization"])
                if a.account != head.account or carrier not in r["carriers"] or outcome not in ("APPLIED", "SKIPPED"):
                    raise ValueError("invalid per-authorization inclusion")
                if before_nonce is not None:
                    _uint(before_nonce, UINT64_MAX, "execution prestate nonce")
                event = {"block_hash": head.block_hash, "carrier": carrier, "outcome": outcome, "migration_nonce_before": before_nonce}
                if event not in r["observations"]:
                    r["observations"].append(event)
                # An included carrier is in a block (A holds it).
                r["custody"][carrier] = _merge_custody(r["custody"].get(carrier), "IN_BLOCK")
            before = set(epochs)
            if current_epoch is not None and head.commitment is not None:
                self._link_locked(s, scope, head.commitment, current_epoch, epochs,
                                  "verified current key whose commitment is known exposed")
            current_exposed = head.commitment is not None and (
                self._key_exposed(s, head.commitment, epochs) or current_epoch in epochs)
            if current_exposed and current_epoch is not None and current_epoch not in epochs:
                self.epochs.mark_compromised(scope, current_epoch,
                                             "verified current key whose commitment is known exposed")
                epochs.add(current_epoch)
            linked = current_epoch if current_epoch is not None and current_epoch in epochs - before else None
            model = _Model(self, s, epochs, head)
            activation_revives = []
            if activation_preview(head) is not None and head.commitment not in model.exposed:
                step = Step("ACTIVATION", head.account_nonce, head.commitment, label="PAYLOAD_ACTIVATION", ident="W:0")
                activation_revives = [list(k) for k in model.judge([step]).made]
            pending, exposed = [], []
            for gid, variants in s["groups"].items():
                for vid, r in variants.items():
                    a = Authorization.from_dict(r["authorization"])
                    if a.account != head.account:
                        continue
                    danger = self._exposed(s, a, epochs)
                    # Keep the event history, but offer repair only for the
                    # still-current out-of-range key. This survives a restart.
                    if (a.kind == "ROTATE" and a.epoch is not None and head.commitment == a.commitment
                            and head.migration_nonce <= a.epoch
                            and any(e["outcome"] == "APPLIED" and e["migration_nonce_before"] is not None
                                    and e["migration_nonce_before"] < a.epoch for e in r["observations"])):
                        notices.append({"group": gid, "action": "REPLACE_EXPOSED_KEY_WITH_CONFIRMATION" if danger else "OFFER_RANGE_REPAIR", "epoch": a.epoch})
                    if r["ended"] is not None:
                        continue
                    pending.append((gid, vid))
                    if not danger:
                        continue
                    exposed.append((gid, vid))
                    notices.append(model.plan((gid, vid)))
            stealth = None
            found = s["stealth"].get(head.account.key)
            if (found is not None and head.mode == "PQ_BY_ENROLL"
                    and head.commitment is not None and head.commitment.hex() == found["commitment"]):
                stealth = self._stealth_notice(found, head, "HEAD", model.override_as())
                notices.insert(0, stealth)
            if (current_epoch is not None and head.commitment is not None and not current_exposed
                    and current_epoch >= head.migration_nonce):
                # (31.2 rule 5, l. 8957; spec 38.3 rule 3): a current key that only MATCH_ABOVE_BOUND finds,
                # at epoch e, gets e - migration_nonce + 1 same-key writes of 31.2 rule 8 (a), offered before any new
                # selection; where its epoch is recorded, 31.2 rule 7 (b) applies instead (32.2 rule 4 (c)).
                notices.insert(0, {"action": OFFER_RANGE_REPAIR, "epoch": current_epoch, "found_by": "MATCH_ABOVE_BOUND",
                                   "repair_steps": current_epoch - head.migration_nonce + 1,
                                   "before_any_new_selection": True, "rule": "31.2 rule 5 (l. 8957), rule 8 (a)"})
            if current_exposed:
                notices.insert(0, {"action": "REPLACE_EXPOSED_CURRENT_KEY_WITH_CONFIRMATION", "race": True})
            _atomic_json(self.path, d)
            return {"head": head.to_dict(), "pending": pending, "exposed_pending": exposed,
                    "current_key_exposed": bool(current_exposed), "current_epoch_linked": linked,
                    "activation_revives": activation_revives, "stealth_enrollment": stealth,
                    "offers": notices, "sends_transaction": False}

    def resubmission_allowed(self, scope, candidate: Authorization, head, after=None):
        """Guard automatic retry of one write at the observed head.

        Guard gap (b): the guard evaluates the state after the candidate alone,
        computed here by single_write_preview; a caller's `after`, if given, must
        equal it, so the end state of a write and the act that follows it is never
        accepted as the preview of the write alone (that pair is a OnePayloadBundle,
        item 3.1). The retry is judged by the condition of 34.2 rule 1 (a) and
        refused where (g) holds it. (spec 35.2 rule 1 (d), (e)): a candidate whose
        nonce is above the head's is never retried alone (its predecessors are not in the head's
        state; the payload is re-planned as a whole). This never authorizes signing, fees or submission.
        Full client validation and explicit user authorization for new transactions
        remain necessary.
        """
        _lone_preview(candidate, head, after)
        epochs = set(self.epochs.security(scope).compromised_epochs)
        with _locked(self.lock_path):
            d = self._read(); s = self._scope(d, scope)
            if s["heads"].get(head.account.key) != head.to_dict():
                raise ValueError("stale or unobserved resubmission head")
            r = s["groups"].get(candidate.group_id, {}).get(candidate.variant_id)
            if r is None:
                raise ValueError("unknown candidate authorization")
            persisted = Authorization.from_dict(r["authorization"])
            if (candidate.epoch is not None and persisted.epoch is not None and candidate.epoch != persisted.epoch):
                raise ValueError("conflicting candidate derivation metadata")
            if persisted.epoch is None and candidate.epoch is not None:
                # This call may itself teach the wallet the binding's epoch.
                # Keep that knowledge before deciding, so a later caller cannot
                # omit it again and bypass the already-known epoch exclusion.
                r["authorization"] = candidate.to_dict()
                persisted = candidate
                if any(candidate.commitment.hex() in values for values in s["exposed"].values()):
                    self.epochs.mark_compromised(scope, candidate.epoch, "known exposed binding key")
                    epochs.add(candidate.epoch)
                _atomic_json(self.path, d)
            if r["ended"] is not None or self._exposed(s, persisted, epochs):
                return False
            if _above_the_head(persisted, head):
                return False    # (35.2 rule 1 (d), (e)): an element after the first never leaves alone
            model = _Model(self, s, epochs, head)
            step = model.step_of(persisted, "RETRY", "W:0")
            pre = model.precursor()
            if pre is not None and step.cls == pre["role"] and step.nonce == pre["nonce"] and model.hold() is not None:
                return False
            return not model.judge([step]).made

    # ------------------------------------------------------------------ bundles
    def _bundle_states(self, s, epochs, bundle, roles=None):
        """The structural check: each element applies at the state its predecessors leave, at
        head.timestamp + SLOT (the earliest timestamp of a block after the head).

        (spec 35.2 rule 1): these states are the payload plan's planning states S_0, ..., S_k,
        anchored at the bundle's head B (S_0) and recomputed there whenever the bundle is presented, so that a
        bundle presented at a new head is re-planned as a whole ((d)): every element must take its values from its
        own S_i ((b): a write's PI.migration_nonce, a 0x7d's or 0x7c's account nonce, the activation condition and
        the sender class, already checked by applicability) and a write's key must be the key of S_i or the key
        that it newly selects at e = m_i ((b), (c); _plan_key_check). `roles`, if given, receives the key role of
        each write."""
        head = bundle.head
        t0 = head.timestamp + self.slot
        states, state = [head], replace(head, timestamp=t0)
        for index, element in enumerate(bundle.elements):
            if element.kind == "WRITE":
                a = element.authorization
                if a.account != head.account:
                    raise ValueError("bundle element account mismatch")
                if self._exposed(s, a, epochs):
                    raise ValueError(f"BUNDLE_ELEMENT_KEY_EXPOSED: element {index}")
                if a.kind == "ROTATE" and self._key_exposed(s, a.signer_commitment, epochs):
                    raise ValueError(f"BUNDLE_ELEMENT_SIGNER_EXPOSED: element {index}; a move away from an "
                                     "exposed key leaves alone on the owner's confirmation (export, confirm_move_away)")
                if not binding_conditions_allow(a, state):
                    raise ValueError(f"BUNDLE_ELEMENT_NOT_APPLICABLE: element {index} (judged at head.timestamp + SLOT)")
                role = self._plan_key_check(s, index, a, head, state)
                if roles is not None:
                    roles.append({"index": index, "kind": a.kind, "key": role,
                                  "planning_state_migration_nonce": state.migration_nonce,
                                  "planning_state_account_nonce": state.account_nonce})
                state = single_write_preview(a, state)
            elif element.kind == "ACTIVATION":
                following = activation_preview(state)
                if (following is None or state.commitment != element.commitment
                        or state.account_nonce != element.account_nonce):
                    raise ValueError(f"BUNDLE_ELEMENT_NOT_APPLICABLE: element {index}")
                if self._key_exposed(s, element.commitment, epochs):
                    raise ValueError(f"BUNDLE_ELEMENT_KEY_EXPOSED: element {index}")
                if roles is not None:
                    roles.append({"index": index, "kind": "ACTIVATION", "key": "THE_KEY_OF_ITS_PLANNING_STATE",
                                  "planning_state_account_nonce": state.account_nonce})
                state = following
            else:
                signer = element.commitment if element.commitment is not None else state.commitment
                if not state.activated or state.account_nonce != element.account_nonce or state.commitment != signer:
                    raise ValueError(f"BUNDLE_ELEMENT_NOT_APPLICABLE: element {index}")
                if self._key_exposed(s, state.commitment, epochs):
                    raise ValueError(f"BUNDLE_ELEMENT_KEY_EXPOSED: element {index}")
                if roles is not None:
                    roles.append({"index": index, "kind": "TRANSACTION", "key": "THE_KEY_OF_ITS_PLANNING_STATE",
                                  "planning_state_account_nonce": state.account_nonce})
                state = replace(state, account_nonce=state.account_nonce + 1)
            states.append(replace(state, timestamp=head.timestamp))
        return states

    @staticmethod
    def _preempted_by(trace):
        labels = list(trace)
        for i, label in enumerate(labels):
            if label.startswith("PAYLOAD") and i > 0:
                return labels[i - 1]
        return "A_MEMBER_OF_K_OR_O"

    def _bundle_analysis(self, s, epochs, bundle, balance_covers_acts=False):
        roles = []
        states = self._bundle_states(s, epochs, bundle, roles)
        head = states[0]
        model = _Model(self, s, epochs, head)
        steps = model.element_steps(bundle)
        between = model.between(steps)
        verdict = model.judge(steps, balance_stated=balance_covers_acts, between=between)
        if verdict.made:
            key, trace = next(iter(verdict.made.items()))
            if any(label.startswith("PAYLOAD_ACTS_PREEMPTED") for label in trace):
                raise ValueError(
                    f"BUNDLE_ACT_PREEMPTIBLE: {self._preempted_by(trace)} before the payload takes the account "
                    "nonce or the balance that an act needs while its precursor still applies, and leaves a tracked "
                    "authorization with an exposed key includable that is not without the payload (spec "
                    "34.2 rule 1 (a) (v), (f)): where someone other than the owner can send a transaction of a until "
                    "the precursor lands, the act is a sponsored write past PI.migration_nonce, which depends on "
                    f"neither, and the activation follows once the writes are in a block; run {trace}")
            raise ValueError("BUNDLE_REVIVES_EXPOSED_AUTHORIZATION: in a state that blocks after the head, F or a seen "
                             "block reach with the payload and members of K and O, a tracked authorization with an "
                             "exposed key is includable that is not after the same members without the payload "
                             f"(spec 34.2 rule 1 (a)); run {trace}")
        end = model.run(steps)
        undischarged = [key for key in between if not model.ended(model.targets[key], end)]
        if undischarged:
            raise ValueError("BUNDLE_LEAVES_AUTHORIZATION_UNDISCHARGED: the payload makes "
                             f"{len(undischarged)} tracked exposed authorization(s) includable and its end "
                             "meets no condition of 32.2 rule 2 for them (spec 34.2 rule 1 (b); 32.2 "
                             "rule 3 (a)): a later write can make them includable again")
        precursor = None
        pre = model.precursor()
        if pre is not None and steps[0].cls == pre["role"] and steps[0].nonce == pre["nonce"]:
            first = bundle.elements[0].authorization
            fresh = not any(k == (first.group_id, first.variant_id) for k, _ in pre["carriers"])
            hold = model.hold() if fresh else None
            precursor = {"case": "(a) (i)" if pre["role"] == "WRITE" else "(a) (ii)", "fresh": fresh,
                         "tracked_carriers": [[g, v] for (g, v), _ in pre["carriers"]], "held": hold is not None}
            if hold is not None:
                raise ValueError("BUNDLE_FRESH_PRECURSOR_HELD: no carrier of the payload's first write that A holds can "
                                 "be included after the head, and A's members reach no state in which a tracked PI "
                                 "is includable, so that write would give A the one piece that it lacks; it waits "
                                 "until a chain-finalized block meets a condition of 32.2 rule 2 for the tracked PI "
                                 "(spec 34.2 rule 1 (g))")
            if fresh:
                handed = model.handoff(steps[0])
                precursor["hands_a_rotates"] = [[g, v] for g, v in handed]
                if handed:
                    raise ValueError("BUNDLE_PRECURSOR_HANDS_A_A_ROTATE: the payload's first write is a precursor that A "
                                     f"does not hold, and after it A's members reach {len(handed)} tracked rotate(s) with "
                                     "an exposed key; a builder that splits the payload hands them to A. The act for such "
                                     "a rotate is a write that commits a key other than the one that signs it, then the "
                                     "activation of that key (spec 34.2 rule 1 (f); 31.2 rule 8 (b); V22-W-5 (vii))")
                bound = [step for _, step in pre["carriers"] if step.cls == "WRITE"]
                if pre["role"] == "WRITE" and bound:
                    same = [b.expiry for b in bound if b.version == steps[0].version]
                    precursor["expiry_bound"] = max(same) if same else None
                    if not same or steps[0].expiry > max(same):
                        raise ValueError("BUNDLE_FRESH_PRECURSOR_OUTLIVES: A holds a carrier of a write at this "
                                         "migration_nonce; a fresh one carries a PI of the same verifier_version whose "
                                         "expiry is no later than the latest expiry of those (spec 34.2 rule 1 "
                                         "(b)), so that a builder that splits the payload gains nothing that outlives "
                                         "what it holds; use the tracked carrier or a PI with that bound")
        if verdict.preempted:
            key, trace = next(iter(verdict.preempted.items()))
            raise ValueError(
                f"BUNDLE_ACT_PREEMPTIBLE: {self._preempted_by(trace)} before the payload makes an act fail while its "
                "conditions other than the account nonce and the balance hold, and a tracked authorization that the "
                "payload's precursor makes includable stays includable (spec 34.2 rule 1 (f)); an act paid by a "
                "after a write whose carrier can take up to max_account_fee needs the caller's statement that a's "
                "balance pays it (balance_covers_acts=True), and where another party can send from a, a sponsored act; "
                f"run {trace}")
        if (precursor is not None and pre["role"] == "WRITE" and len(steps) > 1 and steps[1].cls == "ACTIVATION"
                and between):
            # (spec 39.2 rule 1 (a), (b)): the activation after a write precursor is the act only where
            # no member of K or O placed before the payload makes it fail while a PI that the precursor makes includable
            # stays includable after them; a write of another key at the precursor's migration_nonce displaces the
            # precursor and does that.
            failed = model.robust(steps, between, balance_stated=balance_covers_acts)
            if failed:
                key, trace = next(iter(failed.items()))
                raise ValueError(
                    f"BUNDLE_ACT_PREEMPTIBLE: {self._preempted_by(trace)} before the payload makes its activation fail "
                    "while a tracked authorization that the precursor makes includable stays includable after it: "
                    f"{DISPLACED_PRECURSOR}; the act is the sponsored writes past PI.migration_nonce after the precursor; "
                    f"run {trace}")
        return {"bundle": bundle.bundle_id, "one_payload": True, "route": bundle.route,
                "fee_path": bundle.fee_path, "fee_path_from_fee_modes": bundle.fee_path_from_fee_modes,
                "elements": [e.identity for e in bundle.elements],
                "revived_between_elements": [list(key) for key in between], "end_state": states[-1].to_dict(),
                "precursor": precursor,
                "preemptions": model.preemption_report(steps, between, balance_covers_acts),
                "balance_covers_acts": bool(balance_covers_acts),
                "condition": {"rule": "spec 34.2 rule 1 (a)", "starts": len(model.starts),
                              "members_of_k": len(model.k), "search_nodes": verdict.nodes},
                "plan": {**model.plan_of(steps), "element_keys": roles},
                "race": True, "warning": RACE_WARNING, "sends_transaction": False}

    def rotate_acts_needed(self, scope, bundle: OnePayloadBundle, *, balance_covers_acts=False):
        """(spec 34.2 rule 1 (b), (e)): the account nonce through which ordinary
        transactions, signed by the key that the bundle leaves current, must follow the bundle so that the
        payload meets the condition of rule 1 (a) and discharges what its elements make includable; None when
        the bundle already does, or where no extension makes it admissible (bundle_preview then names the
        refusal). Writes nothing."""
        if not isinstance(bundle, OnePayloadBundle):
            raise ValueError("OnePayloadBundle required")
        epochs = set(self.epochs.security(scope).compromised_epochs)
        with _locked(self.lock_path):
            d = self._read(); s = self._scope(d, scope)
            self._require_observed_head(s, bundle.head, "bundle")
            self._bundle_states(s, epochs, bundle)
            model = _Model(self, s, epochs, bundle.head)
            steps = model.element_steps(bundle)
            need = list(model.between(steps)) + list(model.judge(steps).made)
            ok, through, _ = model.acts_through(steps, need, balance_stated=balance_covers_acts)
            # None where no extension helps: bundle_preview then names what refuses the bundle.
            return through if ok else None

    def bundle_preview(self, scope, bundle: OnePayloadBundle, *, balance_covers_acts=False):
        """Validate a one-payload bundle at the observed head; write nothing.

        Each element must apply at the state its predecessors leave, no write may
        commit an exposed key, no activation may reveal one and no transaction may be
        signed by one. The payload must meet the condition of spec 34.2
        rule 1 (a) (BUNDLE_REVIVES_EXPOSED_AUTHORIZATION, or BUNDLE_ACT_PREEMPTIBLE where the
        run that fails it pre-empts an act); each authorization that a proper prefix of it
        makes includable ("revived_between_elements", what a split delivery would expose)
        must meet a condition of 32.2 rule 2 at its end ((b),
        BUNDLE_LEAVES_AUTHORIZATION_UNDISCHARGED); a precursor that A does not hold waits
        ((g), BUNDLE_FRESH_PRECURSOR_HELD), hands A no tracked rotate ((f),
        BUNDLE_PRECURSOR_HANDS_A_A_ROTATE) and does not outlive the carriers that A holds ((b),
        BUNDLE_FRESH_PRECURSOR_OUTLIVES); and no act may be pre-empted while a target of the
        precursor stays includable ((f), BUNDLE_ACT_PREEMPTIBLE). `balance_covers_acts` is the
        caller's statement that a's balance pays every element paid by a after each write of
        the payload has taken all that its carrier allows (34.2 rule 1 (f)).
        """
        if not isinstance(bundle, OnePayloadBundle):
            raise ValueError("OnePayloadBundle required")
        if type(balance_covers_acts) is not bool:
            raise ValueError("balance_covers_acts must be boolean")
        epochs = set(self.epochs.security(scope).compromised_epochs)
        with _locked(self.lock_path):
            d = self._read(); s = self._scope(d, scope)
            self._require_observed_head(s, bundle.head, "bundle")
            return self._bundle_analysis(s, epochs, bundle, balance_covers_acts)

    def export_bundle(self, scope, bundle: OnePayloadBundle, deliver_payload, *,
                      no_one_payload_path=False, confirm_split=None, balance_covers_acts=False):
        """Item 3.1: persist every write of the bundle, then deliver the WHOLE payload once.

        deliver_payload receives the tuple of every element's carrier, in order, in a
        single call, for a private relay or builder bundle interface; this is the only
        automatic approval. (spec 34.2 rule 1 (c)):
        where no path gives one payload, the caller states it (no_one_payload_path=True);
        if a tracked exposed authorization is includable between the elements, the wallet
        raises SplitDeliveryWarning, which states that gap, and only its token, bound to
        the bundle and the head and passed back as confirm_split after the owner's explicit
        confirmation, delivers the elements split: deliver_payload is then called once per
        element, in order, each a one-element tuple, and a list of the results is returned.
        Call again after every change of the head: the bundle is validated afresh. The checks of bundle_preview apply, and nothing is recorded or delivered when one
        refuses. The writes are recorded EXPORTING, and the activations and
        transactions as transactions of a (members of K), then all EXPORTED once delivered.
        """
        if not isinstance(bundle, OnePayloadBundle):
            raise ValueError("OnePayloadBundle required")
        if not callable(deliver_payload):
            raise ValueError("payload delivery callback required")
        if type(no_one_payload_path) is not bool or type(balance_covers_acts) is not bool:
            raise ValueError("no_one_payload_path and balance_covers_acts must be boolean")
        epochs = set(self.epochs.security(scope).compromised_epochs)
        with _locked(self.lock_path):
            d = self._read(); s = self._scope(d, scope)
            self._require_observed_head(s, bundle.head, "bundle")
            analysis = self._bundle_analysis(s, epochs, bundle, balance_covers_acts)
            between = analysis["revived_between_elements"]
            if no_one_payload_path and between:
                token = _digest(["confirm-split-bundle", bundle.head.to_dict(), bundle.bundle_id, between])
                if confirm_split != token:
                    raise SplitDeliveryWarning(between, token, GAP_STATEMENT.format(count=len(between),
                                                                                    what="first element"))
            members, auths, transactions = [], [], []
            state = bundle.head
            for element in bundle.elements:
                if element.kind == "WRITE":
                    self._record_locked(s, scope, element.authorization, element.carrier, "EXPORTING")
                    members.append([element.authorization.group_id, element.authorization.variant_id])
                    auths.append((element.authorization, element.carrier))
                    state = single_write_preview(element.authorization, state)
                else:
                    if element.kind == "ACTIVATION":
                        tx = Transaction(state.account, "ACTIVATION", element.account_nonce, element.commitment)
                        state = activation_preview(state) or state
                    else:
                        signer = element.commitment if element.commitment is not None else state.commitment
                        tx = Transaction(state.account, "ORDINARY", element.account_nonce, signer)
                        state = replace(state, account_nonce=state.account_nonce + 1)
                    self._record_transaction_locked(s, tx, element.carrier, "EXPORTING")
                    transactions.append((tx, element.carrier))
            s["bundles"][bundle.bundle_id] = {
                "members": members, "fee_path": bundle.fee_path, "route": bundle.route,
                "activations": [e.identity[1] for e in bundle.elements if e.kind == "ACTIVATION"],
                "transactions": [e.identity[1] for e in bundle.elements if e.kind == "TRANSACTION"],
                "delivery": "SPLIT" if no_one_payload_path else "ONE_PAYLOAD",
                "last_head": bundle.head.block_hash}
            _atomic_json(self.path, d)
        if not no_one_payload_path:
            result = deliver_payload(tuple(element.carrier for element in bundle.elements))
        else:
            result = [deliver_payload((element.carrier,)) for element in bundle.elements]
        self._delivered(scope, auths, transactions)
        return result
