"""Finite account-state reachability model used by authorization tracking.
Component model only: it does not parse transactions or verify cryptography.
"""
from __future__ import annotations

from collections import deque, namedtuple
from dataclasses import dataclass, field
import hashlib

SLOT_DEFAULT = 12   # seconds; the SLOT of the chain's consensus configuration (12 s on mainnet, l. 1230)
# Symbolic commitments (no key is derived for them).
A_KEY = hashlib.sha256(b"model: a key that A holds and the owner does not (its own 0x7d or rotate target)").digest()
IND_KEY = hashlib.sha256(b"model: C_ind, a key not derived from the seed (31.2 rule 8 (b))").digest()
FRESH_KEY = hashlib.sha256(b"model: the key that 31.2 rule 2 selects for a write, not yet linked").digest()

St = namedtuple("St", "mode mn an activated commitment enrolled_at code_kind", defaults=(None,))
PQ_MODES = ("PQ_BY_ENROLL", "PQ_BY_PROOF")


@dataclass(frozen=True)
class Config:
    fork_time: int | None
    override_window: int
    protocol_time: int | None = None
    legacy_seed_proof_from_t0: bool = False


@dataclass(frozen=True)
class Step:
    """One transaction of `a` as an effect on the modelled state (see the module docstring)."""
    cls: str
    nonce: int
    commitment: bytes | None = None
    signer: bytes | None = None
    activating: bool = False
    expiry: int | None = None
    a_paid: bool = True
    takes_balance: bool = False
    by_a: bool = False
    version: int | None = None
    label: str = ""
    ident: str = ""         # a member's identity in the comparison without the payload (see search)


def state_of(account_state):
    """The modelled state of an AccountState (fork_time and override_window go to Config)."""
    return St(account_state.mode, account_state.migration_nonce, account_state.account_nonce,
              account_state.activated, account_state.commitment, account_state.enrolled_at,
              account_state.effective_code_kind)


def deadline(st, cfg):
    return None if cfg.fork_time is None else max(st.enrolled_at, cfg.fork_time) + cfg.override_window


def gate(st, t, cfg):
    """The gate of check 5 open at (st, t) (l. 1159-1161), or None; T unscheduled: no finite deadline (l. 61)."""
    if ((cfg.legacy_seed_proof_from_t0 and cfg.protocol_time is None)
            or (cfg.protocol_time is not None and t < cfg.protocol_time)):
        return None
    if st.mode == "PQ_BY_PROOF" and not st.activated:
        return "RECOMMIT"
    if st.mode == "PQ_BY_ENROLL":
        d = deadline(st, cfg)
        return "OVERRIDE" if d is None or t < d else None
    if st.mode == "LEGACY" and st.code_kind in (None, "EMPTY", "DELEGATION"):
        if cfg.fork_time is not None and t >= cfg.fork_time:
            return "FROZEN"
        if cfg.legacy_seed_proof_from_t0:
            return "PRE_T_LEGACY"
    return None


def final(st, t, cfg):
    """final(a) (l. 113): binding-final."""
    if st.mode == "PQ_NATIVE":
        return True
    if st.mode == "PQ_BY_PROOF":
        return st.activated
    if st.mode == "PQ_BY_ENROLL":
        d = deadline(st, cfg)
        return d is not None and t >= d
    return False


def ecdsa_alive(st, t, cfg):
    """A secp256k1 signature of `a` can be valid: LEGACY and before T (l. 360-361; R1 pre-T reads mode)."""
    return st.mode == "LEGACY" and (cfg.fork_time is None or t < cfg.fork_time)


def conditions(step, st, t, cfg):
    """(write_level, nonce_ok): the step's validity apart from a's account nonce and balance, and that nonce."""
    c = step.cls
    if c == "WRITE":
        return (st.mn == step.nonce and t <= step.expiry and gate(st, t, cfg) is not None), True
    nonce_ok = st.an == step.nonce
    if c == "ENROLL":
        installed = ((cfg.protocol_time is None and not cfg.legacy_seed_proof_from_t0)
                     or (cfg.protocol_time is not None and t >= cfg.protocol_time))
        return installed and ecdsa_alive(st, t, cfg), nonce_ok
    if c == "ECDSA":
        return ecdsa_alive(st, t, cfg), nonce_ok
    if c == "ACTIVATION":
        return (st.mode in PQ_MODES and not st.activated and st.commitment == step.commitment), nonce_ok
    if c == "ORDINARY":
        return (st.activated and st.commitment == step.commitment), nonce_ok
    if c == "ROTATE":
        if step.activating:
            return (st.mode in PQ_MODES and not st.activated and st.commitment == step.signer), nonce_ok
        return (st.activated and st.commitment == step.signer), nonce_ok
    raise ValueError(f"unknown effect class {c}")


def valid(step, st, t, cfg):
    w, n = conditions(step, st, t, cfg)
    return w and n


def apply(step, st, t, cfg):
    """The state after `step`, which must be valid at (st, t)."""
    c = step.cls
    if c == "WRITE":
        return st._replace(mode="PQ_BY_PROOF", mn=st.mn + 1, commitment=step.commitment,
                           activated=False, code_kind="EMPTY")
    if c == "ENROLL":
        return st._replace(mode="PQ_BY_ENROLL", mn=st.mn + 1, an=st.an + 1, commitment=step.commitment,
                           activated=False, enrolled_at=t, code_kind="EMPTY")
    if c == "ECDSA":
        return st._replace(an=st.an + 1)
    if c in ("ACTIVATION", "ORDINARY"):
        return st._replace(an=st.an + 1, activated=True, code_kind="PQ_MARKER")
    if c == "ROTATE":
        mid = st._replace(an=st.an + 1, activated=True, code_kind="PQ_MARKER")
        if final(mid, t, cfg):
            return mid._replace(mn=mid.mn + 1, commitment=step.commitment)
        return mid                      # NOT_FINAL: the frame reverts, the nonce and activation stay (l. 328)
    raise ValueError(f"unknown effect class {c}")


def planning_states(start, steps, t, cfg):
    """Spec 35.2 rule 1 (b): [S_0, ..., S_k] for the payload `steps` in its order, S_0 = `start` and S_i
    the state after steps[0..i-1], each taken as valid (its transition applied whether or not its conditions
    hold there; a caller checks those separately). A rotate's frame binds only where final(a) holds after its
    activation (l. 328), as apply() states."""
    out = [start]
    for step in steps:
        out.append(apply(step, out[-1], t, cfg))
    return out


def binds(step, st, t, cfg):
    """A tracked binding authorization is includable with its binding effect at (st, t)."""
    if not valid(step, st, t, cfg):
        return False
    if step.cls == "ROTATE":
        return final(st._replace(an=st.an + 1, activated=True), t, cfg)
    return step.cls in ("WRITE", "ENROLL")


@dataclass
class Problem:
    """One instance of the condition: the model at one observed head."""
    cfg: Config
    times: tuple            # header timestamps visited: head.timestamp + SLOT, then each threshold above it
    starts: tuple           # St of the head, of F and of every seen block that may descend from F
    members: tuple          # Steps of K, and of carriers formed from K's or the payload's 0x7e
    a_signs: dict           # commitment -> label: keys of `a` that A holds
    a_ecdsa: bool           # A holds a's secp256k1 key (published, l. 45) in the run with the payload
    rotate_targets: tuple   # keys that A rotates to (its own, and held keys that sign tracked members)
    targets: dict           # id -> Step: tracked carriers that bind an exposed key (35.3 rule 1)
    max_an: int             # the bound on O's account-nonce templates
    a_ecdsa_without: bool | None = None   # ... in the run without it (None: as with it)


def a_moves(p, st, t, *, without=False):
    """Members of O that A signs at (st, t): their effect classes, instantiated at a's nonce. `without`:
    A's knowledge in the run without the payload (a payload whose ECDSA or 0x7d element reaches A reveals
    a's secp256k1 public key, l. 45, which A lacks without it)."""
    ecdsa = p.a_ecdsa if not without or p.a_ecdsa_without is None else p.a_ecdsa_without
    out = []
    if st.an > p.max_an:
        return out
    c = st.commitment
    if st.mode in PQ_MODES and c in p.a_signs:
        label = p.a_signs[c]
        out.append(Step("ORDINARY" if st.activated else "ACTIVATION", st.an, c, by_a=True, label=label,
                        ident="A:0x7c:" + c.hex()))
        for target in p.rotate_targets:
            if target != c:
                out.append(Step("ROTATE", st.an, target, signer=c, activating=not st.activated, by_a=True,
                                label=label.replace("0x7C", "ROTATE"), ident=f"A:rotate:{c.hex()}:{target.hex()}"))
    if ecdsa and ecdsa_alive(st, t, p.cfg):
        out.append(Step("ECDSA", st.an, by_a=True, label="ECDSA_TRANSACTION_AT_THE_ACCOUNT_NONCE", ident="A:ecdsa"))
        out.append(Step("ENROLL", st.an, A_KEY, by_a=True, label="0x7D_OF_A_AT_THE_ACCOUNT_NONCE", ident="A:0x7d"))
    return out


def same_member(p, m, st, t):
    """`m` in the run without the payload: a member of K or a carrier keeps its bytes; a member that A
    signs keeps its signer and effect class, and A signs it at the account nonce that the position has
    (A creates it at will, so its nonce is not part of what the comparison holds equal). None if it does
    not apply there."""
    if not m.by_a:
        return m if valid(m, st, t, p.cfg) else None
    for x in a_moves(p, st, t, without=True):
        if x.ident == m.ident and valid(x, st, t, p.cfg):
            return x
    return None


def payload_outcomes(p, payload, st, t, drained, taken, balance_stated):
    """Every end state of the payload included whole at (st, t), and the acts that a pre-emption failed.

    Returns [(end_state, pre-empted indices, by_taking)]: an element at index i >= 1 is pre-empted when
    its conditions other than the account nonce and the balance hold but the nonce or the balance
    fails. `by_taking` marks an outcome in which an element failed only because a carrier formed
    from a 0x7e took balance (no member that A signs drained it): rule 1 (a) (v) keeps such a carrier
    in the comparison without the payload and leaves that act to (f)'s condition on a's balance, so
    the search judges (a) without these outcomes and (f) with them.
    """
    out = []

    def rec(i, cur, pre, by_taking):
        if i == len(payload):
            out.append((cur, tuple(pre), by_taking))
            return
        e = payload[i]
        w, n = conditions(e, cur, t, p.cfg)
        if not (w and n):
            rec(i + 1, cur, pre + [i] if (w and not n and i) else pre, by_taking)
            return
        if e.a_paid and (drained or (taken and not balance_stated)):
            rec(i + 1, cur, pre + [i] if i else pre, by_taking or not drained)   # popped: too little balance
        rec(i + 1, apply(e, cur, t, p.cfg), pre, by_taking)

    rec(0, st, [], False)
    return out


@dataclass
class Verdict:
    made: dict              # target id -> witness: made includable by the payload (fails 34.2 rule 1 (a))
    reach: dict             # target id -> witness: includable in a state that the members reach (no payload)
    preempted: dict         # target id -> witness: an act pre-empted and a precursor target left includable
    nodes: int
    failed: dict = field(default_factory=dict)   # target id -> witness: includable after the payload


def search(p, payload=None, *, balance_stated=False, between=(), need=()):
    """Decide the condition of 34.2 rule 1 (a) for `payload`, or (payload None) the reach of the members.

    `between`: ids of targets that a proper prefix of the payload makes includable (the precursor's
    targets); a run in which an act is pre-empted and one of them is includable after the payload is
    reported in `preempted` (rule 1 (f)).

    (34.2 rule 1 (e), (f) with V25-W-1 (ii)): `need`, the ids of the targets that the
    payload answers, are reported in `failed` wherever one of them is includable in a state that a run reaches after
    the payload, the runs in which members of K or O placed before the payload made an act of it fail included. An
    act whose payload has a `failed` target is one that a member of K or O placed before it can make fail. The
    outcomes in which an element failed only because a carrier took balance stay out, as for `made`: the offers
    judge acts with the balance stated, and the bundle path refuses those failures by (f) (`preempted`).
    """
    made, reach, preempted, failed = {}, {}, {}, {}
    parent, queue = {}, deque()

    def push(node, prev, label):
        if node not in parent:
            parent[node] = (prev, label)
            queue.append(node)

    def trace(node):
        labels = []
        while node is not None:
            node, label = parent[node]
            labels.append(label)
        return list(reversed(labels))

    for index, start in enumerate(p.starts):
        push(("B", start, start, 0, False, False), None, f"START_{index}")
    while queue:
        node = queue.popleft()
        phase, w, wo, ti, drained, taken = node
        t = p.times[ti]
        if phase == "B" and payload is None:
            for tid, x in p.targets.items():
                if tid not in reach and binds(x, w, t, p.cfg):
                    reach[tid] = trace(node) + [f"INCLUDABLE_AT_{t}"]
        if phase == "A":
            for tid, x in p.targets.items():
                if tid not in made and binds(x, w, t, p.cfg) and not binds(x, wo, t, p.cfg):
                    made[tid] = trace(node) + [f"INCLUDABLE_AT_{t}"]
        if phase == "A":
            for tid in need:
                if tid not in failed and binds(p.targets[tid], w, t, p.cfg):
                    failed[tid] = trace(node) + [f"INCLUDABLE_AFTER_THE_PAYLOAD_AT_{t}"]
        for m in tuple(p.members) + tuple(a_moves(p, w, t)):
            if not valid(m, w, t, p.cfg):
                continue
            w2 = apply(m, w, t, p.cfg)
            twin = same_member(p, m, wo, t) if payload is not None else m
            wo2 = apply(twin, wo, t, p.cfg) if twin is not None else wo          # popped without the payload
            if phase == "B":
                push(("B", w2, wo2, ti, drained or m.by_a, taken or m.takes_balance), node, m.label)
            else:
                push(("A", w2, wo2, ti, False, False), node, m.label)
        if phase == "B" and payload is not None:
            for end, pre, by_taking in payload_outcomes(p, payload, w, t, drained, taken, balance_stated):
                label = "PAYLOAD" + (f"_ACTS_PREEMPTED_{list(pre)}" if pre else "")
                if by_taking:
                    label += "_BY_A_CARRIER_THAT_TOOK_BALANCE"
                else:
                    push(("A", end, wo, ti, False, False), node, label)
                if pre:
                    for tid in between:
                        if tid not in preempted and any(binds(p.targets[tid], end, p.times[j], p.cfg)
                                                        for j in range(ti, len(p.times))):
                            preempted[tid] = trace(node) + [label, "INCLUDABLE_AFTER_THE_PAYLOAD"]
        if ti + 1 < len(p.times):
            push((phase, w, wo, ti + 1, drained, taken), node, f"TIME_{p.times[ti + 1]}")
    return Verdict(made, reach, preempted, len(parent), failed)


def critical_times(t0, cfg, starts, steps=()):
    """head.timestamp + SLOT, and every threshold above it at which a validity condition becomes true.

    The conditions that time makes true are the frozen gate (t >= T) and final(a) of an enrollment
    (t >= deadline(a), which also lets an activating rotate's frame bind); those it makes false are a
    PI's expiry, a secp256k1 signature (t >= T) and the override gate (t >= deadline(a)). A run takes
    each member at the earliest time it allows, since a later time only ends validity, so the left
    ends of the validity intervals suffice: t0, T and each deadline(a) (T + W for an enrollment made
    before T; enrolled_at + W otherwise). An expiry is no such left end. `steps` is accepted for the
    callers and not read.
    """
    times = {t0}
    if cfg.protocol_time is not None:
        times.add(cfg.protocol_time)
    if cfg.fork_time is not None:
        times.add(cfg.fork_time)
        times.add(cfg.fork_time + cfg.override_window)          # deadline(a) of an enrollment before T
    for st in starts:
        if st.mode == "PQ_BY_ENROLL":
            d = deadline(st, cfg)
            if d is not None:
                times.add(d)
    return tuple(sorted(t for t in times if t >= t0))
