---------------------------- MODULE AccountInductive ----------------------------
(******************************************************************************)
(* The authority record of one account of a protected owner, as an inductive  *)
(* invariant over unbounded integers (Apalache).  Draft of 2026-11-10 for the *)
(* security section of the paper (Theorem 2, Appendix "Security Proofs").     *)
(*                                                                            *)
(* Rules: the transitions of PQMigrate.tla (code/formal-model-20261027) that  *)
(* touch mode, commitment, migration nonce and installed key: DoEcdsa,        *)
(* DoEnroll, MigWrite under MigChecks / GatePasses with PreTLegacy = TRUE,    *)
(* DoPQ (activation, spend, rotate).  Fees, gas, batches, lanes, facts, the   *)
(* EIP-7702 designator (cleared by an enrollment and by a migration; it       *)
(* changes no guard) and native creation (it needs a key whose address is the *)
(* account's: an address preimage) are left out.  T0, T and W are fixed in a  *)
(* behaviour; releases that change them are WindowInductive.tla.              *)
(*                                                                            *)
(* Abstraction (ideal proofs and signatures):                                 *)
(*  - a commitment or an installed key has a class: "O" (a key that only the  *)
(*    owner holds) or "A" (any other key); commitments are binding, so an     *)
(*    activation installs a key of the commitment's class;                    *)
(*  - a seed proof exists only for public inputs that the owner proved, and   *)
(*    these commit to keys of class "O"; a migration applies a public input   *)
(*    whose nonce is the account's (ma records it); the owner may have proved *)
(*    one for every nonce, and none expires, so a migration is possible       *)
(*    whenever its gate is open (more behaviours than the rules allow, which  *)
(*    is the safe direction for every property below);                        *)
(*  - both parties hold the account's secp256k1 key from the start;           *)
(*  - time is an integer and moves forward by any positive amount; the        *)
(*    initial time and nonce are arbitrary integers.                          *)
(*                                                                            *)
(* Apalache proves Init => IndInv (length 0) and, from an arbitrary state of  *)
(* IndInv, IndInv /\ Next => IndInv' /\ the step properties (length 1).       *)
(* Hence IndInv holds in every state and the step properties on every step of *)
(* every behaviour, for all integer values of T0 < T, W >= 1, the time and    *)
(* the nonce.                                                                 *)
(*                                                                            *)
(* Not independently reviewed.                                                *)
(******************************************************************************)
EXTENDS Integers, Apalache

VARIABLES
    \* @type: Int;
    T0,
    \* @type: Int;
    T,
    \* @type: Int;
    W,
    \* @type: Str;
    m,      \* mode: "LEGACY", "ENROLLED", "BYPROOF"
    \* @type: Str;
    c,      \* class of the commitment: "none", "O", "A"
    \* @type: Str;
    k,      \* class of the installed key: "none", "O", "A"
    \* @type: Int;
    n,      \* migration nonce
    \* @type: Int;
    ma,     \* the nonce of the public input applied last (below n; n - 1 at the start)
    \* @type: Int;
    enr,    \* time of the enrollment (meaningful in mode ENROLLED)
    \* @type: Int;
    t,      \* time of the current block
    \* the state before the last transition, the transition and its authority
    \* @type: Str;
    pm,
    \* @type: Str;
    pc,
    \* @type: Str;
    pk,
    \* @type: Int;
    pn,
    \* @type: Int;
    pma,
    \* @type: Int;
    pt,
    \* @type: Str;
    act,    \* "init", "ecdsa", "enroll", "migrate", "activate", "use", "rotate", "tick"
    \* @type: Str;
    by      \* "O": the owner's seed or key; "A": a key the adversary holds; "E": the secp256k1 key (both); "-": none

Modes == {"LEGACY", "ENROLLED", "BYPROOF"}
Cls == {"none", "O", "A"}

\* @type: (Str, Str, Int) => Bool;
Final(mm, kk, tt) == (mm = "BYPROOF" /\ kk # "none") \/ (mm = "ENROLLED" /\ tt >= T + W)
\* the three gates of a migration (GatePasses with PreTLegacy = TRUE)
\* @type: (Str, Str, Int) => Bool;
Gate(mm, kk, tt) == mm = "LEGACY" \/ (mm = "ENROLLED" /\ tt < T + W) \/ (mm = "BYPROOF" /\ kk = "none")
\* EcdsaDead
\* @type: (Str, Int) => Bool;
Dead(mm, tt) == tt >= T \/ mm # "LEGACY"

Hist(a, who) == pm' = m /\ pc' = c /\ pk' = k /\ pn' = n /\ pma' = ma /\ pt' = t /\ act' = a /\ by' = who
Params == UNCHANGED <<T0, T, W>>

\* a legacy transaction, an EIP-7702 authorization or an ecrecover consent (R1-R3)
Ecdsa ==
    /\ m = "LEGACY" /\ t < T
    /\ UNCHANGED <<m, c, k, n, ma, enr, t>>
    /\ Hist("ecdsa", "E") /\ Params

\* 0x7d: the owner enrolls a key of its own, or the adversary one of its own
Enroll ==
    /\ m = "LEGACY" /\ T0 <= t /\ t < T
    /\ \E cls \in {"O", "A"} : c' = cls
    /\ m' = "ENROLLED" /\ k' = "none" /\ n' = n + 1 /\ enr' = t
    /\ UNCHANGED <<ma, t>>
    /\ Hist("enroll", "E") /\ Params

\* 0x7e or a 0x7f entry: only with a public input that the owner proved, whose nonce is n
Migrate ==
    /\ t >= T0 /\ Gate(m, k, t)
    /\ m' = "BYPROOF" /\ c' = "O" /\ k' = "none" /\ n' = n + 1
    /\ ma' = n
    /\ UNCHANGED <<enr, t>>
    /\ Hist("migrate", "O") /\ Params

\* first 0x7c: installs the key that the commitment fixes
Activate ==
    /\ m # "LEGACY" /\ k = "none"
    /\ k' = c
    /\ UNCHANGED <<m, c, n, ma, enr, t>>
    /\ Hist("activate", c) /\ Params

\* a 0x7c of an activated account, or a signature that R5 verifies
Use ==
    /\ k # "none"
    /\ UNCHANGED <<m, c, k, n, ma, enr, t>>
    /\ Hist("use", k) /\ Params

\* rotate: a final, activated account; the owner rotates to a key of its own,
\* the adversary to any key
Rotate ==
    /\ k # "none" /\ Final(m, k, t)
    /\ \E cls \in {"O", "A"} : (k = "O" => cls = "O") /\ c' = cls /\ k' = cls
    /\ n' = n + 1
    /\ UNCHANGED <<m, ma, enr, t>>
    /\ Hist("rotate", k) /\ Params

Tick ==
    /\ \E d \in Int : d > 0 /\ t' = t + d
    /\ UNCHANGED <<m, c, k, n, ma, enr>>
    /\ Hist("tick", "-") /\ Params

Next == Ecdsa \/ Enroll \/ Migrate \/ Activate \/ Use \/ Rotate \/ Tick

Init ==
    /\ T0 = Gen(1) /\ T = Gen(1) /\ W = Gen(1)
    /\ T0 < T /\ W >= 1
    /\ m = "LEGACY" /\ c = "none" /\ k = "none"
    /\ n = Gen(1) /\ ma = n - 1 /\ enr = Gen(1) /\ t = Gen(1)
    /\ pm = m /\ pc = c /\ pk = k /\ pn = n /\ pma = ma /\ pt = t /\ act = "init" /\ by = "-"

(******************************************************************************)
(* The inductive invariant                                                    *)
(******************************************************************************)
IndInv ==
    /\ T0 < T /\ W >= 1
    /\ m \in Modes /\ c \in Cls /\ k \in Cls
    /\ (m = "LEGACY" => c = "none" /\ k = "none")
    /\ (m # "LEGACY" => c # "none")
    \* I2: an installed key is the key of the commitment
    /\ (k # "none" => k = c)
    \* I1: a proof-bound account commits to a key of the owner
    /\ (m = "BYPROOF" => c = "O")
    \* every enrollment precedes T
    /\ (m = "ENROLLED" => T0 <= enr /\ enr < T /\ enr <= t)
    \* every public input applied so far has a nonce below the account's
    /\ ma < n

(******************************************************************************)
(* Step properties (over the last transition)                                 *)
(******************************************************************************)
\* P1: no return to LEGACY; time moves forward; the death of secp256k1 authority is permanent
NoReturn == (pm # "LEGACY" => m # "LEGACY") /\ t >= pt /\ (Dead(pm, pt) => Dead(m, t))
\* (a): secp256k1 authority takes effect only while it is alive
EcdsaOnlyAlive == by = "E" => ~Dead(pm, pt)
\* P2: the nonce grows by one with every change of authority and not otherwise
NonceStep ==
    /\ (act \in {"enroll", "migrate", "rotate"} => n = pn + 1)
    /\ (act \notin {"enroll", "migrate", "rotate"} => n = pn)
\* (b): a migration applies a public input whose nonce is above every nonce applied before: at most once
AppliedOnce == act = "migrate" => (ma = pn /\ pn > pma)
\* P3: inside its window an enrolled key can neither close nor move the gate
WindowKept ==
    (pm = "ENROLLED" /\ pt < T + W) =>
        /\ act \in {"init", "migrate", "activate", "use", "tick"}
        /\ (act \in {"activate", "use"} => m = pm /\ c = pc /\ n = pn)
\* P4: from T on, only a seed proof changes the record of a frozen account
FrozenOnlyProof == (pm = "LEGACY" /\ pt >= T) => act \in {"init", "migrate", "tick"}
\* (b): a proof-bound account stays the owner's; the adversary authorizes nothing on it
OwnerKept == pm = "BYPROOF" => (m = "BYPROOF" /\ c = "O" /\ by \in {"O", "-"})
\* (c): a migration leaves the owner's commitment and no installed key
MigrationEffect == act = "migrate" => (m = "BYPROOF" /\ c = "O" /\ k = "none")
\* (c): the adversary's key acts on the account only under its own enrollment
AdvOnlyOwnEnrollment == by = "A" => (pm = "ENROLLED" /\ pc = "A")
\* (c): the gates are open: an enrollment until T + W, a LEGACY account from T0 without a deadline
GateOpen ==
    /\ (m = "ENROLLED" /\ t < T + W => t >= T0 /\ Gate(m, k, t))
    /\ (m = "LEGACY" /\ t >= T0 => Gate(m, k, t))
\* (c): the window is longer than W
WindowAtLeastW == m = "ENROLLED" => (T + W) - enr > W
\* (d): an enrollment happens in LEGACY only, hence once (with NoReturn)
EnrollOnce == act = "enroll" => (pm = "LEGACY" /\ pt < T /\ m = "ENROLLED")

StepProps ==
    /\ NoReturn /\ EcdsaOnlyAlive /\ NonceStep /\ AppliedOnce /\ WindowKept /\ FrozenOnlyProof
    /\ OwnerKept /\ MigrationEffect /\ AdvOnlyOwnEnrollment /\ GateOpen
    /\ WindowAtLeastW /\ EnrollOnce

IndInvAndProps == IndInv /\ StepProps

\* an arbitrary state of IndInv as the start of the inductive step; its
\* previous-step record is the state itself
IndInit ==
    /\ T0 = Gen(1) /\ T = Gen(1) /\ W = Gen(1)
    /\ m \in Modes /\ c \in Cls /\ k \in Cls
    /\ n = Gen(1) /\ ma = Gen(1) /\ enr = Gen(1) /\ t = Gen(1)
    /\ pm = m /\ pc = c /\ pk = k /\ pn = n /\ pma = ma /\ pt = t /\ act = "init" /\ by = "-"
    /\ IndInv

(******************************************************************************)
(* Scenarios: each is expected to be VIOLATED after one step from IndInit, so *)
(* the inductive step is not vacuous for the scenario it names                *)
(******************************************************************************)
\* an override of an enrollment is possible
NoOverride == ~(act = "migrate" /\ pm = "ENROLLED")
\* a stealth enrollment is possible
NoAdvEnroll == ~(act = "enroll" /\ c = "A")
\* the adversary's enrolled key rotates once its window has closed
NoAdvRotate == ~(act = "rotate" /\ by = "A")
\* a frozen account is recovered
NoFrozenRecovery == ~(act = "migrate" /\ pm = "LEGACY" /\ pt >= T)
\* a seed-proof migration before T
NoPreTMigration == ~(act = "migrate" /\ pm = "LEGACY" /\ pt < T)
==============================================================================
