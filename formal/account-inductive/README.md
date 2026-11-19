# AccountInductive: one account's authority record as an inductive invariant (Apalache)

`AccountInductive.tla` models one account of a protected owner: its mode, the class of its commitment and of its
installed key ("O": only the owner holds it; "A": any other key), its migration nonce and the time. It includes the
transitions of the account rules that touch them, under ideal proofs and signatures. `IndInv` is the strengthened
invariant, and `StepProps` are twelve properties of the last transition. Apalache checks them over unbounded integers:
`T0 < T`, `W >= 1`, the time and the migration nonce. The module's header states the abstraction in full.

| File | What it is |
|---|---|
| `AccountInductive.tla` | The module, written in TLA+ (Temporal Logic of Actions). Its SHA-256 with CR (carriage return) stripped is `aa1df41d80bcd9caeffa597d30eb23d99778bf279cd907fc63c421e95ee3e7d1`. |
| `run_apalache.sh` | Runs three kinds of job: INIT (`Init => IndInv`, length 0); STEP (from an arbitrary state of `IndInv`: `IndInv` and `StepProps` after one step); and five scenarios that must be reachable in one step from some state of `IndInv` (their negations must be violated). |
| `mutation_check.py` | Runs six controls. Each weakens one rule of the module, and the inductive step must then be violated. It also writes `summary.json` from `summary.txt`. |
| `record-20261110/` | The run of record (2026-11-10 16:21 UTC; Apalache 0.62.4, OpenJDK 21): `summary.txt`, `summary.json` and one log per job. |

Run on Linux with Apalache 0.62.4 and Java 21, writing outside the source tree. It takes about a minute and 1.5 GB
of heap:

```
bash run_apalache.sh /tmp/account-inductive-out
python3 mutation_check.py /tmp/account-inductive-out
```

`APALACHE` names the `apalache-mc` launcher (default `~/tools/apalache-0.62.4/apalache-0.62.4/bin/apalache-mc`), and
`JVM_ARGS` sets the heap (default `-Xmx1500m`). Expected result: 13 jobs, all as expected (2 checks hold, 5 scenarios
are reached, 6 mutations are violated). Without an argument, both scripts write to `apalache-out/` beside
themselves. `.gitignore` excludes that folder.

`tests/test_formal_record.py` checks four things without Java:
- the module, `run_apalache.sh` and `mutation_check.py` match the SHA-256 (CR stripped) of the research copies;
- the record names that module;
- every mutation applies to exactly one place in the module;
- the record lists the 13 jobs of the two scripts, all as expected. Each has a log that names its initial predicate,
  its invariant and its verdict.

Scope and limits, as the module's header states them:
- one account;
- `T0`, `T` and `W` are fixed in a behaviour;
- keys and commitments keep only their ownership class;
- a seed proof exists only for public inputs that the owner proved, and none expires;
- the model has no fees, gas, batches, lanes or facts, no EIP-7702 (Ethereum Improvement Proposal 7702) designator
  and no native creation.

The research records hold the related models, outside this package:
- the bounded model of the full account rules (`PQMigrate.tla`, checked with TLC, the TLA+ model checker);
- the window models: `WindowRelease.tla` (TLC), and `WindowInductive.tla` (Apalache), which the module's header names
  for releases that change `T0`, `T` or `W`.

The correspondence between these transitions and those of `PQMigrate.tla` is by inspection, not by a refinement proof.

Provenance:
- The module, `run_apalache.sh` and `mutation_check.py` are byte copies of the research files
  (`code/formal-model-20261027/account-inductive/`).
- `record-20261110/` is a byte copy of their run of record (`results/formal-model-20261027/account-inductive/`).
- The `status` text in `summary.json` describes that research run, and `mutation_check.py` writes the same text on any
  rerun. The "external reviewer" it names read the module outside the authoring loop and did not rerun it. As the
  module's header states, that is not an independent review.
