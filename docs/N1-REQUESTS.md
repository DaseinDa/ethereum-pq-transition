# Withdrawal-address request protection

This research client applies the migration rule at the EVM call
site of the EIP-7002 and EIP-7251 request contracts. From T0, a nonempty request
from a LEGACY account reverts. An ENROLLED account is blocked until
`max(enrolled_at, T) + W`, including after activation installs its PQ public-key
marker. A seed recovery changes authority to BY_PROOF and permits the request.
NATIVE accounts and ENROLLED accounts at their deadline are also permitted.
Normal contract code, the system address and empty-input fee reads retain their
ordinary behavior. The upstream request-contract bytecode is unchanged.

The request gate is `core/vm/pq_request_gate.go` with its call-site hooks in
`core/vm/evm.go`, both in `client/geth/0001-pq-migrate.patch`. The
registry lookup uses the existing cold/warm storage-read charging convention
(2,100/100 gas), charged before reading state. All call entry points use their
actual `msg.sender`; failures revert the frame before value or queue changes.

After building and installing the runtime, run:

```sh
python3 PREFIX/tools/run_demo.py --scenario n1-requests --work NEW_RUN_DIRECTORY
```

An optional `--proofs PUBLIC_PROOF_DIRECTORY` reuses an authenticated, unexpired
`recovery/` proof for the installed public test credential. Otherwise the prover
creates a fresh F proof. No statement bytes or clocks are changed to reuse an
expired proof. Each new run generates fresh leanXMSS keys under the shared job
lock. Restarts within that same run retain the signing histories.

The scenario uses two actual Ream/geth nodes and a synthetic genesis. It submits
only to A and checks A's proposer slot, B's identical imported receipts, both
request contracts, an activated ENROLLED attacker, BY_PROOF recovery/activation,
ordinary contract forwarding, fee reads, and restart. The deadline regression
uses an explicitly named synthetic override `W = 612` seconds, with
`T = genesis + 180`. This makes `T + W = genesis + 792` an actual proposer slot
for A. The production profile retains its normal one-year window. Preflight
accepts the short window only when the caller explicitly supplies the matching
`research_window_seconds` value.

After the earlier request checks, the activated ENROLLED account submits both
request types at each of three boundaries: `T + W - 36` (both revert), exactly
`T + W` (both succeed), and `T + W + 36` (both succeed). These are consecutive A
proposer slots; a one-second boundary is covered by component tests, not by an
impossible live slot. The request nonces are 4/5, 6/7 and 8/9. Each pair is queued
before waiting for either receipt. The driver requires both receipts in the same
canonical block, identical on A and B, verifies the actual canonical timestamp,
and checks the combined request hash for both request types. A missed exact
boundary fails the run rather than being accepted as an after-deadline result. `RUN.json`,
`network/result.json`, transaction bytes and signature-audit logs record the
actual outcome. This is a functional run, not a throughput measurement.

Passing this scenario establishes execution-layer request authorization and
transport only. Ream's subsequent validator exit, balance withdrawal and late
leanXMSS registration require the separate stake-state implementation. They are
unfinished work, not accepted limitations or satisfied acceptance gates.

Validation is loop-internal self-review; not independently reviewed.

The historical local run in `N1-VALIDATION.json` predates the deadline extension
and passed all 12 original scenario transactions
(four expected reverts, eight successes), identical A/B import and restart.
The affected component suite passed 353 tests including subtests; its 47 skips
are excluded from that count. This result uses one synthetic network run and
does not establish the later stake transition.

The extended driver has 18 transactions: six expected reverts and twelve
successes. Small schedule/hash tests validate its assertions without running a
network. A new live run, including the exact-deadline pair, remains required;
the earlier 12-transaction record does not establish those additional checks.
