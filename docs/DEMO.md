# Local migration demonstration

This run uses synthetic balances and public test credentials on chain 13378.
It is not a mainnet snapshot or a production client release. The two geth nodes
are driven by actual Ream validators using the ordinary upstream Lean signature
parameters. Three validators are split between two nodes so that a majority
branch can replace a minority migration block without fabricated votes.

Build the clients as described in [BUILD.md](BUILD.md), then build the proving
and provisioning tools with the same offline dependency cache available:

```sh
python3 tools/build_verified_prover.py --out prover-build --dependencies dependencies \
  --expect-cache-sha256 "$CACHE_SHA256"
python3 tools/build_demo_tools.py --build build --dependencies dependencies \
  --expect-cache-sha256 "$CACHE_SHA256"
python3 demo/assemble.py --client-build build --prover-build prover-build \
  --aggregate-build aggregate-build --n1-dependencies n1-dependencies --out runtime
python3 runtime/start.py --prefix installed --work runs/first
```

The verified prover wrapper copies the authenticated dependency bundle into a
fresh Cargo cache and builds a copy of the committed source. Set `CACHE_SHA256`
from the trusted source channel. Prepare `n1-dependencies` using the offline
wheel collector in [N1-CHECKPOINT.md](N1-CHECKPOINT.md). Toolchains and system
development packages must already be installed. Builds and proving use the
same exclusive heavy-job lock.

`run_demo.py` generates four complete proofs serially, with current expiry and
the full statement bound into each proof. The first recovers a funded, previously unenrolled legacy
account; the other three exercise the sponsor modes as successive writes. It
uses only the explicitly public credential in `share/public-input.json`.
The installed payload contains no proof and does not change during a run.
The final proving stage requires at least 48 GiB available memory. A shared
`pq-heavy-job.lock` in the current user's home prevents concurrent heavy jobs;
all participants on the same machine must use the same lock.

Each new run provisions fresh public XMSS test seeds and fresh histories once.
The restart phase reuses the existing histories, preserving consumed signing
indices. A whole-authority rollback cannot be detected by inspecting a rolled
back local disk alone; this demo does not claim otherwise.

The driver checks pre-T enrollment and activation, the legacy cutoff, recovery,
reorg and reinclusion, all three sponsor modes, activating and ordinary rotate,
the first ML-DSA-44 spend, and restart. `RUN.json`, `network/result.json`, the
raw logs, `SUMMARY.json`, and `report.html` record what actually happened.
A failed or unexecuted stage remains visibly failed or unverified. Signature
history is checked again with the public keys after the nodes stop.

Execution clients have `--maxpeers=0` in this particular partition/reorg test.
Consensus peers transfer the execution material for Engine import. This run
therefore does not establish execution-layer transaction gossip interoperability;
that remains a separately identified component test. The driver never sends
`forkchoiceUpdated`, `newPayload`, or fabricated consensus votes.

The configured 5,666,000 verification gas uses the portable-client measurement
rule in [VERIFICATION-GAS.md](VERIFICATION-GAS.md). This run
does not certify a production worst-case gas calibration, target quantum
security, complete hiding, or an independently reviewed protocol.

Proof output now retains only F, public statement metadata and sanitized metrics.
Inner proofs stay in anonymous memory unless explicitly retained for public test
benchmarks. The demo derives its public signing seed itself. See
[PROVER-CUSTODY.md](PROVER-CUSTODY.md) for input/output and memory boundaries.
