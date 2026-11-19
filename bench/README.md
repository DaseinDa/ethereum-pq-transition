# Repeating the measurements

These scripts use the same full relationship, PI198, pinned keys, native geth
verifier and resource caps as the demo. Run heavy jobs serially. Keep the shared
lock in the same location for all processes on the machine.

```sh
python3 bench/run.py prepare --work runs/bench --prover-build prover-build
python3 bench/run.py prove --work runs/bench --prover-build prover-build
python3 bench/run.py geth --work runs/bench --prover-build prover-build \
  --client-build build --dependencies dependencies
python3 bench/summarize.py --work runs/bench
```

The primary cohort contains ten independently randomized proofs of one fixed
public statement. Prover preparation, proving, fresh verification and serialization
are included in command wall time; the internal proving timer is also reported.
GNU time records peak RSS separately for each layer. Compilation is excluded.
Record the host's physical CPU and RAM separately when running under a VM;
`hardware.json` describes the environment visible to Linux.

Client verification uses ten fresh processes, each with ten direct verifier
calls, and reports the ten within-process means as the primary sample. Pool
result caches are not used. Each process checks altered PI and proof rejection.
Transaction execution repeats each case ten times against fresh state. Sponsor
cases use one carrier per mode; a zero gas standard deviation reflects deterministic
execution, not ten independently generated sponsor proofs. This is a component
benchmark, not a ten-run consensus network experiment.

`SUMMARY.json`, CSV files and `SHA256.json` are computed from successful raw
outputs. Capacity uses the measured maximum gas, the configured block budget,
the 16,777,216 transaction cap and the wallet's 16,000,000 declared gas limit.
Geth reserves the declared limit before executing each transaction, so the
current packing estimate is `1 + floor((blockGasLimit - declaredLimit) / gas)`.
The tighter-limit arithmetic bound is reported separately. Neither calculation
includes other traffic, missed slots, bandwidth, consensus cost or proving supply;
adding nodes does not multiply a single chain's capacity.

loop-internal self-review; not independently reviewed.

The ported carrier generator was checked byte-for-byte against the original
measurement cohort (19 carriers). Replaying that cohort through the ported
summarizer also passed. These compatibility checks reuse prior observations;
they are not additional independent performance samples.

The capacity table separates recoveries alone from recovery plus ordinary
activation and first spend. The latter sums measured gas maxima and models a
steady pipeline across accounts; it does not assume that a wallet can admit
activation before its recovery is included, or prove an observed network rate.

Inner proofs are not retained by default. Add `--keep-inner` explicitly to the
`prove` command to retain them for these public test inputs. The summarizer reads
per-layer metrics and fresh-verification verdicts from `PROOF.json`; it also
accepts the original report layout of already frozen cohorts.
