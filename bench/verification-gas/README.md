# Portable F verification gas calibration

Author assignment 1, 2026-11-02. Protocol rules/parameters and verifier identity
are unchanged. Classical precompiles are pricing anchors, not security components
of the migration proof. Requirements: D16-COST, S12-8.

## Predeclared measurement rule

- The same portable geth test binary calls native F and the Osaka precompile
  table. F uses the authenticated x86-64 native library, not a target-cpu=native
  build. GOAMD64=v1, GOMAXPROCS=1, RAYON_NUM_THREADS=1; one CPU affinity.
- Ten fresh processes; one untimed warm-up per operation, then ten timed
  batches per process. Each batch averages ten invocations. Every invocation
  checks its expected result. Report each process's average as one sample.
- F cold key initialization is separately recorded once per process. It is a
  startup/configuration cost, not included in the warm verification charge.
- Three pinned geth vectors: ecRecover/ValidKey, bn256Pairing/jeff1 (two pairs),
  blsPairing/bls_pairing_e(2*G1,3*G2)=e(6*G1,G2) (two pairs). Nonempty valid
  inputs, no infinity-only fast path. RequiredGas is read from the same binary.
- Public deterministic interleaving of the four operations reduces order drift.
  Compare direct verifier/precompile work, excluding EVM call memory expansion,
  transaction intrinsic gas and pool caches; those are charged in execution.
- For each anchor j, r_j = gas_j / median(processMeanNs_j).
  r = median(r_ecrecover, r_BN254, r_BLS12_381).
  F_verify_gas = ceil(r * median(processMeanNs_F)), rounded upward to the next
  1,000 gas. This rounding rule is chosen before seeing measurements.
- Re-execute ten recovery transactions on ten fresh state instances at that
  verifyGas and current block time, with actual proofs/carriers and normal gas
  caps. Report execution gas (including intrinsic gas) and verifier charge apart.

The resulting value is an empirical research-profile calibration, not a
worst-case execution bound or production security acceptance. Tail/invalid-input
measurements and additional hardware are separate obligations if required by the
production release; they are not converted into accepted gaps by this experiment.

loop-internal self-review; not independently reviewed.

## Actual result and reproduction

The ten-process sample selects 5,666,000 gas. Ten fresh-state recoveries use
8,717,476--8,770,396 gas (mean 8,738,836.8); all are successful under the normal
16,777,216 transaction cap. The targeted client regression has 43 passing cases
and 17 fixture/build-conditional skips, counting subtests. No skipped case is
counted as an actual F/recovery pass. Raw outputs are in `samples/`, `PRICE.json`, and `RESULT.json`.

Use Linux, Python 3, Go 1.25.14 and the already authenticated portable native
library. Supply local source archives, Go module cache and ten public, unexpired
mode-0 fixture directories produced by `bench/run.py`; no network is needed.
The fixture preparation copies only F, PI and carriers, never inner proofs.

```sh
python3 run.py --phase prepare --lab "$LAB" --archive-cache "$ARCHIVES" --clients "$CLIENTS" --go-mod "$GO_MODULES" --fixtures "$PUBLIC_FIXTURES" --out "$WORK"
python3 run.py --phase measure --lab "$LAB" --archive-cache "$ARCHIVES" --clients "$CLIENTS" --go-mod "$GO_MODULES" --fixtures "$PUBLIC_FIXTURES" --out "$WORK"
python3 run.py --phase recovery --lab "$LAB" --archive-cache "$ARCHIVES" --clients "$CLIENTS" --go-mod "$GO_MODULES" --fixtures "$PUBLIC_FIXTURES" --out "$WORK"
```

The package pins the calibrated price. Re-running timing does not automatically
change it. Recovery reads the package price and tests it with the matching binary
and genesis. Another price requires an explicit source/configuration update;
a mismatch fails configuration validation.
