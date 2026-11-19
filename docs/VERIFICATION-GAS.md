# Portable F verification gas

The F research profile now charges **5,666,000 gas** for verification. The proof relation, PI198, trusted keys and proof size bound are unchanged. Earlier Succinct profiles retain their historical charge. Existing demo chains must keep their original binary/configuration; initialize a fresh chain for this profile update.

Method: ten fresh geth processes pinned to one CPU, one warm-up and 100 timed calls per operation per process. GOAMD64=v1; native F compiled with `-C target-cpu=x86-64`; GOMAXPROCS=RAYON_NUM_THREADS=1. Machine: Intel Core i9-12950HX, 16 physical cores / 24 threads, 64 GiB host RAM (WSL about 51 GiB).

| Operation | n | Mean ms | SD ms | Min ms | Max ms | Median ms | Gas |
|---|---:|---:|---:|---:|---:|---:|---:|
| F | 10 | 39.680160 | 0.736683 | 38.699674 | 40.675333 | 39.666479 | 5,666,000 |
| ecrecover | 10 | 0.029131 | 0.001625 | 0.027743 | 0.033524 | 0.028769 | 3,000 |
| BN254-pairing | 10 | 0.434270 | 0.007917 | 0.424081 | 0.450863 | 0.433556 | 113,000 |
| BLS12-381-pairing | 10 | 0.724926 | 0.019860 | 0.700178 | 0.766243 | 0.720426 | 102,900 |

For each anchor, divide its actual `RequiredGas` by its median nanoseconds. Take the median of those three ratios (0.142832238927 gas/ns), multiply by F median time (39,666,479.23 ns), and round upward to the next 1,000 gas. Timing and mutation controls use the same executable and native library. Cold key initialization is recorded separately.

Ten actual recovery executions on fresh geth states all succeeded. Total transaction gas: mean 8,738,836.8, SD 18,209.6, min 8,717,476, max 8,770,396. Each preserves the 16,777,216 transaction gas cap; no exemption is enabled. Different proof encodings account for calldata gas variation. Recovery checks the BY_PROOF state, incremented migration nonce, exact commitment and unchanged ordinary nonce.

Targeted client regression: 43 pass, 0 fail, 17 skip (including subtests). The new geth executable was built successfully.

Raw samples, binary hashes, price calculation and reproducible harness are in [bench/verification-gas](../bench/verification-gas/README.md). These are in-process client measurements, not network throughput, production worst-case bounds, or approval of quantum security/hiding. Required implementation and validation gaps remain open work.

loop-internal self-review; not independently reviewed.
