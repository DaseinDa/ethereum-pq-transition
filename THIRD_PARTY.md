# Third-party components

Third-party code keeps its own licence. The main upstream components are:

| Component | Upstream | Licence | Use here |
|---|---|---|---|
| go-ethereum | <https://github.com/ethereum/go-ethereum> | LGPL-3.0-or-later (library code), GPL-3.0-or-later (go-ethereum's command-line programs) | the patched execution client; our changes to it are under the same licences (texts in `client/geth/COPYING` and `client/geth/COPYING.LESSER`) |
| Ream | <https://github.com/ReamLabs/ream> | MIT (text in `client/ream/LICENSE`) | the Lean consensus client |
| Plonky3 | <https://github.com/Plonky3/Plonky3> | MIT OR Apache-2.0 | the proof system |
| leanSig | <https://github.com/leanEthereum/leanSig> | Apache-2.0 | leanXMSS validator signatures (used by Ream) |
| fips204 | <https://github.com/integritychain/fips204> | MIT OR Apache-2.0 | ML-DSA-44 keys and signatures |
| Solana SDK crates | <https://github.com/anza-xyz/solana-sdk> | Apache-2.0 | the three programs under `solana/` (`solana-program` 6.0.0) and `solana/cost-check/` |
| Agave crates | <https://github.com/anza-xyz/agave>, <https://github.com/anza-xyz/agave-sdk> | Apache-2.0 | `solana/cost-check/`: `solana-cost-model`, `solana-runtime-transaction`, `solana-fee` and `agave-feature-set` 4.4.1, `agave-transaction-view` 7.0.0 |

The execution and consensus revisions and complete patched-source hashes are in
`client/geth/source.json` and `client/ream/source.json`. Rust dependency revisions
are fixed by each `Cargo.lock`; Go dependencies by the client's `go.mod` and
`go.sum`. The build does not substitute newer versions.

The directory `solana/` is outside the build and the two inventories described below. Its five `Cargo.lock`
files fix the dependencies of its crates, which Cargo fetches from crates.io; none is copied into this repository.

`third_party/rust-dependencies.json` and `third_party/go-dependencies.json` list
the dependency closure of the Linux builds and related tests. Their `notices`
entries refer to verbatim upstream texts under `third_party/licenses/`. Some
crate archives declare an SPDX licence but omit a separate notice file. Some
Git workspace members omit the SPDX field and inherit the licence at their
repository root; the inventory retains that distinction. This inventory is not
a legal compatibility opinion. Distribute the matching source archives and
patches with client binaries, including upstream notices; do not relabel those
sources under this repository's top-level dual licence.

Additional substantial dependencies include LeanVM/leanMultisig (Apache-2.0),
rust-kzg (Apache-2.0), CIRCL (BSD-3-Clause), RocksDB (Apache-2.0 OR GPL-2.0),
OpenSSL (Apache-2.0 for OpenSSL 3), and numerous Rust and Go libraries. The
per-package notices take precedence over this abbreviated table. In particular,
leanSig is Apache-2.0, not MIT OR Apache-2.0.

The fixed proof-verifier identity hashes portions of its source text. Those
algorithm identifiers and source strings are preserved exactly; editing them
for presentation would change the verification-key identity. Historical reports
and expiring proofs are not part of the runtime package.

Six directories hold modified copies of Plonky3 crates. Each includes the verbatim upstream `LICENSE-MIT` and
`LICENSE-APACHE`, copied from the official Plonky3 Git object `2ba5dfb3c4423f68165928983b3e09b694b15dc5`, a
`MODIFICATIONS.md`, and a notice at the top of every changed or added Rust file; no upstream copyright or licence terms
were replaced.

| Directory | Upstream crate | Changes |
|---|---|---|
| `prover/pinned-deps/p3-batch-stark` | p3-batch-stark 0.9.0-rc.1 | optional prover-side memory and matrix-shape diagnostics |
| `prover/pinned-deps/p3-merkle-tree` | p3-merkle-tree 0.9.0-rc.1 | a prover-side node cache that recomputes dropped digests, and the same diagnostics |
| `prover/crates/p3-batch-stark-c3` | p3-batch-stark 0.9.0-rc.1 | quotient chunks and randomization polynomials in one tree (C3), and optional memory and matrix-shape diagnostics |
| `prover/crates/p3-batch-stark-c3n` | p3-batch-stark 0.9.0-rc.1 | C3, next-row subset openings (C3n), and optional memory and matrix-shape diagnostics |
| `prover/final-verifier/crates/p3-batch-stark-c3np` | p3-batch-stark 0.9.0-rc.1 | the diagnostics, C3, C3n and LogUp over periodic lookups (C3nP) |
| `prover/final-verifier/crates/p3-merkle-tree-ps` | p3-merkle-tree 0.9.0-rc.1 | the node cache, the diagnostics (including salt-generation metadata), and salts from a per-matrix ChaCha20 seed (verifier unchanged) |

All six copies include optional diagnostics on stderr, enabled only with `PQ_PROVER_DIAGNOSTICS=1`. Their added `diagnostics_enabled()` helper gates matrix-shape output (`MATRICES`) and process-memory sampling and output (`MEMORY`, read from `/proc/self/status`); it also gates the `SALTS` metadata output in `p3-merkle-tree-ps`. Diagnostics are disabled when the variable is absent or has any other value.

The two `pinned-deps` copies keep the upstream package names and versions; `[patch.crates-io]` in
`prover/tree/Cargo.toml` substitutes them for the crates.io packages. When `tools/licenses.py` regenerates
`third_party/rust-dependencies.json`, it includes these vendored path packages with their own notices. The committed
inventory predates the vendored copies and lists p3-batch-stark and p3-merkle-tree 0.9.0-rc.1 as crates.io packages
without notices; each of the six copies carries its own `LICENSE-MIT`, `LICENSE-APACHE` and `MODIFICATIONS.md`.
