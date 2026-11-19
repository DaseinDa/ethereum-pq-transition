# Modifications to Plonky3

This crate is a modified copy of Plonky3 p3-merkle-tree 0.9.0-rc.1, under MIT OR Apache-2.0. Original copyright and license terms are retained in LICENSE-MIT and LICENSE-APACHE.

PQ-Migrate contributors made these changes:

- the prover-side node cache of `prover/pinned-deps/p3-merkle-tree` and optional diagnostics on stderr, enabled only with `PQ_PROVER_DIAGNOSTICS=1`: matrix shapes (`MATRICES`), process memory (`MEMORY`, read from `/proc/self/status`) and salt-generation metadata (`SALTS`). The added `diagnostics_enabled()` helper gates the diagnostic output and memory sampling;
- the hiding MMCS draws each committed matrix's salts from ChaCha20 keyed by a per-matrix 256-bit seed that lives only in the prover data, instead of storing the salt matrix; every read of a row returns the same salts, so leaf hashes, openings and recomputed nodes agree. The verifier path is unchanged.

The crate is named `p3-merkle-tree-ps`; the final proof F and its verifier (`prover/final-verifier`) use it.

This notice was added on 2026-11-07; it does not claim that upstream authored these changes.

Modified or added Rust files relative to the upstream crate:

- `src/builder.rs`
- `src/hiding_mmcs.rs`
- `src/merkle_tree.rs`
- `src/mmcs/batch.rs`
- `src/mmcs/mod.rs`

`Cargo.toml` is also modified to name the fork and add `chacha20`; dev-dependencies and benches are dropped.
