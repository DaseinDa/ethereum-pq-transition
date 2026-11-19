# Modifications to Plonky3

This crate is a modified copy of Plonky3 p3-batch-stark 0.9.0-rc.1, under MIT OR Apache-2.0. Original copyright and license terms are retained in LICENSE-MIT and LICENSE-APACHE.

PQ-Migrate contributors made these changes, in order:

- optional diagnostics on stderr, enabled only with `PQ_PROVER_DIAGNOSTICS=1`: the prover-side `MATRICES` and `MEMORY` diagnostics of `prover/pinned-deps/p3-batch-stark`, gated by the added `diagnostics_enabled()` helper for shape output and memory sampling and output;
- C3: quotient chunks and randomization polynomials are committed in one tree;
- C3n: the required next-row column subsets are opened, with zero for omitted entries and a check of the layout;
- C3nP: the LogUp permutation trace of an AIR whose lookups read periodic columns.

The crate is named `p3-batch-stark-c3np`; the final proof F and its verifier (`prover/final-verifier`) use it.

This notice was added on 2026-11-07; it does not claim that upstream authored these changes.

Modified or added Rust files relative to the upstream crate:

- `src/error.rs`
- `src/lib.rs`
- `src/next_row.rs` (added)
- `src/periodic_logup.rs` (added)
- `src/prover.rs`
- `src/transcript.rs`
- `src/verifier/mod.rs`

`Cargo.toml` is also modified to name the fork; dev-dependencies and benches are dropped.
