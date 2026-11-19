# Modifications to Plonky3

This crate is a modified copy of Plonky3 p3-batch-stark 0.9.0-rc.1, under MIT OR Apache-2.0. Original copyright and license terms are retained in LICENSE-MIT and LICENSE-APACHE.

PQ-Migrate contributors modified the batch layout to commit quotient chunks and randomization polynomials in one tree (C3). The copy also includes optional diagnostics on stderr, enabled only with `PQ_PROVER_DIAGNOSTICS=1`: matrix shapes (`MATRICES`) and process memory (`MEMORY`, read from `/proc/self/status`). The added `diagnostics_enabled()` helper gates the shape output and the memory sampling and output.

This notice was added on 2026-11-02; it does not claim that upstream authored these changes.

Modified Rust files relative to the bundled pinned upstream copy:

- `src/lib.rs`
- `src/prover.rs`
- `src/transcript.rs`
- `src/verifier/mod.rs`

`Cargo.toml` is also modified to name the fork and select its local dependencies.
