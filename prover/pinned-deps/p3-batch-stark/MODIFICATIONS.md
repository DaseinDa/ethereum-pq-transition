# Modifications to Plonky3

This crate is a modified copy of Plonky3 p3-batch-stark 0.9.0-rc.1, under MIT OR Apache-2.0. Original copyright and license terms are retained in LICENSE-MIT and LICENSE-APACHE. It keeps the upstream package name and version, so that `[patch.crates-io]` in `prover/tree/Cargo.toml` substitutes it for the crates.io package.

PQ-Migrate contributors added optional diagnostics on stderr, enabled only with `PQ_PROVER_DIAGNOSTICS=1`: the matrix shapes (`MATRICES` lines) and the process's memory (`MEMORY` lines, read from `/proc/self/status`). The added `diagnostics_enabled()` helper gates the shape output and the memory sampling and output. They change no commitment, transcript, proof or verification.

This notice was added on 2026-11-07; it does not claim that upstream authored these changes.

Modified or added Rust files relative to the upstream crate:

- `src/prover.rs`
