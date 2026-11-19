# Modifications to Plonky3

This crate is a modified copy of Plonky3 p3-merkle-tree 0.9.0-rc.1, under MIT OR Apache-2.0. Original copyright and license terms are retained in LICENSE-MIT and LICENSE-APACHE. It keeps the upstream package name and version, so that `[patch.crates-io]` in `prover/tree/Cargo.toml` substitutes it for the crates.io package.

PQ-Migrate contributors made two prover-side changes:

- a node cache: for binary trees whose matrices have power-of-two heights, the MMCS drops the lowest digest layers (at most four, never those the cap needs) after committing, and recomputes a dropped node from the retained leaves when an opening needs it, so that large commitments fit in memory; the root, the cap and every opened digest are the ones upstream computes;
- optional diagnostics on stderr, enabled only with `PQ_PROVER_DIAGNOSTICS=1`: the `MATRICES` and `MEMORY` diagnostics of the batch-STARK copy. The added `diagnostics_enabled()` helper gates the shape output and the memory sampling and output.

Commitments, openings and verification are unchanged.

This notice was added on 2026-11-07; it does not claim that upstream authored these changes.

Modified or added Rust files relative to the upstream crate:

- `src/builder.rs`
- `src/hiding_mmcs.rs`
- `src/merkle_tree.rs`
- `src/mmcs/batch.rs`
- `src/mmcs/mod.rs`
