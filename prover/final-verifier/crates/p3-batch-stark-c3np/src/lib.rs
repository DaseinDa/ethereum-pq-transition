// Modified by the PQ-Migrate contributors; see MODIFICATIONS.md (2026-11-07 notice).
#![doc = include_str!("../README.md")]
#![no_std]

extern crate alloc;

#[cfg(debug_assertions)]
mod check_constraints;
pub mod common;
pub mod config;
pub mod error;
pub mod folder;
pub mod next_row;
/// C3nP (L5 layer F2): the LogUp permutation trace with periodic columns in the row context.
pub mod periodic_logup;
pub mod proof;
pub mod prover;
pub mod security;
pub mod symbolic;
pub(crate) mod transcript;
pub mod verifier;

// Re-export main types and functions for convenience
pub use common::{CommonData, ProverData, ProverOnlyData};
pub use config::{
    Challenge, Commitment, Domain, PackedChallenge, PackedVal, PcsError, PcsProof,
    StarkGenericConfig, Val,
};
pub use error::BatchVerificationError;
pub use next_row::{
    MergedTrace, NextRowColumns, OmittedFill, TraceSplit, derive as derive_next_row_columns,
    next_row_columns_for_batch,
};
pub use p3_uni_stark::{OpenedValues, ProvingError, VerificationError};
pub use proof::{BatchCommitments, BatchOpenedValues, BatchProof};
pub use periodic_logup::generate_permutation_periodic;
pub use prover::{C3OpeningLayout, StarkInstance, prove_batch, prove_batch_with_next_row_columns};
pub use security::num_batched_openings;
pub use transcript::{
    BatchProverTranscript, BatchShape, BatchTranscriptFailure, BatchVerifierTranscript,
};
pub use verifier::{VerifierData, verify_batch, verify_batch_with_next_row_columns};
