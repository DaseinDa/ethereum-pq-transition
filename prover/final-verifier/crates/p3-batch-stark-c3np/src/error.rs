// Modified by the PQ-Migrate contributors; see MODIFICATIONS.md (2026-11-07 notice).
//! Error types for batch-STARK verification.

use core::fmt::Debug;

use p3_lookup::LookupError;
use p3_uni_stark::{InvalidProofShapeError, PeriodicColumnShapeError, VerificationError};
use thiserror::Error;

use crate::transcript::BatchTranscriptFailure;

/// Failure returned when verifying a batch proof.
///
/// A batch proof layers a lookup argument on top of a generic multi-AIR STARK.
/// Verification can therefore fail in three independent ways.
///
/// - The generic STARK part rejects the proof shape, an opening, or an evaluation.
/// - The lookup argument rejects the auxiliary trace or the cross-AIR balance.
/// - A described transcript step rejects the value the proof carries for it.
///
/// Splitting them keeps lookup and transcript concerns out of the base STARK error type.
#[derive(Debug, Error)]
pub enum BatchVerificationError<PcsErr>
where
    PcsErr: Debug,
{
    /// A generic STARK verification failure.
    #[error(transparent)]
    Verification(#[from] VerificationError<PcsErr>),
    /// A lookup-argument verification failure.
    #[error(transparent)]
    Lookup(#[from] LookupError),
    /// A described transcript step the proof failed to satisfy.
    ///
    /// Both grinding sites report here.
    ///
    /// A rejection means the witness was forged.
    /// It also means the two sides may have been configured with different difficulties.
    #[error(transparent)]
    Transcript(#[from] BatchTranscriptFailure),
    /// C3n: a next-row opening that does not match the column set derived from the AIR (`None` stands for
    /// an absent opening). Checked before the transcript starts.
    #[error("instance {air}: {trace} next-row openings: expected {expected:?} values, got {got:?}")]
    NextRowOpening {
        /// Instance index.
        air: usize,
        /// `main`, `preprocessed` or `permutation`.
        trace: &'static str,
        /// The derived count (`None`: no next-row opening).
        expected: Option<usize>,
        /// The proof's count (`None`: no next-row opening).
        got: Option<usize>,
    },
    /// C3n: a next-row column set that cannot describe this batch (not strictly increasing, outside its
    /// width, or for another width), or a proper preprocessed subset, which the key's one matrix per
    /// instance cannot open (only none or every preprocessed column is supported).
    #[error("instance {air}: next-row column set unusable: {reason}")]
    NextRowColumns {
        /// Instance index.
        air: usize,
        /// What is wrong with it.
        reason: &'static str,
    },
}

impl<PcsErr: Debug> From<InvalidProofShapeError> for BatchVerificationError<PcsErr> {
    fn from(err: InvalidProofShapeError) -> Self {
        Self::Verification(VerificationError::InvalidProofShape(err))
    }
}

impl<PcsErr: Debug> From<PeriodicColumnShapeError> for BatchVerificationError<PcsErr> {
    fn from(err: PeriodicColumnShapeError) -> Self {
        Self::Verification(VerificationError::PeriodicColumn(err))
    }
}
