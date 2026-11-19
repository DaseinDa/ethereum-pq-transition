//! The verifier's error type. Every variant belongs to exactly one class (`VerifyError::class`):
//!
//! | Class | Meaning | Variants |
//! |---|---|---|
//! | `InvalidInput` | the input fails a check made before any cryptography; the proof is invalid for this statement | `ProofTooLarge`, `Decode`, `TrailingBytes`, `NonCanonicalEncoding`, `Statement` |
//! | `InvalidProof` | F's STARK verifier rejected the proof for this statement (a cryptographic rejection) | `Shape`, `Transcript`, `CommitmentOpening`, `Fri`, `Constraint`, `LookupTerminal` |
//! | `LocalFault` | the verifier could not run as pinned; **not** a verdict on the proof | `VerifierKey`, `Internal` |
//!
//! A proof made for another statement (a well-formed PI198 other than the proven one) is rejected in class
//! `InvalidProof`: every public value is absorbed by F's transcript before the first commitment, so the challenges and
//! the query positions differ, and which check fails first depends on them (the recorded control flipped one public
//! value and got a pruned Merkle proof that no longer fits the queried positions). Rely on the class, not on the
//! variant, for such rejections.
use core::fmt;

use crate::childpin::pi::StatementError;

/// The coarse class of a `VerifyError`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ErrorClass {
    /// Size, decoding or statement: rejected before any cryptographic check.
    InvalidInput,
    /// Rejected by F's STARK verifier.
    InvalidProof,
    /// The verifier itself failed; retry or report, never treat as a rejection of the proof.
    LocalFault,
}

/// Why `verify` did not accept.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VerifyError {
    /// The proof is longer than `MAX_PROOF_BYTES` (196,608). Checked first, before decoding.
    ProofTooLarge { len: usize, max: usize },
    /// The bytes do not decode as F's proof type (postcard): empty, truncated, an out-of-range tag or length, a
    /// non-canonical field element that the decoder refuses.
    Decode(String),
    /// A proof decodes from a prefix of the input and bytes are left over.
    TrailingBytes { consumed: usize, trailing: usize },
    /// The proof decodes, but its canonical encoding differs from the input (an overlong varint, for instance): the
    /// encoding of a proof is unique.
    NonCanonicalEncoding,
    /// The 198-byte statement is not a canonical layout-2 PI (spec section 16.3 and section 19.2): `DOMAIN_TAG` is not
    /// keccak256("PQ-MIGRATE-v1" || chain_id), `pq_pk_commit` is zero, or the fee fields break their mode's rule.
    Statement(StatementError),
    /// The proof's shape is not F's (degree bits, instance count, widths, next-row openings, round, query and value
    /// counts), found by a check that no transcript challenge affects.
    Shape(String),
    /// A transcript step rejected its value (a grinding witness, which F does not use, or an out-of-domain point
    /// inside the trace domain).
    Transcript(String),
    /// A Merkle opening of one of F's three input commitments (the main trace, the quotient chunks with the
    /// randomization polynomial, the permutation trace) does not authenticate to the commitment at the queried
    /// position, or its pruned proof does not fit the queried positions.
    CommitmentOpening(String),
    /// FRI rejected: a commit-phase Merkle opening, a fold, or the final polynomial.
    Fri(String),
    /// F's constraint identity at the out-of-domain point does not hold (the quotient check).
    Constraint(String),
    /// The global LogUp terminal sum is not zero.
    LookupTerminal,
    /// The embedded verifier-key material does not reproduce `TrustedParams` (a corrupted build), or the parameters
    /// passed are not the pinned ones. A local fault.
    VerifierKey(String),
    /// The verifier panicked (caught). A local fault; report it with the input.
    Internal(String),
}

impl VerifyError {
    pub fn class(&self) -> ErrorClass {
        match self {
            Self::ProofTooLarge { .. } | Self::Decode(_) | Self::TrailingBytes { .. } | Self::NonCanonicalEncoding | Self::Statement(_) => {
                ErrorClass::InvalidInput
            }
            Self::Shape(_) | Self::Transcript(_) | Self::CommitmentOpening(_) | Self::Fri(_) | Self::Constraint(_) | Self::LookupTerminal => {
                ErrorClass::InvalidProof
            }
            Self::VerifierKey(_) | Self::Internal(_) => ErrorClass::LocalFault,
        }
    }
    /// A short stable name of the variant (for logs and the C ABI).
    pub fn kind(&self) -> &'static str {
        match self {
            Self::ProofTooLarge { .. } => "proof_too_large",
            Self::Decode(_) => "decode",
            Self::TrailingBytes { .. } => "trailing_bytes",
            Self::NonCanonicalEncoding => "non_canonical_encoding",
            Self::Statement(_) => "statement",
            Self::Shape(_) => "shape",
            Self::Transcript(_) => "transcript",
            Self::CommitmentOpening(_) => "commitment_opening",
            Self::Fri(_) => "fri",
            Self::Constraint(_) => "constraint",
            Self::LookupTerminal => "lookup_terminal",
            Self::VerifierKey(_) => "verifier_key",
            Self::Internal(_) => "internal",
        }
    }
    /// True for every rejection of the input or the proof; false for a local fault.
    pub fn is_rejection(&self) -> bool {
        self.class() != ErrorClass::LocalFault
    }
}

impl fmt::Display for VerifyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ProofTooLarge { len, max } => write!(f, "proof of {len} bytes exceeds MAX_PROOF_BYTES = {max}"),
            Self::Decode(e) => write!(f, "proof does not decode: {e}"),
            Self::TrailingBytes { consumed, trailing } => write!(f, "{trailing} trailing bytes after a proof of {consumed} bytes"),
            Self::NonCanonicalEncoding => f.write_str("proof encoding is not canonical (re-encoding differs)"),
            Self::Statement(e) => write!(f, "statement is not a canonical layout-2 PI: {e}"),
            Self::Shape(e) => write!(f, "proof shape is not F's: {e}"),
            Self::Transcript(e) => write!(f, "transcript check failed: {e}"),
            Self::CommitmentOpening(e) => write!(f, "commitment opening failed: {e}"),
            Self::Fri(e) => write!(f, "FRI check failed: {e}"),
            Self::Constraint(e) => write!(f, "constraint check failed: {e}"),
            Self::LookupTerminal => f.write_str("LogUp terminal sum is not zero"),
            Self::VerifierKey(e) => write!(f, "local fault, verifier key: {e}"),
            Self::Internal(e) => write!(f, "local fault, verifier panicked: {e}"),
        }
    }
}

impl std::error::Error for VerifyError {}
