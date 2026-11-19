//! # pq-final-verifier
//!
//! The verifier of **F**, the final layer of the PQ-Migrate migration proof (the candidate tree L0' v2 -> B -> F of
//! the L5 records): the proof that a carrier would hold, at most `MAX_PROOF_BYTES` = 196,608 bytes. Exactly F's
//! verifier path of the record code/l5-layer-f2-20261031: `p3_batch_stark_c3np::verify_batch_with_next_row_columns`
//! (C3n's verifier) with F's AIR (`fkernel.rs`, byte-identical), F's key data, F's opened next-row sets, F's PCS
//! (`HidingFriPcs` over `p3_merkle_tree_ps`) and F's transcript prefix (F's domain, F's verifier-key digest, the 198
//! public values).
//!
//! ```no_run
//! let proof: Vec<u8> = std::fs::read("proof.postcard").unwrap();
//! let pi198: [u8; 198] = [0u8; 198]; // the node computes the PI from the transaction's fields
//! match pq_final_verifier::verify(&proof, &pi198, &pq_final_verifier::TRUSTED_PARAMS) {
//!     Ok(()) => println!("accepted"),
//!     Err(e) if e.is_rejection() => println!("rejected: {e}"),
//!     Err(e) => println!("local fault (not a verdict): {e}"),
//! }
//! ```
//!
//! What `TRUSTED_PARAMS` pins and how the crate checks it: see `TrustedParams` and the README. Research packaging;
//! loop-internal self-review; not independently reviewed. No figure here is a post-quantum security level.
use std::panic::{AssertUnwindSafe, catch_unwind};

use p3_batch_stark_c3np::{BatchVerificationError, OmittedFill};
use p3_field::PrimeCharacteristicRing;
use p3_fri::verifier::FriError;
use p3_koala_bear::KoalaBear as F;
use p3_lookup::LookupError;
use p3_uni_stark::VerificationError;

mod error;
#[allow(dead_code)]
mod fkernel;
mod key;
#[allow(dead_code)]
mod material;
mod pi;

pub use error::{ErrorClass, VerifyError};
pub use key::{FriPcsParams, TRUSTED_PARAMS, TrustedParams};
pub use pi::{PI_BYTES, Pi198, StatementError, domain_tag, u256};

/// `MAX_PROOF_BYTES` of spec l. 72 (192 KiB); `TRUSTED_PARAMS.max_proof_bytes()` is the value `verify` uses.
pub const MAX_PROOF_BYTES: usize = 196_608;

/// Verify a proof of F for a 198-byte statement (PI layout 2) under the pinned parameters.
///
/// In this order: the size (`ProofTooLarge`, before decoding); strict decoding of F's proof type (postcard; no
/// trailing byte; the canonical re-encoding must equal the input); the statement's canonical rules (`Pi198`); F's
/// verifier key (built once per process from the embedded material and checked against `params`); the proof's degree
/// bits; then F's STARK verifier. `Ok(())` means accepted. Every `Err` says why, in one of three classes
/// (`VerifyError::class`): an invalid input, a proof rejected by the STARK verifier, or a local fault that is not a
/// verdict on the proof. A panic inside the verifier is caught and returned as `Internal` (unwinding builds only).
pub fn verify(proof_bytes: &[u8], expected_pi198: &[u8; PI_BYTES], params: &TrustedParams) -> Result<(), VerifyError> {
    if proof_bytes.len() > params.max_proof_bytes() {
        return Err(VerifyError::ProofTooLarge { len: proof_bytes.len(), max: params.max_proof_bytes() });
    }
    let proof = decode_strict(proof_bytes)?;
    Pi198::decode(expected_pi198).check_canonical().map_err(VerifyError::Statement)?;
    let key = key::verifier_key(params)?;
    let want = vec![key.air.log_n + 1];
    if proof.degree_bits != want {
        return Err(VerifyError::Shape(format!("degree bits {:?}, expected {want:?}", proof.degree_bits)));
    }
    let pv: Vec<F> = expected_pi198.iter().map(|&b| F::from_u8(b)).collect();
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        let cfg = key::config(params, &pv);
        p3_batch_stark_c3np::verify_batch_with_next_row_columns(&cfg, std::slice::from_ref(&key.air), &proof, &[pv.clone()], &key.common,
            std::slice::from_ref(&key.opened), OmittedFill::Zero)
    }));
    match outcome {
        Ok(Ok(())) => Ok(()),
        Ok(Err(e)) => Err(classify(e)),
        Err(p) => Err(VerifyError::Internal(panic_message(p))),
    }
}

/// Build (once) and check F's verifier key without verifying anything: for a node's start-up. Returns the time the
/// build took in milliseconds (0 when it was already built).
pub fn verifier_ready(params: &TrustedParams) -> Result<f64, VerifyError> {
    key::verifier_key(params).map(|k| k.build_ms)
}

/// Strict decoding of F's proof: postcard, the whole input, and a canonical encoding.
pub fn decode_strict(bytes: &[u8]) -> Result<key::FProof, VerifyError> {
    let decoded = catch_unwind(AssertUnwindSafe(|| postcard::take_from_bytes::<key::FProof>(bytes)));
    let (proof, rest) = match decoded {
        Ok(Ok(x)) => x,
        Ok(Err(e)) => return Err(VerifyError::Decode(format!("{e}"))),
        Err(p) => return Err(VerifyError::Internal(format!("decoding: {}", panic_message(p)))),
    };
    if !rest.is_empty() {
        return Err(VerifyError::TrailingBytes { consumed: bytes.len() - rest.len(), trailing: rest.len() });
    }
    match postcard::to_allocvec(&proof) {
        Ok(again) if again == bytes => Ok(proof),
        Ok(_) => Err(VerifyError::NonCanonicalEncoding),
        Err(e) => Err(VerifyError::Internal(format!("re-encoding: {e}"))),
    }
}

fn panic_message(p: Box<dyn std::any::Any + Send>) -> String {
    p.downcast_ref::<String>().cloned().or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string())).unwrap_or_else(|| "panic".into())
}

type PcsError = FriError<p3_merkle_tree_ps::MerkleTreeError, p3_merkle_tree_ps::MerkleTreeError>;

/// The STARK verifier's error, mapped to the variant that names the check that failed.
fn classify(e: BatchVerificationError<PcsError>) -> VerifyError {
    match e {
        BatchVerificationError::Verification(v) => match v {
            VerificationError::InvalidProofShape(s) => VerifyError::Shape(format!("{s}")),
            VerificationError::PeriodicColumn(s) => VerifyError::Shape(format!("{s}")),
            VerificationError::InvalidOpeningArgument(fe) => classify_pcs(fe),
            VerificationError::OodEvaluationMismatch { index } => {
                VerifyError::Constraint(format!("OodEvaluationMismatch {{ index: {index:?} }}: F's constraint identity at zeta"))
            }
            VerificationError::RandomizationError => VerifyError::Shape("RandomizationError: the batch randomization does not match the hiding setting".into()),
            VerificationError::NextPointUnavailable => VerifyError::Shape("NextPointUnavailable".into()),
            VerificationError::OodPointInDomain => VerifyError::Transcript("OodPointInDomain: the out-of-domain point lies in the trace domain".into()),
            VerificationError::InvalidOodPowWitness => VerifyError::Transcript("InvalidOodPowWitness".into()),
        },
        BatchVerificationError::Lookup(LookupError::TerminalSumNonZero) => VerifyError::LookupTerminal,
        BatchVerificationError::Lookup(l) => VerifyError::Shape(format!("lookup: {l}")),
        BatchVerificationError::Transcript(t) => VerifyError::Transcript(format!("{t}")),
        e @ BatchVerificationError::NextRowOpening { .. } => VerifyError::Shape(format!("{e}")),
        e @ BatchVerificationError::NextRowColumns { .. } => VerifyError::VerifierKey(format!("{e}")),
    }
}

fn classify_pcs(fe: PcsError) -> VerifyError {
    match fe {
        FriError::InputError(e) => VerifyError::CommitmentOpening(format!("{e:?}")),
        FriError::CommitPhaseMmcsError(e) => VerifyError::Fri(format!("commit-phase opening: {e:?}")),
        FriError::FinalPolyMismatch => VerifyError::Fri("FinalPolyMismatch: the last fold differs from the final polynomial".into()),
        e @ FriError::OpeningPointMatchesQueryPoint { .. } => VerifyError::Fri(format!("{e}")),
        e @ (FriError::InvalidPowWitness(_) | FriError::NonCanonicalPowWitness { .. }) => VerifyError::Transcript(format!("{e}")),
        // Every other variant is a count, length, height or schedule mismatch: the proof's shape.
        e => VerifyError::Shape(format!("{e}")),
    }
}
