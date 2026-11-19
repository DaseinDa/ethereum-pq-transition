//! The 198-byte public input, layout 2 (spec section 16.3 for the nine layout-1 fields and their offsets, section
//! 19.2 for the three fee fields), decoded field by field, and the canonical rules that hold for every PI a node
//! computes: `DOMAIN_TAG = keccak256(ASCII("PQ-MIGRATE-v1") || u256(chain_id))` (l. 62), `pq_pk_commit != 0` (pool
//! check 2), and the fee-field rules of section 19.2. Integers are big-endian. Which `chain_id`, `verifier_version`,
//! `alg_id` and `expiry` a node accepts is its own policy (checks 3 and 4), not this module's.
use core::fmt;

use tiny_keccak::{Hasher, Keccak};

/// Layout 2's length.
pub const PI_BYTES: usize = 198;

/// The twelve fields of a layout-2 PI.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pi198 {
    /// Offset 0, 32 bytes: u256 big-endian.
    pub chain_id: [u8; 32],
    /// Offset 32, 32 bytes.
    pub domain_tag: [u8; 32],
    /// Offset 64, 20 bytes.
    pub legacy_address: [u8; 20],
    /// Offset 84, u64.
    pub migration_nonce: u64,
    /// Offset 92, u8 (1: ML-DSA-44).
    pub alg_id: u8,
    /// Offset 93, 32 bytes: keccak256(u8(alg_id) || pq_pk).
    pub pq_pk_commit: [u8; 32],
    /// Offset 125, u32.
    pub verifier_version: u32,
    /// Offset 129, u64.
    pub expiry: u64,
    /// Offset 137, 32 bytes: u256 big-endian (wei).
    pub max_account_fee: [u8; 32],
    /// Offset 169, u8 (0 self-pay, 1 named sponsor, 2 zero-reimbursement third party, 3 public bounty).
    pub fee_mode: u8,
    /// Offset 170, 20 bytes.
    pub fee_sponsor: [u8; 20],
    /// Offset 190, u64.
    pub fee_auth_until: u64,
}

/// A PI that no node computes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StatementError {
    /// `DOMAIN_TAG` is not keccak256("PQ-MIGRATE-v1" || chain_id).
    DomainTagMismatch,
    /// `pq_pk_commit` is zero (`NON_CANONICAL_ENCODING`, pool check 2).
    ZeroPqPkCommit,
    /// `fee_mode` is not 0, 1, 2 or 3.
    UnknownFeeMode(u8),
    /// The fee fields break their mode's rule (section 19.2): modes 0 and 2 need a zero sponsor and a zero
    /// authorization time; mode 1 a non-zero sponsor and `fee_auth_until <= expiry`; mode 3 a zero sponsor and
    /// `fee_auth_until <= expiry`.
    FeeFields { fee_mode: u8, rule: &'static str },
}

impl fmt::Display for StatementError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DomainTagMismatch => f.write_str("DOMAIN_TAG is not keccak256(\"PQ-MIGRATE-v1\" || u256(chain_id))"),
            Self::ZeroPqPkCommit => f.write_str("pq_pk_commit is zero"),
            Self::UnknownFeeMode(m) => write!(f, "fee_mode {m} is not 0, 1, 2 or 3"),
            Self::FeeFields { fee_mode, rule } => write!(f, "fee mode {fee_mode}: {rule}"),
        }
    }
}

impl std::error::Error for StatementError {}

fn take<const N: usize>(b: &[u8; PI_BYTES], off: usize) -> [u8; N] {
    b[off..off + N].try_into().unwrap()
}

/// keccak256(ASCII("PQ-MIGRATE-v1") || chain_id), chain_id as the 32-byte big-endian integer.
pub fn domain_tag(chain_id: &[u8; 32]) -> [u8; 32] {
    let mut h = Keccak::v256();
    h.update(b"PQ-MIGRATE-v1");
    h.update(chain_id);
    let mut out = [0u8; 32];
    h.finalize(&mut out);
    out
}

/// A u256 big-endian from a u64.
pub fn u256(x: u64) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[24..].copy_from_slice(&x.to_be_bytes());
    out
}

impl Pi198 {
    /// Split 198 bytes into the twelve fields (never fails; `check_canonical` judges the values).
    pub fn decode(b: &[u8; PI_BYTES]) -> Pi198 {
        Pi198 {
            chain_id: take(b, 0),
            domain_tag: take(b, 32),
            legacy_address: take(b, 64),
            migration_nonce: u64::from_be_bytes(take(b, 84)),
            alg_id: b[92],
            pq_pk_commit: take(b, 93),
            verifier_version: u32::from_be_bytes(take(b, 125)),
            expiry: u64::from_be_bytes(take(b, 129)),
            max_account_fee: take(b, 137),
            fee_mode: b[169],
            fee_sponsor: take(b, 170),
            fee_auth_until: u64::from_be_bytes(take(b, 190)),
        }
    }

    /// The 198 bytes of these fields.
    pub fn encode(&self) -> [u8; PI_BYTES] {
        let mut b = [0u8; PI_BYTES];
        b[0..32].copy_from_slice(&self.chain_id);
        b[32..64].copy_from_slice(&self.domain_tag);
        b[64..84].copy_from_slice(&self.legacy_address);
        b[84..92].copy_from_slice(&self.migration_nonce.to_be_bytes());
        b[92] = self.alg_id;
        b[93..125].copy_from_slice(&self.pq_pk_commit);
        b[125..129].copy_from_slice(&self.verifier_version.to_be_bytes());
        b[129..137].copy_from_slice(&self.expiry.to_be_bytes());
        b[137..169].copy_from_slice(&self.max_account_fee);
        b[169] = self.fee_mode;
        b[170..190].copy_from_slice(&self.fee_sponsor);
        b[190..198].copy_from_slice(&self.fee_auth_until.to_be_bytes());
        b
    }

    /// `chain_id` as a u64 when it fits.
    pub fn chain_id_u64(&self) -> Option<u64> {
        self.chain_id[..24].iter().all(|&x| x == 0).then(|| u64::from_be_bytes(self.chain_id[24..].try_into().unwrap()))
    }

    /// The rules every node-computed layout-2 PI satisfies (see the module documentation).
    pub fn check_canonical(&self) -> Result<(), StatementError> {
        if self.domain_tag != domain_tag(&self.chain_id) {
            return Err(StatementError::DomainTagMismatch);
        }
        if self.pq_pk_commit == [0u8; 32] {
            return Err(StatementError::ZeroPqPkCommit);
        }
        let zero_sponsor = self.fee_sponsor == [0u8; 20];
        let fee = |rule| Err(StatementError::FeeFields { fee_mode: self.fee_mode, rule });
        match self.fee_mode {
            0 | 2 if !zero_sponsor => fee("fee_sponsor must be zero"),
            0 | 2 if self.fee_auth_until != 0 => fee("fee_auth_until must be zero"),
            1 if zero_sponsor => fee("fee_sponsor must be non-zero"),
            3 if !zero_sponsor => fee("fee_sponsor must be zero"),
            1 | 3 if self.fee_auth_until > self.expiry => fee("fee_auth_until must not exceed expiry"),
            0..=3 => Ok(()),
            m => Err(StatementError::UnknownFeeMode(m)),
        }
    }
}
