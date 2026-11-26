//! Measurement program: one ML-DSA-44 verification inside the Solana virtual machine.
//!
//! The registry program of `../program` carries the ML-DSA-44 signatures without verifying them. This program
//! measures what the verification costs when a program does it: it verifies the proof of possession of one key
//! with the verifier of [`mldsa44`] and does nothing else.
//!
//! Accounts: the wallet (signer). Data: ML-DSA-44 public key, signature. The signed message is the label
//! `pq-enroll-v1`, the wallet's address and the public key.

extern crate alloc;

pub mod mldsa44;

use solana_program::{
    account_info::AccountInfo, entrypoint, entrypoint::ProgramResult, program_error::ProgramError, pubkey::Pubkey,
};

pub const PQ_PUBKEY_LEN: usize = mldsa44::PUBLIC_KEY_LEN;
pub const PQ_SIG_LEN: usize = mldsa44::SIGNATURE_LEN;
pub const LABEL: &[u8] = b"pq-enroll-v1";

entrypoint!(process_instruction);

pub fn process_instruction(_program_id: &Pubkey, accounts: &[AccountInfo], data: &[u8]) -> ProgramResult {
    if data.len() != PQ_PUBKEY_LEN + PQ_SIG_LEN {
        return Err(ProgramError::InvalidInstructionData);
    }
    let wallet = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    if !wallet.is_signer {
        return Err(ProgramError::MissingRequiredSignature);
    }
    // The key and the signature are read where the instruction data lies; only the message is assembled, on
    // the heap.
    let (pq_pubkey, signature) = data.split_at(PQ_PUBKEY_LEN);
    let pq_pubkey: &[u8; PQ_PUBKEY_LEN] = pq_pubkey.try_into().map_err(|_| ProgramError::InvalidInstructionData)?;
    let signature: &[u8; PQ_SIG_LEN] = signature.try_into().map_err(|_| ProgramError::InvalidInstructionData)?;
    let mut message = Vec::with_capacity(LABEL.len() + 32 + PQ_PUBKEY_LEN);
    message.extend_from_slice(LABEL);
    message.extend_from_slice(wallet.key.as_ref());
    message.extend_from_slice(pq_pubkey);
    if mldsa44::verify(pq_pubkey, &message, signature) {
        Ok(())
    } else {
        Err(ProgramError::InvalidArgument)
    }
}
