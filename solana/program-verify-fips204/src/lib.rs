//! Control for program-verify: the same instruction, verified with the fips204 crate.

use fips204::ml_dsa_44;
use fips204::traits::{SerDes, Verifier};
use solana_program::{
    account_info::AccountInfo, entrypoint, entrypoint::ProgramResult, program_error::ProgramError, pubkey::Pubkey,
};

pub const PQ_PUBKEY_LEN: usize = 1312;
pub const PQ_SIG_LEN: usize = 2420;
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
    let (pq_pubkey, signature) = data.split_at(PQ_PUBKEY_LEN);
    let pq_pubkey: [u8; PQ_PUBKEY_LEN] = pq_pubkey.try_into().map_err(|_| ProgramError::InvalidInstructionData)?;
    let signature: [u8; PQ_SIG_LEN] = signature.try_into().map_err(|_| ProgramError::InvalidInstructionData)?;
    let mut message = Vec::with_capacity(LABEL.len() + 32 + PQ_PUBKEY_LEN);
    message.extend_from_slice(LABEL);
    message.extend_from_slice(wallet.key.as_ref());
    message.extend_from_slice(&pq_pubkey);
    let key = ml_dsa_44::PublicKey::try_from_bytes(pq_pubkey).map_err(|_| ProgramError::InvalidArgument)?;
    if key.verify(&message, &signature, &[]) {
        Ok(())
    } else {
        Err(ProgramError::InvalidArgument)
    }
}
