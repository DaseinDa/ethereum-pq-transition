//! Measurement program: a post-quantum key registry for Solana wallets.
//!
//! It mirrors the two steps an Ethereum account takes on the paper's enrollment path:
//!
//! * `Enroll` (the paper's `0x7d`): a wallet, signing with its Ed25519 key, registers a commitment to an
//!   ML-DSA-44 public key. The transaction carries the public key and a proof of possession.
//! * `Activate` (the paper's first `0x7c`): the transaction carries the public key and an ML-DSA-44 signature;
//!   the program checks the key against the commitment and stores it.
//!
//! A wallet has one record: the account at the address that the system program derives from the wallet's
//! address, the seed `pq-enroll` and this program's id. The wallet itself signs for that address, so nobody else
//! can create the record, and a wallet cannot have a second one.
//!
//! The stock validator has no ML-DSA verifier, so this program does NOT verify the two ML-DSA signatures. It
//! carries them, so that every transaction has its real size, and does all the other work. The run charges
//! the verification separately (see the README). Do not deploy this program to hold value.

use solana_program::{
    account_info::{next_account_info, AccountInfo},
    entrypoint,
    entrypoint::ProgramResult,
    program::invoke,
    program_error::ProgramError,
    pubkey::Pubkey,
    rent::Rent,
    sysvar::{clock::Clock, Sysvar},
};
use solana_system_interface::instruction as system_instruction;

/// ML-DSA-44 sizes (FIPS 204).
pub const PQ_PUBKEY_LEN: usize = 1312;
pub const PQ_SIG_LEN: usize = 2420;

/// Seed of a wallet's record address.
pub const RECORD_SEED: &str = "pq-enroll";

pub const MODE_ENROLLED: u8 = 1;
pub const MODE_ACTIVATED: u8 = 2;
pub const SCHEME_ML_DSA_44: u8 = 1;

/// Record layout: mode, scheme, enrollment slot, commitment; the public key follows at activation.
pub const OFF_MODE: usize = 0;
pub const OFF_SCHEME: usize = 1;
pub const OFF_SLOT: usize = 2;
pub const OFF_COMMITMENT: usize = 10;
pub const OFF_PUBKEY: usize = 42;
pub const RECORD_LEN_ENROLLED: usize = OFF_PUBKEY;
pub const RECORD_LEN_ACTIVATED: usize = OFF_PUBKEY + PQ_PUBKEY_LEN;

pub const IX_ENROLL: u8 = 0;
pub const IX_ACTIVATE: u8 = 1;

entrypoint!(process_instruction);

pub fn process_instruction(program_id: &Pubkey, accounts: &[AccountInfo], data: &[u8]) -> ProgramResult {
    match data.first() {
        Some(&IX_ENROLL) => enroll(program_id, accounts, &data[1..]),
        Some(&IX_ACTIVATE) => activate(program_id, accounts, &data[1..]),
        _ => Err(ProgramError::InvalidInstructionData),
    }
}

/// The three accounts of both instructions: wallet (signer, writable), its record (writable), system program.
fn wallet_and_record<'a, 'b>(
    program_id: &Pubkey,
    accounts: &'a [AccountInfo<'b>],
) -> Result<(&'a AccountInfo<'b>, &'a AccountInfo<'b>, &'a AccountInfo<'b>), ProgramError> {
    let iter = &mut accounts.iter();
    let wallet = next_account_info(iter)?;
    let record = next_account_info(iter)?;
    let system_program = next_account_info(iter)?;
    if !wallet.is_signer {
        return Err(ProgramError::MissingRequiredSignature);
    }
    let expected =
        Pubkey::create_with_seed(wallet.key, RECORD_SEED, program_id).map_err(|_| ProgramError::InvalidSeeds)?;
    if expected != *record.key {
        return Err(ProgramError::InvalidSeeds);
    }
    Ok((wallet, record, system_program))
}

/// Data: ML-DSA-44 public key, proof of possession.
fn enroll(program_id: &Pubkey, accounts: &[AccountInfo], data: &[u8]) -> ProgramResult {
    if data.len() != PQ_PUBKEY_LEN + PQ_SIG_LEN {
        return Err(ProgramError::InvalidInstructionData);
    }
    let pq_pubkey = &data[..PQ_PUBKEY_LEN];
    let (wallet, record, system_program) = wallet_and_record(program_id, accounts)?;
    if record.owner == program_id || !record.data_is_empty() {
        return Err(ProgramError::AccountAlreadyInitialized);
    }

    let commitment = solana_sha256_hasher::hashv(&[pq_pubkey]);
    let rent = Rent::get()?.minimum_balance(RECORD_LEN_ENROLLED);
    let infos = [wallet.clone(), record.clone(), system_program.clone()];
    if record.lamports() == 0 {
        invoke(
            &system_instruction::create_account_with_seed(
                wallet.key,
                record.key,
                wallet.key,
                RECORD_SEED,
                rent,
                RECORD_LEN_ENROLLED as u64,
                program_id,
            ),
            &infos,
        )?;
    } else {
        // Someone sent lamports to the address first. Creating it would fail, so top it up and allocate it.
        let top_up = rent.saturating_sub(record.lamports());
        if top_up > 0 {
            invoke(&system_instruction::transfer(wallet.key, record.key, top_up), &infos)?;
        }
        invoke(
            &system_instruction::allocate_with_seed(
                record.key,
                wallet.key,
                RECORD_SEED,
                RECORD_LEN_ENROLLED as u64,
                program_id,
            ),
            &infos,
        )?;
    }

    let slot = Clock::get()?.slot;
    let mut out = record.try_borrow_mut_data()?;
    out[OFF_MODE] = MODE_ENROLLED;
    out[OFF_SCHEME] = SCHEME_ML_DSA_44;
    out[OFF_SLOT..OFF_SLOT + 8].copy_from_slice(&slot.to_le_bytes());
    out[OFF_COMMITMENT..OFF_COMMITMENT + 32].copy_from_slice(commitment.as_ref());
    Ok(())
}

/// Data: ML-DSA-44 public key, ML-DSA-44 signature.
fn activate(program_id: &Pubkey, accounts: &[AccountInfo], data: &[u8]) -> ProgramResult {
    if data.len() != PQ_PUBKEY_LEN + PQ_SIG_LEN {
        return Err(ProgramError::InvalidInstructionData);
    }
    let pq_pubkey = &data[..PQ_PUBKEY_LEN];
    let (wallet, record, system_program) = wallet_and_record(program_id, accounts)?;
    if record.owner != program_id {
        return Err(ProgramError::IllegalOwner);
    }
    {
        let cur = record.try_borrow_data()?;
        if cur.len() != RECORD_LEN_ENROLLED || cur[OFF_MODE] != MODE_ENROLLED {
            return Err(ProgramError::InvalidAccountData);
        }
        let commitment = solana_sha256_hasher::hashv(&[pq_pubkey]);
        if commitment.as_ref() != &cur[OFF_COMMITMENT..OFF_COMMITMENT + 32] {
            return Err(ProgramError::InvalidArgument);
        }
    }

    let need = Rent::get()?.minimum_balance(RECORD_LEN_ACTIVATED);
    let top_up = need.saturating_sub(record.lamports());
    if top_up > 0 {
        invoke(
            &system_instruction::transfer(wallet.key, record.key, top_up),
            &[wallet.clone(), record.clone(), system_program.clone()],
        )?;
    }
    record.resize(RECORD_LEN_ACTIVATED)?;
    let mut out = record.try_borrow_mut_data()?;
    out[OFF_PUBKEY..OFF_PUBKEY + PQ_PUBKEY_LEN].copy_from_slice(pq_pubkey);
    out[OFF_MODE] = MODE_ACTIVATED;
    Ok(())
}
