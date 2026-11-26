//! The program's instruction, run on the host: the answers for a valid proof of possession, for the client's
//! tampered one and for malformed calls.

use fips204::ml_dsa_44;
use fips204::traits::{KeyGen as _, SerDes as _, Signer as _};
use pq_verify_in_vm::{process_instruction, LABEL, PQ_PUBKEY_LEN, PQ_SIG_LEN};
use solana_program::{account_info::AccountInfo, program_error::ProgramError, pubkey::Pubkey};

fn call(wallet: Option<(&Pubkey, bool)>, data: &[u8]) -> Result<(), ProgramError> {
    let program_id = Pubkey::new_from_array([9; 32]);
    let owner = Pubkey::new_from_array([0; 32]);
    let mut lamports = 1;
    let mut account_data = [];
    let mut accounts = Vec::new();
    if let Some((key, is_signer)) = wallet {
        accounts.push(AccountInfo::new(key, is_signer, true, &mut lamports, &mut account_data, &owner, false));
    }
    process_instruction(&program_id, &accounts, data)
}

#[test]
fn proof_of_possession() {
    let wallet = Pubkey::new_from_array([3; 32]);
    let (pk, sk) = ml_dsa_44::KG::keygen_from_seed(&[1; 32]);
    let pk = pk.into_bytes();
    // The message of the client: label, wallet address, public key.
    let message = [LABEL, wallet.as_ref(), &pk].concat();
    assert_eq!(message.len(), 1356);
    let sig = sk.try_sign_with_seed(&[2; 32], &message, &[]).expect("signing");
    let data = [pk.as_slice(), &sig].concat();
    assert_eq!(data.len(), PQ_PUBKEY_LEN + PQ_SIG_LEN);

    assert_eq!(call(Some((&wallet, true)), &data), Ok(()));

    // The client's tampered proof: bit 0 of byte 100 of the signature.
    let mut tampered = data.clone();
    tampered[PQ_PUBKEY_LEN + 100] ^= 1;
    assert_eq!(call(Some((&wallet, true)), &tampered), Err(ProgramError::InvalidArgument));
    // Every single-byte change of the signature that the loop reaches is refused in the same way.
    for at in (0..PQ_SIG_LEN).step_by(37) {
        let mut tampered = data.clone();
        tampered[PQ_PUBKEY_LEN + at] ^= 0x10;
        assert_eq!(call(Some((&wallet, true)), &tampered), Err(ProgramError::InvalidArgument), "byte {at}");
    }

    // The proof binds the wallet: another signer's address gives another message.
    let other = Pubkey::new_from_array([4; 32]);
    assert_eq!(call(Some((&other, true)), &data), Err(ProgramError::InvalidArgument));

    // Malformed calls.
    assert_eq!(call(Some((&wallet, false)), &data), Err(ProgramError::MissingRequiredSignature));
    assert_eq!(call(None, &data), Err(ProgramError::NotEnoughAccountKeys));
    assert_eq!(call(Some((&wallet, true)), &data[1..]), Err(ProgramError::InvalidInstructionData));
    assert_eq!(
        call(Some((&wallet, true)), &[data.as_slice(), &[0]].concat()),
        Err(ProgramError::InvalidInstructionData)
    );
    assert_eq!(call(Some((&wallet, true)), &[]), Err(ProgramError::InvalidInstructionData));
}
