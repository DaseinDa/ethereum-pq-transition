//! In-process C ABI for the fixed F candidate. Internal regression, not independent review.
use std::{ffi::{c_char, CString}, panic::{catch_unwind, AssertUnwindSafe}, slice, sync::OnceLock};
use pq_final_verifier::{ErrorClass, TRUSTED_PARAMS, PI_BYTES, MAX_PROOF_BYTES};
use tiny_keccak::{Hasher, Keccak};

const LOCAL_FAULT: i32 = 3;
fn guarded(f: impl FnOnce() -> i32) -> i32 {
    catch_unwind(AssertUnwindSafe(f)).unwrap_or(LOCAL_FAULT)
}
fn hex(x: &[u8]) -> String { x.iter().map(|b| format!("{b:02x}")).collect() }
fn identity() -> CString {
    let mut h=Keccak::v256(); let mut digest=[0;32];
    h.update(include_bytes!("../ALGORITHM.txt")); h.finalize(&mut digest);
    CString::new(serde_json::json!({
        "abi":1,"backend":"l5-f-native-v1","chain_id":13378,"verifier_version":2147483656u32,
        "algorithm_digest":"0x".to_owned()+&hex(&digest),"algorithm_digest_hash":"keccak256",
        "f_vk_digest":"0x".to_owned()+&hex(TRUSTED_PARAMS.f_vk_digest()),
        "b_vk_digest":"0x".to_owned()+&hex(TRUSTED_PARAMS.b_vk_digest()),
        "l0p2_vk_digest":"0x".to_owned()+&hex(TRUSTED_PARAMS.l0p2_vk_digest()),
        "max_proof_bytes":MAX_PROOF_BYTES,"pi_bytes":PI_BYTES,"groth16":false,"dev_mode":false
    }).to_string()).expect("JSON has no NUL")
}

#[unsafe(no_mangle)]
pub extern "C" fn pq_f_identity_v1() -> *const c_char {
    static ID: OnceLock<CString> = OnceLock::new();
    catch_unwind(|| ID.get_or_init(identity).as_ptr()).unwrap_or(std::ptr::null())
}
#[unsafe(no_mangle)]
pub extern "C" fn pq_f_ready_v1() -> i32 {
    guarded(|| match pq_final_verifier::verifier_ready(&TRUSTED_PARAMS) { Ok(_) => 0, Err(_) => LOCAL_FAULT })
}
/// The caller provides readable, immutable buffers for this call. No pointer is retained.
/// Null, empty, oversized and incorrect PI lengths are rejected before dereferencing.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn pq_f_verify_v1(proof: *const u8, proof_len: usize, pi: *const u8, pi_len: usize) -> i32 {
    if proof.is_null() || pi.is_null() || proof_len == 0 || proof_len > MAX_PROOF_BYTES || pi_len != PI_BYTES { return 1; }
    guarded(|| {
        let proof=unsafe { slice::from_raw_parts(proof,proof_len) };
        let pi: &[u8;PI_BYTES]=unsafe { &*(pi as *const [u8;PI_BYTES]) };
        match pq_final_verifier::verify(proof,pi,&TRUSTED_PARAMS) {
            Ok(())=>0,
            Err(e)=>match e.class() { ErrorClass::InvalidInput=>1, ErrorClass::InvalidProof=>2, ErrorClass::LocalFault=>3 }
        }
    })
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn panic_is_local_fault() { assert_eq!(guarded(|| panic!("test")),3); }
    #[test] fn invalid_lengths_and_null_are_safe() {
        unsafe {
            assert_eq!(pq_f_verify_v1(std::ptr::null(),1,std::ptr::null(),198),1);
            let x=[0u8;198];
            assert_eq!(pq_f_verify_v1(x.as_ptr(),MAX_PROOF_BYTES+1,x.as_ptr(),198),1);
            assert_eq!(pq_f_verify_v1(x.as_ptr(),1,x.as_ptr(),197),1);
        }
    }
}
