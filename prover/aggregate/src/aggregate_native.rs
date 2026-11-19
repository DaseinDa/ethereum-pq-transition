//! Native option-C boundary: verify C, then recompute F's periodic advice.
//! The submitter cannot supply a key, change N, or select weaker parameters.
use std::sync::OnceLock;
use std::panic::{catch_unwind, AssertUnwindSafe};
use p3_air::BaseAir;
use p3_challenger::CanObserve;
use p3_commit::{Pcs, PeriodicColumns, PolynomialSpace};
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing, PrimeField32};
use p3_koala_bear::{KoalaBear as F, default_koalabear_poseidon2_16};
use p3_symmetric::CryptographicHasher;
use p3_batch_stark_c3np::{StarkGenericConfig, NextRowColumns, OmittedFill};
use serde_json::Value;
use sha2::{Sha256, Digest};
use crate::{childpin, fkernel, material};
use childpin::key::{EF, FConfig, FProof, FCommon, FHPcs, Challenger, Hash};

pub const MAX_CARRIER: usize = 196608;
pub const BASE_LEN: usize = 6+4*198;
pub const AUX_LEN: usize = 4*64;
const HEADER: [u8;6] = [0,4,0x80,0,0,8];
const DOMAIN: &str = "PQ-MIGRATE-RESEARCH-L5-C-v1";
include!("aggregate-key/pins.rs");
const KEY_JSON: &[u8]=include_bytes!("aggregate-key/c-material.json");
const PERIODIC: &[u8]=include_bytes!("aggregate-key/c-periodic.rle");

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyError { InvalidInput(&'static str), InvalidProof(&'static str), LocalFault(&'static str) }
impl std::fmt::Display for VerifyError {
    fn fmt(&self,f:&mut std::fmt::Formatter<'_>)->std::fmt::Result { write!(f,"{self:?}") }
}
impl std::error::Error for VerifyError {}

/// Private fields and a sole constant instance; callers cannot select another verifying key.
pub struct TrustedParams { _fixed: () }
pub const TRUSTED_PARAMS: TrustedParams = TrustedParams { _fixed: () };
struct Key { air:fkernel::KernelAir, common:FCommon, opened:NextRowColumns, vk:[u8;32] }

fn config(vk:&[u8;32],pv:&[F])->FConfig {
    // Reuse the exact pinned F PCS parameters (no Groth16; OS entropy is never read by verification).
    let pcs=childpin::key::pcs(childpin::key::TRUSTED_PARAMS.fri());
    let mut c=Challenger::new(default_koalabear_poseidon2_16());
    for bytes in [DOMAIN.as_bytes(),&vk[..]] { c.observe(F::from_usize(bytes.len())); for &b in bytes { c.observe(F::from_u8(b)); } }
    c.observe(F::from_usize(pv.len())); for &v in pv { c.observe(v); }
    p3_uni_stark::StarkConfig::new(pcs,c)
}

fn build()->Result<Key,VerifyError> {
    let fault=||VerifyError::LocalFault("pinned aggregate key mismatch");
    let hash=|b:&[u8]|material::hex(&Sha256::digest(b));
    if hash(KEY_JSON)!=KEY_SHA256 || hash(PERIODIC)!=PERIODIC_SHA256 || hash(include_bytes!("fkernel.rs"))!=KERNEL_SHA256 { return Err(fault()); }
    let doc:Value=serde_json::from_slice(KEY_JSON).map_err(|_|fault())?;
    if doc["schema"]!="pq-aggregate-verifier/key/v1" || doc["domain"]!=DOMAIN || doc["vk"]!=C_VK_HEX {return Err(fault());}
    if doc["input_f_vk"]!=material::hex(childpin::key::TRUSTED_PARAMS.f_vk_digest()) {return Err(fault());}
    let a=&doc["air"];
    let columns=material::num(&a["periodic"],"columns").map_err(|_|fault())?;
    let cols=material::decode_periodic(PERIODIC,columns,1<<14).map_err(|_|fault())?;
    let air=material::air_from_material(a,cols).map_err(|_|fault())?;
    if air.log_n!=14 || air.num_public!=BASE_LEN+16*4 {return Err(fault());}
    let vk=material::digest32(&doc,"vk").map_err(|_|fault())?;
    let cfg=config(&vk,&[]);
    let common=p3_batch_stark_c3np::ProverData::from_airs_and_degrees(&cfg,std::slice::from_ref(&air),&[15]).map_err(|_|fault())?.common;
    let opened=material::next_rows_from_json(&doc["next"]).map_err(|_|fault())?;
    let derived=p3_batch_stark_c3np::next_row_columns_for_batch(std::iter::once(&air),&common);
    if material::opened_from_derived(&derived[0],29,8,8)!=opened {return Err(fault());}
    childpin::key::verifier_key(&childpin::key::TRUSTED_PARAMS).map_err(|_|fault())?;
    Ok(Key{air,common,opened,vk})
}
fn key()->Result<&'static Key,VerifyError> {
    static K:OnceLock<Result<Key,VerifyError>>=OnceLock::new();
    K.get_or_init(||catch_unwind(AssertUnwindSafe(build)).unwrap_or(Err(VerifyError::LocalFault("key construction panicked")))).as_ref().map_err(Clone::clone)
}

pub fn periodic(zeta:EF)->Result<Vec<EF>,VerifyError> {
    crate::sparse_periodic::evaluate(zeta)
}
pub fn advice_digest(p:&[EF])->[F;8] {
    Hash::new(default_koalabear_poseidon2_16()).hash_iter(p.iter().flat_map(|v|v.as_basis_coefficients_slice().iter().copied()))
}
fn public_values(base:&[u8],aux:&[u8])->Result<Vec<F>,VerifyError> {
    let bad=VerifyError::InvalidInput("N/version/PI-list encoding");
    if base.len()!=BASE_LEN || base[..6]!=HEADER || aux.len()!=AUX_LEN {return Err(bad);}
    for pi in base[6..].chunks_exact(198) {
        let p=childpin::pi::Pi198::decode(pi.try_into().unwrap());
        p.check_canonical().map_err(|_|VerifyError::InvalidInput("noncanonical PI198"))?;
        if p.verifier_version!=u32::from_be_bytes(HEADER[2..].try_into().unwrap()) {return Err(bad);}
    }
    let mut pv:Vec<F>=base.iter().copied().map(F::from_u8).collect();
    for word in aux.chunks_exact(4) {
        let n=u32::from_le_bytes(word.try_into().unwrap());
        if n>=F::ORDER_U32 {return Err(VerifyError::InvalidInput("noncanonical auxiliary field"));}
        pv.push(F::from_u32(n));
    }
    Ok(pv)
}
pub fn check_periodic(pv:&[F])->Result<(),VerifyError> {
    if pv.len()!=BASE_LEN+64 {return Err(VerifyError::InvalidInput("public fields length"));}
    for a in pv[BASE_LEN..].chunks_exact(16) {
        let zeta=EF::from_basis_coefficients_slice(&a[..8]).ok_or(VerifyError::InvalidInput("zeta width"))?;
        if advice_digest(&periodic(zeta)?)!=a[8..] {return Err(VerifyError::InvalidProof("periodic advice digest mismatch"));}
    }
    Ok(())
}
fn verify_inner(carrier:&[u8],base:&[u8],k:&Key)->Result<(),VerifyError> {
    if carrier.len()<=AUX_LEN || carrier.len()>MAX_CARRIER {return Err(VerifyError::InvalidInput("carrier size"));}
    let pv=public_values(base,&carrier[..AUX_LEN])?;
    let bytes=&carrier[AUX_LEN..];
    let (p,rest):(FProof,_)=postcard::take_from_bytes(bytes).map_err(|_|VerifyError::InvalidInput("proof decoding"))?;
    if !rest.is_empty() || postcard::to_allocvec(&p).map_err(|_|VerifyError::LocalFault("proof encoding"))?!=bytes {return Err(VerifyError::InvalidInput("noncanonical proof encoding"));}
    if p.degree_bits!=[15] {return Err(VerifyError::InvalidInput("proof parameters"));}
    p3_batch_stark_c3np::verify_batch_with_next_row_columns(&config(&k.vk,&pv),std::slice::from_ref(&k.air),&p,&[pv.clone()],&k.common,
        std::slice::from_ref(&k.opened),OmittedFill::Zero).map_err(|_|VerifyError::InvalidProof("outer STARK"))?;
    check_periodic(&pv)
}
pub fn verify(carrier:&[u8],expected_statement:&[u8],_:&TrustedParams)->Result<(),VerifyError> {
    let k=key()?;
    catch_unwind(AssertUnwindSafe(||verify_inner(carrier,expected_statement,k)))
        .unwrap_or(Err(VerifyError::InvalidInput("malformed proof caused verifier panic")))
}

/// 0 accepted; 1 invalid input; 2 invalid proof; 3 local fault. Never reads a caller-supplied verifier key.
/// # Safety
/// Non-null pointers must reference readable buffers of exactly the supplied lengths for the call duration.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn pq_aggregate_verify(proof:*const u8,proof_len:usize,statement:*const u8,statement_len:usize)->i32 {
    if proof.is_null()||statement.is_null()||proof_len>MAX_CARRIER||statement_len!=BASE_LEN {return 1;}
    let result=catch_unwind(AssertUnwindSafe(|| {
        let p=unsafe{std::slice::from_raw_parts(proof,proof_len)};
        let s=unsafe{std::slice::from_raw_parts(statement,statement_len)};
        verify(p,s,&TRUSTED_PARAMS)
    }));
    match result {Ok(Ok(()))=>0,Ok(Err(VerifyError::InvalidInput(_)))=>1,Ok(Err(VerifyError::InvalidProof(_)))=>2,_=>3}
}

#[unsafe(no_mangle)]
pub extern "C" fn pq_aggregate_ready_v1()->i32 {
    match catch_unwind(AssertUnwindSafe(|| {key()?; periodic(EF::ONE)?; Ok::<(),VerifyError>(())})) { Ok(Ok(()))=>0, _=>3 }
}
#[unsafe(no_mangle)]
pub extern "C" fn pq_aggregate_key_v1()->*const std::ffi::c_char {
    static ID:OnceLock<std::ffi::CString>=OnceLock::new();
    ID.get_or_init(||std::ffi::CString::new(C_VK_HEX).expect("fixed hex key")).as_ptr()
}
