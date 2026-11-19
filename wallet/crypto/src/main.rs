//! Public synthetic keys only. Standard pure ML-DSA-44 and Ethereum Keccak.
//! Signing is deterministic: `rnd` is the fixed 32 bytes 0x42, which keeps the public test vectors reproducible; a
//! wallet holding real keys would use fresh randomness (hedged signing). Errors never echo request bytes: a malformed
//! request ends the helper with a fixed message and exit status 2.
use fips204::{ml_dsa_44, traits::{KeyGen,SerDes,Signer,Verifier}};
use sha3::{Digest,Keccak256};
use std::io::{self,BufRead};
use std::process::exit;
fn fail(what:&str)->! { eprintln!("pq-test-crypto: {what}"); exit(2) }
fn bytes(s:&str)->Vec<u8> { if s=="-" {vec![]} else {hex::decode(s).unwrap_or_else(|_| fail("malformed hex argument"))} }
fn arg<'a>(a:&[&'a str],i:usize)->&'a str { a.get(i).copied().unwrap_or_else(|| fail("missing argument")) }
fn seed(s:&str)->[u8;32] { bytes(s).try_into().unwrap_or_else(|_| fail("the seed must have 32 bytes")) }
fn main(){
 for line in io::stdin().lock().lines(){
  let line=line.unwrap_or_else(|_| fail("unreadable request"));let a:Vec<_>=line.split_whitespace().collect();
  match arg(&a,0){
   "hash"=>println!("{}",hex::encode(Keccak256::digest(bytes(arg(&a,1))))),
   "pk"=>{let(pk,_)=ml_dsa_44::KG::keygen_from_seed(&seed(arg(&a,1)));println!("{}",hex::encode(pk.into_bytes()));},
   "sign"=>{let(_,sk)=ml_dsa_44::KG::keygen_from_seed(&seed(arg(&a,1)));let sig=sk.try_sign_with_seed(&[0x42;32],&bytes(arg(&a,2)),&bytes(arg(&a,3))).unwrap_or_else(|_| fail("signing failed"));println!("{}",hex::encode(sig));},
   "verify"=>{let pk=bytes(arg(&a,1));let sig=bytes(arg(&a,4));let ok=if pk.len()!=1312||sig.len()!=2420{false}else{ml_dsa_44::PublicKey::try_from_bytes(pk.try_into().unwrap()).map(|p|p.verify(&bytes(arg(&a,2)),&sig.try_into().unwrap(),&bytes(arg(&a,3)))).unwrap_or(false)};println!("{ok}");},
   _=>fail("unsupported command")
  }
 }
}
