//! The research instance (public BIP-39 vector, m/44'/60'/7'/1/0): the six I_L values of its master
//! and CKDpriv HMACs, its keys k0..k5, and the three scalars whose points the relation computes (the
//! parents of the two non-hardened CKD steps and the final key). The derivation uses the `hmac` crate
//! and the reference curve code; the address is checked against the research fixture. Witness
//! generation only.
use hmac::{Hmac, Mac};
use num_bigint::BigUint;
use num_traits::Zero;
use sha2::Sha512;
use tiny_keccak::{Hasher, Keccak};

use crate::program::{mul_point, n};

pub const PUBLIC_SEED_HEX: &str = "5eb00bbddcf069084889a8ab9155568165f5c453ccb85e70811aaed6f6da5fc19a5ac40b389cd370d086206dec8aa6c43daea6690f20ad3d8d48b2d2ce9e38e4";
pub const EXPECTED_ADDRESS_HEX: &str = "429663f135228624435091c29d28a5b0e23c15c0";
pub const PATH: [u32; 5] = [44 | 1 << 31, 60 | 1 << 31, 7 | 1 << 31, 1, 0];

fn hmac512(key: &[u8], msg: &[u8]) -> [u8; 64] {
    let mut mac = Hmac::<Sha512>::new_from_slice(key).unwrap();
    mac.update(msg);
    mac.finalize().into_bytes().into()
}

fn be32(x: &BigUint) -> [u8; 32] {
    let bytes = x.to_bytes_be();
    let mut out = [0u8; 32];
    out[32 - bytes.len()..].copy_from_slice(&bytes);
    out
}

/// A derivation: the six I_L values (master HMAC first), the six keys k0..k5 and the address.
pub struct Derivation { pub il: [BigUint; 6], pub keys: [BigUint; 6], pub address: [u8; 20] }

/// The research instance's public BIP-39 seed.
pub fn seed() -> [u8; 64] {
    std::array::from_fn(|i| u8::from_str_radix(&PUBLIC_SEED_HEX[2 * i..2 * i + 2], 16).unwrap())
}

/// The research instance, with its address checked against the fixture.
pub fn derive() -> Derivation {
    let d = derive_with(&seed(), &PATH);
    let address: String = d.address.iter().map(|b| format!("{b:02x}")).collect();
    assert_eq!(address, EXPECTED_ADDRESS_HEX, "derived address differs from the research fixture");
    d
}

/// Any seed and path (controls), with the `hmac` crate and the reference curve code.
pub fn derive_with(seed: &[u8; 64], path: &[u32; 5]) -> Derivation {
    let n = n();
    let i = hmac512(b"Bitcoin seed", seed);
    let mut k = BigUint::from_bytes_be(&i[..32]);
    let mut chain = i[32..].to_vec();
    assert!(!k.is_zero() && k < n);
    let mut ils = vec![k.clone()];
    let mut keys = vec![k.clone()];
    for &index in path {
        let mut data = Vec::with_capacity(37);
        if index >= 1 << 31 {
            data.push(0);
            data.extend(be32(&k));
        } else {
            let (x, y) = mul_point(&k);
            data.push(if y.bit(0) { 3 } else { 2 });
            data.extend(be32(&x));
        }
        data.extend(index.to_be_bytes());
        let i = hmac512(&chain, &data);
        let il = BigUint::from_bytes_be(&i[..32]);
        let child = (&il + &k) % &n;
        assert!(il < n && !child.is_zero());
        ils.push(il);
        k = child;
        chain = i[32..].to_vec();
        keys.push(k.clone());
    }
    let (x, y) = mul_point(&k);
    let mut h = Keccak::v256();
    h.update(&be32(&x));
    h.update(&be32(&y));
    let mut out = [0u8; 32];
    h.finalize(&mut out);
    Derivation { il: ils.try_into().unwrap(), keys: keys.try_into().unwrap(), address: out[12..].try_into().unwrap() }
}
