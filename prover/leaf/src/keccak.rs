//! The Keccak table of stage S4b: Plonky3's `p3-keccak-air` (0.9.0-rc.1) unchanged, holding the relation's
//! one Keccak-f permutation (Keccak-256 of the 64-byte uncompressed public key x || y, big-endian) in rows
//! 0..24, padded with zero permutations to the 256 rows that the hiding budget needs. The AIR's `export`
//! flag, which it allows only on a final-round row, is set on row 23 alone: the wrapper (air.rs) uses it to
//! pin the block padding, to bind output bytes 12..32 to `legacy_address` in the public `PI_bytes`, and as
//! the multiplicity of the byte-level bus that brings the 64 message bytes (as 32 little-endian byte
//! pairs) from the field-operation table.
use p3_field::PrimeField64;
use p3_keccak_air::{NUM_KECCAK_COLS, NUM_ROUNDS, generate_trace_rows, input_limb, output_limb};
use p3_matrix::{Matrix, dense::RowMajorMatrix};
use tiny_keccak::{Hasher, Keccak};

pub const HEIGHT: usize = 256;
const PERMUTATIONS: usize = 10; // (10 * 24).next_power_of_two() = 256
pub const EXPORT: usize = NUM_ROUNDS; // the `export` column of `KeccakCols`
pub const A_PRIME: usize = NUM_ROUNDS + 1 + 100 + 100 + 320 + 320; // the first A' bit column (controls)
pub const EXPORT_ROW: usize = NUM_ROUNDS - 1;
pub const ADDRESS_BYTES: usize = 20;
pub const MESSAGE_PAIRS: usize = 32;
/// Since S4d the table's public values are the 198 bytes of `PI_bytes` (layout 2, spec §16.3 and §19.2),
/// which the transcript absorbs; the address is read from its `legacy_address` field, bytes 64..84.
pub const PI_BYTES: usize = 198;
pub const ADDRESS_OFFSET: usize = 64;
const VERSION_OFFSET: usize = 125;
/// The research `verifier_version` of this layout (not allocated; spec §20.15 RP1 has no register).
pub const RESEARCH_VERIFIER_VERSION: u32 = 0x8000_0007;

/// The research `PI_bytes`: the layout-2 fixture of 2026-10-27 (chain 13375) with `legacy_address` set to
/// `address`, `migration_nonce` (bytes 84..92) to `nonce` and `verifier_version` to the research value.
pub fn pi_bytes(address: &[u8; ADDRESS_BYTES], nonce: u64) -> [u8; PI_BYTES] {
    let hex = include_str!("../fixtures/pi198.hex").trim();
    let mut pi: [u8; PI_BYTES] = std::array::from_fn(|i| u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).unwrap());
    assert_eq!(&pi[30..32], &13375u16.to_be_bytes(), "the fixture's chain_id");
    pi[ADDRESS_OFFSET..ADDRESS_OFFSET + ADDRESS_BYTES].copy_from_slice(address);
    pi[84..92].copy_from_slice(&nonce.to_be_bytes());
    pi[VERSION_OFFSET..VERSION_OFFSET + 4].copy_from_slice(&RESEARCH_VERIFIER_VERSION.to_be_bytes());
    pi
}

/// Column of preimage limb t (lane t / 4, 16-bit limb t % 4), rate and capacity alike.
pub fn preimage_col(t: usize) -> usize {
    debug_assert!(t < 100);
    NUM_ROUNDS + 1 + t
}

/// The fixed limbs of the block after a 64-byte message: limbs 32..100 (rate tail and capacity).
pub fn padding_limb(t: usize) -> u64 {
    match t { 32 => 0x0001, 67 => 0x8000, _ => 0 }
}

pub fn keccak256(bytes: &[u8]) -> [u8; 32] {
    let mut h = Keccak::v256();
    h.update(bytes);
    let mut out = [0u8; 32];
    h.finalize(&mut out);
    out
}

pub fn address(message: &[u8; 64]) -> [u8; ADDRESS_BYTES] { keccak256(message)[12..].try_into().unwrap() }

fn padded_state(m: &[u8; 64]) -> [u64; 25] {
    let mut block = [0u8; 136];
    block[..64].copy_from_slice(m);
    block[64] = 0x01;
    block[135] |= 0x80;
    std::array::from_fn(|i| if i < 17 { u64::from_le_bytes(block[8 * i..8 * i + 8].try_into().unwrap()) } else { 0 })
}

/// The trace for `message`, with export on row 23; the layout and the digest are checked against the
/// AIR's own column map and Keccak-256. `fault` adds one to one cell (malicious-prover controls).
pub fn trace<F: PrimeField64>(message: &[u8; 64], fault: Option<(usize, usize)>) -> RowMajorMatrix<F> {
    let mut inputs = vec![[0u64; 25]; PERMUTATIONS];
    inputs[0] = padded_state(message);
    let mut t = generate_trace_rows::<F>(inputs, 0);
    assert_eq!((t.height(), t.width()), (HEIGHT, NUM_KECCAK_COLS));
    t.values[EXPORT_ROW * NUM_KECCAK_COLS + EXPORT] = F::ONE;
    let digest = keccak256(message);
    for i in 0..68 { assert_eq!(input_limb(i), preimage_col(i), "preimage layout"); }
    for i in 0..16 {
        let v = t.values[EXPORT_ROW * NUM_KECCAK_COLS + output_limb(i)].as_canonical_u64();
        assert_eq!(v, u16::from_le_bytes([digest[2 * i], digest[2 * i + 1]]) as u64, "trace output differs from Keccak-256");
    }
    for i in 0..MESSAGE_PAIRS {
        let v = t.values[EXPORT_ROW * NUM_KECCAK_COLS + preimage_col(i)].as_canonical_u64();
        assert_eq!(v, u16::from_le_bytes([message[2 * i], message[2 * i + 1]]) as u64, "preimage differs from the message");
    }
    if let Some((r, c)) = fault { t.values[r * NUM_KECCAK_COLS + c] += F::ONE; }
    t
}
