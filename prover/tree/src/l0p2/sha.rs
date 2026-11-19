//! The SHA-512 table of stage S4c: the 24 compressions of the relation's six HMAC-SHA512 evaluations (the
//! master key and five CKDpriv steps), one round per row, 81 rows per compression. The round, message
//! schedule, register-shift, round-0 and finalization constraints are those of S1
//! (`narrow-sha512/src/sha_air.rs`), unchanged. The S1 public binding of every compression's chaining
//! input, block and output is replaced by:
//! - transition links: the inner (outer) key block's output is the next compression's chaining input;
//! - periodic constants: the IV, the master key's ipad and opad blocks, the CKD ipad and opad tails and the
//!   SHA-512 padding words (the program's public part);
//! - since S4e the path shape of spec §16.3 instead of the path: on round 4 of each CKD message block,
//!   where window[0] is word 4 (message bytes 32..39), periodic constants fix the bits of bytes 33..37 that
//!   the shape fixes (all of 44' and 60', the hardened bit of a' set, bits 1..31 of c and the hardened bit
//!   of i clear, the 0x80 after the message); the other index bits are the witness's, so the path is private;
//! - the bits of window[0] (W_t on round t), so every block word is range-checked now that blocks are
//!   private, and so the chain code can be read through the ipad or opad XOR, which is linear in bits;
//! - four buses: `digest` (inner digest to the outer digest block, in this table), `il` (I_L to the key
//!   arithmetic of the field-operation table), `cc` (I_R, the chain code, to the next HMAC's two key
//!   blocks, in this table) and `data` (the CKD message: the parent key or the parent point and the
//!   index, from the field-operation table).
//! The seed is the private message of the master HMAC's inner block. No public values.
//!
//! L5 leaf L0' v2 (2026-10-31): the 123 "periodic" columns below (period `HEIGHT`, so each is a full column) are
//! committed as this table's preprocessed trace; `eval` reads them from `b.preprocessed()` instead of
//! `b.periodic_values()`, row for row the same values. Nothing else in this file changes.
//!
//! A continuation compression's chaining input is the previous output, whose limbs come from carry sums
//! and may be small signed values. They still represent the right word modulo 2^64, and every use of
//! the words held as limbs (d and h at round 0, the finalization sum) is an addition modulo 2^64; the
//! words held as bits force canonical limbs. So no range check is added for them.
use p3_air::WindowAccess;
use p3_field::{Dup, PrimeCharacteristicRing, PrimeField64};
use p3_lookup::{Count, InteractionBuilder, LookupBus};
use p3_matrix::dense::RowMajorMatrix;

pub const ROUNDS: usize = 80;
pub const ROWS_PER_COMPRESSION: usize = ROUNDS + 1;
pub const HMACS: usize = 6;
pub const COMPRESSIONS: usize = 4 * HMACS;
pub const HEIGHT: usize = 2048;

pub const DIGEST: &str = "digest";
pub const IL: &str = "il";
pub const CC: &str = "cc";
pub const DATA: &str = "data";

// Main columns (S1's, then the S4c additions).
pub const A_BITS: usize = 0;
pub const B_BITS: usize = A_BITS + 64;
pub const C_BITS: usize = B_BITS + 64;
pub const E_BITS: usize = C_BITS + 64;
pub const F_BITS: usize = E_BITS + 64;
pub const G_BITS: usize = F_BITS + 64;
pub const D_LIMBS: usize = G_BITS + 64;
pub const H_LIMBS: usize = D_LIMBS + 4;
pub const WIN: usize = H_LIMBS + 4; // window[k] limb j at WIN + 4k + j; window[k] = W_{t+k}
pub const W1_BITS: usize = WIN + 64; // bits of window[1]
pub const W14_BITS: usize = W1_BITS + 64; // bits of window[14]
pub const HIN: usize = W14_BITS + 64; // chaining input, word w limb j at HIN + 4w + j
pub const HOUT: usize = HIN + 32; // chaining output (finalization rows)
pub const CARRY_A: usize = HOUT + 32; // 4 limbs x 3 bits
pub const CARRY_E: usize = CARRY_A + 12;
pub const CARRY_W: usize = CARRY_E + 12;
pub const CARRY_FIN: usize = CARRY_W + 12; // 8 words x 4 limbs x 1 bit
pub const W0_BITS: usize = CARRY_FIN + 32; // bits of window[0] (S4c)
// Main-column copies of periodic values that the buses use (lookups cannot read periodic columns).
pub const H_ID: usize = W0_BITS + 64;
pub const M_DOUT: usize = H_ID + 1;
pub const M_DIN: usize = M_DOUT + 1;
pub const M_IL: usize = M_DIN + 1;
pub const M_CC: usize = M_IL + 1;
pub const M_CCI: usize = M_CC + 1;
pub const M_CCO: usize = M_CCI + 1;
pub const W_IDX: usize = M_CCO + 1;
pub const M_DATA: usize = W_IDX + 1;
pub const WIDTH: usize = M_DATA + 1;

// Periodic columns, period = HEIGHT.
pub const P_K: usize = 0; // 4 limbs of K_t on round rows
pub const P_ROUND: usize = 4; // rounds 0..79
pub const P_SCHED: usize = 5; // rounds 0..78: window shift and schedule recurrence
pub const P_R0: usize = 6; // round 0 of any compression
pub const P_FIN: usize = 7; // finalization row of any compression
pub const P_LINK: usize = 8; // finalization rows of the key blocks: next chaining input = this output
pub const P_IV: usize = 9; // round 0 of the key blocks: chaining input = IV
pub const P_WC: usize = 10; // 64 columns: round 0, constant block limb + 1, or 0 if not constant
pub const P_BC: usize = P_WC + 64; // BC_BITS columns: round 4 of a CKD message block, fixed bit + 1, or 0 (S4e)
pub const P_COPY: usize = P_BC + BC_BITS; // the 9 copied values, in the order H_ID .. M_DATA
pub const NUM_PERIODIC: usize = P_COPY + 9;
/// The bits of word 4 that the path shape constrains: bits 16..56, that is message byte 37 (the 0x80 after
/// the message) and bytes 36..33 (the index, least significant byte first).
pub const BC_FIRST: usize = 16;
pub const BC_BITS: usize = 40;

/// The five-level path shape of spec §16.3, per CKD step: the index bits it fixes (mask) and their values.
/// 44' and 60' are fixed; a' = a + 2^31 has the hardened bit set; c is 0 or 1; i < 2^31.
pub const PATH_SHAPE: [(u32, u32); 5] = [
    (u32::MAX, 44 | 1 << 31),
    (u32::MAX, 60 | 1 << 31),
    (1 << 31, 1 << 31),
    (!1, 0),
    (1 << 31, 0),
];

/// Whether a path has the shape (witness generation and controls only; the AIR checks it bit by bit).
pub fn fits_shape(path: &[u32; 5]) -> bool {
    path.iter().zip(PATH_SHAPE).all(|(&j, (mask, value))| j & mask == value)
}

pub const K: [u64; 80] = [
    0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc, 0x3956c25bf348b538,
    0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118, 0xd807aa98a3030242, 0x12835b0145706fbe,
    0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2, 0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235,
    0xc19bf174cf692694, 0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
    0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5, 0x983e5152ee66dfab,
    0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4, 0xc6e00bf33da88fc2, 0xd5a79147930aa725,
    0x06ca6351e003826f, 0x142929670a0e6e70, 0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed,
    0x53380d139d95b3df, 0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
    0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30, 0xd192e819d6ef5218,
    0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8, 0x19a4c116b8d2d0c8, 0x1e376c085141ab53,
    0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8, 0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373,
    0x682e6ff3d6b2b8a3, 0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
    0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b, 0xca273eceea26619c,
    0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178, 0x06f067aa72176fba, 0x0a637dc5a2c898a6,
    0x113f9804bef90dae, 0x1b710b35131c471b, 0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc,
    0x431d67c49c100d4c, 0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817,
];

pub const IV: [u64; 8] = [
    0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
    0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179,
];
pub const IPAD: u64 = 0x3636363636363636;
pub const OPAD: u64 = 0x5c5c5c5c5c5c5c5c;
pub const MASTER_KEY: &[u8] = b"Bitcoin seed";

/// One SHA-512 compression of the relation, in the order the table holds them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Compression {
    pub hin: [u64; 8],
    pub block: [u64; 16],
    pub hout: [u64; 8],
}

pub fn big_sigma0(x: u64) -> u64 { x.rotate_right(28) ^ x.rotate_right(34) ^ x.rotate_right(39) }
pub fn big_sigma1(x: u64) -> u64 { x.rotate_right(14) ^ x.rotate_right(18) ^ x.rotate_right(41) }
pub fn small_sigma0(x: u64) -> u64 { x.rotate_right(1) ^ x.rotate_right(8) ^ (x >> 7) }
pub fn small_sigma1(x: u64) -> u64 { x.rotate_right(19) ^ x.rotate_right(61) ^ (x >> 6) }

/// Message schedule extended to W_94: row t holds the window W_t ... W_{t+15}.
pub fn schedule(block: &[u64; 16]) -> [u64; 95] {
    let mut w = [0u64; 95];
    w[..16].copy_from_slice(block);
    for t in 16..95 {
        w[t] = small_sigma1(w[t - 2]).wrapping_add(w[t - 7]).wrapping_add(small_sigma0(w[t - 15])).wrapping_add(w[t - 16]);
    }
    w
}

/// Plain SHA-512 compression, the reference for the trace.
pub fn compress(hin: [u64; 8], block: &[u64; 16]) -> [u64; 8] {
    let w = schedule(block);
    let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = hin;
    for t in 0..ROUNDS {
        let t1 = h.wrapping_add(big_sigma1(e)).wrapping_add((e & f) ^ (!e & g)).wrapping_add(K[t]).wrapping_add(w[t]);
        let t2 = big_sigma0(a).wrapping_add((a & b) ^ (a & c) ^ (b & c));
        h = g; g = f; f = e; e = d.wrapping_add(t1); d = c; c = b; b = a; a = t1.wrapping_add(t2);
    }
    let state = [a, b, c, d, e, f, g, h];
    std::array::from_fn(|i| hin[i].wrapping_add(state[i]))
}

pub fn limb(x: u64, j: usize) -> u64 { (x >> (16 * j)) & 0xffff }

fn words(block: &[u8; 128]) -> [u64; 16] {
    std::array::from_fn(|i| u64::from_be_bytes(block[8 * i..8 * i + 8].try_into().unwrap()))
}

pub fn digest_bytes(h: &[u64; 8]) -> [u8; 64] {
    let mut out = [0u8; 64];
    for (i, w) in h.iter().enumerate() { out[8 * i..8 * i + 8].copy_from_slice(&w.to_be_bytes()); }
    out
}

/// One-block message (at most 111 bytes) after a 128-byte key block: SHA-512 padding.
fn message_block(msg: &[u8]) -> [u8; 128] {
    assert!(msg.len() <= 111);
    let mut block = [0u8; 128];
    block[..msg.len()].copy_from_slice(msg);
    block[msg.len()] = 0x80;
    block[112..].copy_from_slice(&(((128 + msg.len()) * 8) as u128).to_be_bytes());
    block
}

/// HMAC-SHA512 as its four compressions (inner key block, inner message block, outer key block,
/// outer digest block). The caller cross-checks the output.
pub fn hmac_compressions(key: &[u8], msg: &[u8]) -> ([u8; 64], [Compression; 4]) {
    assert!(key.len() <= 128);
    let mut ipad = [0x36u8; 128];
    let mut opad = [0x5cu8; 128];
    for (i, &k) in key.iter().enumerate() { ipad[i] ^= k; opad[i] ^= k; }
    let c0 = Compression { hin: IV, block: words(&ipad), hout: compress(IV, &words(&ipad)) };
    let b1 = words(&message_block(msg));
    let c1 = Compression { hin: c0.hout, block: b1, hout: compress(c0.hout, &b1) };
    let c2 = Compression { hin: IV, block: words(&opad), hout: compress(IV, &words(&opad)) };
    let b3 = words(&message_block(&digest_bytes(&c1.hout)));
    let c3 = Compression { hin: c2.hout, block: b3, hout: compress(c2.hout, &b3) };
    (digest_bytes(&c3.hout), [c0, c1, c2, c3])
}

/// The constant limbs of each compression's block, as value + 1 (0 where the limb is a witness): the
/// master key's ipad and opad blocks, the CKD pad tails, the padding words, and in the CKD message blocks
/// the zero bytes 38, 39 and the length. Since S4e no limb depends on the path (see `index_bit_constants`).
pub fn block_constants() -> Vec<[u64; 64]> {
    let mut out = Vec::with_capacity(COMPRESSIONS);
    let set_word = |c: &mut [u64; 64], w: usize, x: u64| for j in 0..4 { c[4 * w + j] = limb(x, j) + 1; };
    for h in 0..HMACS {
        let mut key = [[0u64; 64]; 4];
        if h == 0 {
            let mut ipad = [0x36u8; 128];
            let mut opad = [0x5cu8; 128];
            for (i, &k) in MASTER_KEY.iter().enumerate() { ipad[i] ^= k; opad[i] ^= k; }
            for (w, (&a, &b)) in words(&ipad).iter().zip(words(&opad).iter()).enumerate() {
                set_word(&mut key[0], w, a);
                set_word(&mut key[2], w, b);
            }
            // Inner message block: the 64-byte seed (witness), then padding words 8..15.
            set_word(&mut key[1], 8, 0x8000000000000000);
            for w in 9..15 { set_word(&mut key[1], w, 0); }
            set_word(&mut key[1], 15, (128 + 64) * 8);
        } else {
            for w in 4..16 {
                set_word(&mut key[0], w, IPAD);
                set_word(&mut key[2], w, OPAD);
            }
            // Data block: 37 bytes (prefix, 32 key or x bytes, 4 index bytes), 0x80, zeros, length. Word 4
            // holds bytes 32..39; its limbs 1 and 2 (bytes 34..37) are checked bit by bit on round 4.
            key[1][4 * 4] = 1; // bytes 38, 39 = 0, 0
            for w in 5..15 { set_word(&mut key[1], w, 0); }
            set_word(&mut key[1], 15, (128 + 37) * 8);
        }
        // Outer digest block: the 64-byte inner digest (bus), then padding words 8..15.
        set_word(&mut key[3], 8, 0x8000000000000000);
        for w in 9..15 { set_word(&mut key[3], w, 0); }
        set_word(&mut key[3], 15, (128 + 64) * 8);
        out.extend(key);
    }
    out
}

/// Per CKD step, the bits BC_FIRST.. of word 4 of its message block as value + 1 where the path shape
/// fixes them, 0 where they are the witness's: byte 37 is 0x80; index bit k is word bit 24 + k.
pub fn index_bit_constants() -> [[u64; BC_BITS]; 5] {
    std::array::from_fn(|s| {
        let (mask, value) = PATH_SHAPE[s];
        std::array::from_fn(|i| {
            if i < 8 {
                ((0x80u64 >> i) & 1) + 1
            } else if (mask >> (i - 8)) & 1 == 1 {
                ((value >> (i - 8)) & 1) as u64 + 1
            } else {
                0
            }
        })
    })
}

/// Periodic columns: S1's K limbs and row selectors, then the links, the IV, the constant block limbs,
/// the path shape and the copied bus values. They are public: the transcript absorbs a digest of them
/// (the program). Since S4e they do not depend on the path.
pub fn periodic() -> Vec<Vec<u64>> {
    let mut cols = vec![vec![0u64; HEIGHT]; NUM_PERIODIC];
    let consts = block_constants();
    let shape = index_bit_constants();
    for c in 0..COMPRESSIONS {
        let (h, r) = (c / 4, c % 4);
        let base = c * ROWS_PER_COMPRESSION;
        let fin = base + ROUNDS;
        for t in 0..ROUNDS {
            for j in 0..4 { cols[P_K + j][base + t] = limb(K[t], j); }
            cols[P_ROUND][base + t] = 1;
            if t < ROUNDS - 1 { cols[P_SCHED][base + t] = 1; }
        }
        cols[P_R0][base] = 1;
        cols[P_FIN][fin] = 1;
        if r == 0 || r == 2 {
            cols[P_LINK][fin] = 1;
            cols[P_IV][base] = 1;
        }
        for i in 0..64 { cols[P_WC + i][base] = consts[c][i]; }
        if r == 1 && h > 0 {
            for i in 0..BC_BITS { cols[P_BC + i][base + 4] = shape[h - 1][i]; }
        }
        for row in base..=fin { cols[P_COPY][row] = h as u64; }
        let copy = |k: usize| P_COPY + k - H_ID;
        match r {
            1 => {
                cols[copy(M_DOUT)][fin] = 1;
                if h > 0 { cols[copy(M_DATA)][base] = 1; }
            }
            3 => {
                cols[copy(M_DIN)][base] = 1;
                cols[copy(M_IL)][fin] = 1;
                if h + 1 < HMACS { cols[copy(M_CC)][fin] = 2; }
            }
            _ if h > 0 => {
                for t in 0..4 {
                    cols[if r == 0 { copy(M_CCI) } else { copy(M_CCO) }][base + t] = 1;
                    cols[copy(W_IDX)][base + t] = t as u64;
                }
            }
            _ => {}
        }
    }
    cols
}

/// The trace for the given compressions. `fault` adds one to one cell (row, column) after the honest
/// trace is built, for malicious-prover controls only.
pub fn trace<F: PrimeField64>(comps: &[Compression], periodic: &[Vec<u64>], fault: Option<(usize, usize)>) -> RowMajorMatrix<F> {
    assert_eq!(comps.len(), COMPRESSIONS);
    let mut v = vec![0u64; HEIGHT * WIDTH];
    let set_bits = |row: &mut [u64], base: usize, x: u64| for i in 0..64 { row[base + i] = (x >> i) & 1; };
    let set_limbs = |row: &mut [u64], base: usize, x: u64| for j in 0..4 { row[base + j] = limb(x, j); };
    for (ci, comp) in comps.iter().enumerate() {
        let w = schedule(&comp.block);
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = comp.hin;
        for t in 0..ROWS_PER_COMPRESSION {
            let r = ci * ROWS_PER_COMPRESSION + t;
            let row = &mut v[r * WIDTH..(r + 1) * WIDTH];
            set_bits(row, A_BITS, a); set_bits(row, B_BITS, b); set_bits(row, C_BITS, c);
            set_bits(row, E_BITS, e); set_bits(row, F_BITS, f); set_bits(row, G_BITS, g);
            set_limbs(row, D_LIMBS, d); set_limbs(row, H_LIMBS, h);
            for (wi, &x) in comp.hin.iter().enumerate() { set_limbs(row, HIN + 4 * wi, x); }
            if t == ROUNDS {
                let state = [a, b, c, d, e, f, g, h];
                for wi in 0..8 {
                    let out = comp.hin[wi].wrapping_add(state[wi]);
                    set_limbs(row, HOUT + 4 * wi, out);
                    let mut carry = 0;
                    for j in 0..4 {
                        let s = limb(state[wi], j) + limb(comp.hin[wi], j) + carry;
                        carry = s >> 16;
                        row[CARRY_FIN + 4 * wi + j] = carry;
                    }
                }
                assert_eq!(std::array::from_fn::<u64, 8, _>(|i| limb_join(row, HOUT + 4 * i)), comp.hout);
                break;
            }
            for k in 0..16 { set_limbs(row, WIN + 4 * k, w[t + k]); }
            set_bits(row, W0_BITS, w[t]);
            if t < ROUNDS - 1 {
                set_bits(row, W1_BITS, w[t + 1]);
                set_bits(row, W14_BITS, w[t + 14]);
            }
            let s1 = big_sigma1(e); let ch = (e & f) ^ (!e & g);
            let s0 = big_sigma0(a); let mj = (a & b) ^ (a & c) ^ (b & c);
            let t1 = h.wrapping_add(s1).wrapping_add(ch).wrapping_add(K[t]).wrapping_add(w[t]);
            let t2 = s0.wrapping_add(mj);
            let new_a = t1.wrapping_add(t2);
            let new_e = d.wrapping_add(t1);
            let mut ca = 0; let mut ce = 0; let mut cw = 0;
            for j in 0..4 {
                let sa = limb(h, j) + limb(s1, j) + limb(ch, j) + limb(K[t], j) + limb(w[t], j) + limb(s0, j) + limb(mj, j) + ca;
                ca = sa >> 16;
                let se = limb(d, j) + limb(h, j) + limb(s1, j) + limb(ch, j) + limb(K[t], j) + limb(w[t], j) + ce;
                ce = se >> 16;
                for bit in 0..3 {
                    row[CARRY_A + 3 * j + bit] = (ca >> bit) & 1;
                    row[CARRY_E + 3 * j + bit] = (ce >> bit) & 1;
                }
                if t < ROUNDS - 1 {
                    let sw = limb(small_sigma1(w[t + 14]), j) + limb(w[t + 9], j) + limb(small_sigma0(w[t + 1]), j) + limb(w[t], j) + cw;
                    cw = sw >> 16;
                    for bit in 0..3 { row[CARRY_W + 3 * j + bit] = (cw >> bit) & 1; }
                }
                assert!(ca < 8 && ce < 8 && cw < 8);
            }
            h = g; g = f; f = e; e = new_e; d = c; c = b; b = a; a = new_a;
        }
    }
    for r in 0..HEIGHT {
        for k in 0..9 { v[r * WIDTH + H_ID + k] = periodic[P_COPY + k][r]; }
    }
    if let Some((r, col)) = fault { v[r * WIDTH + col] += 1; }
    RowMajorMatrix::new(v.into_iter().map(F::from_u64).collect(), WIDTH)
}

fn limb_join(row: &[u64], base: usize) -> u64 { (0..4).map(|j| row[base + j] << (16 * j)).sum() }

fn pow2<E: PrimeCharacteristicRing>(k: usize) -> E { E::from_u64(1u64 << k) }

fn pack16<E: PrimeCharacteristicRing>(row: &[E], base: usize, j: usize) -> E
where E: Dup {
    (0..16).fold(E::ZERO, |acc, k| acc + row[base + 16 * j + k].dup() * pow2::<E>(k))
}

fn xor2<E: PrimeCharacteristicRing + Dup>(x: E, y: E) -> E { x.dup() + y.dup() - (x * y).double() }

fn xor3<E: PrimeCharacteristicRing + Dup>(x: E, y: E, z: E) -> E {
    let xy = x.dup() * y.dup();
    let yz = y.dup() * z.dup();
    let zx = z.dup() * x.dup();
    let xyz = xy.dup() * z.dup();
    x + y + z - (xy + yz + zx).double() + xyz * E::from_u64(4)
}

/// Limb j of a bitwise function of 64-bit words held as bits; `f` gets bit index i.
fn limb_of<E: PrimeCharacteristicRing>(j: usize, f: impl Fn(usize) -> E) -> E {
    (0..16).fold(E::ZERO, |acc, k| acc + f(16 * j + k) * pow2::<E>(k))
}

/// The AIR. Its periodic columns come from `periodic(path)` (held by `air::Ag1Air`).
pub fn eval<AB: InteractionBuilder>(b: &mut AB)
where
    AB::F: PrimeField64,
{
    let main = b.main();
    let l: Vec<AB::Expr> = main.current_slice().iter().map(|&v| v.into()).collect();
    let n: Vec<AB::Expr> = main.next_slice().iter().map(|&v| v.into()).collect();
    // L0' v2: the program row from the preprocessed trace (S5 and L0': from the periodic values).
    let per: Vec<AB::Expr> = b.preprocessed().current_slice().iter().map(|&p| p.into()).collect();
    assert_eq!(per.len(), NUM_PERIODIC);
    let e = |c: usize| -> AB::Expr { l[c].dup() };
    let ne = |c: usize| -> AB::Expr { n[c].dup() };
    let bit = |base: usize, i: usize| -> AB::Expr { l[base + i].dup() };
    let rotr = |base: usize, s: usize, i: usize| -> AB::Expr { l[base + (i + s) % 64].dup() };
    let two16 = pow2::<AB::Expr>(16);
    let round = per[P_ROUND].dup();
    let sched = per[P_SCHED].dup();

    // Booleans, on every row.
    for c in (A_BITS..D_LIMBS).chain(W1_BITS..HIN).chain(CARRY_A..W0_BITS + 64) {
        b.assert_bool(l[c].dup());
    }

    // Bitwise round functions, limb j.
    let big_s0 = |j| limb_of(j, |i| xor3(rotr(A_BITS, 28, i), rotr(A_BITS, 34, i), rotr(A_BITS, 39, i)));
    let big_s1 = |j| limb_of(j, |i| xor3(rotr(E_BITS, 14, i), rotr(E_BITS, 18, i), rotr(E_BITS, 41, i)));
    let ch = |j| limb_of(j, |i| {
        let (x, y, z) = (bit(E_BITS, i), bit(F_BITS, i), bit(G_BITS, i));
        x.dup() * y - x * z.dup() + z
    });
    let maj = |j| limb_of(j, |i| {
        let (x, y, z) = (bit(A_BITS, i), bit(B_BITS, i), bit(C_BITS, i));
        let xy = x.dup() * y.dup();
        let xyz = xy.dup() * z.dup();
        xy + x * z.dup() + y * z - xyz.double()
    });
    let small_s0 = |j| limb_of(j, |i| {
        let (x, y) = (rotr(W1_BITS, 1, i), rotr(W1_BITS, 8, i));
        if i + 7 < 64 { xor3(x, y, bit(W1_BITS, i + 7)) } else { xor2(x, y) }
    });
    let small_s1 = |j| limb_of(j, |i| {
        let (x, y) = (rotr(W14_BITS, 19, i), rotr(W14_BITS, 61, i));
        if i + 6 < 64 { xor3(x, y, bit(W14_BITS, i + 6)) } else { xor2(x, y) }
    });
    let carry3 = |base: usize| e(base) + e(base + 1).double() + e(base + 2) * AB::Expr::from_u64(4);
    let win = |k: usize, j: usize| e(WIN + 4 * k + j);

    // New a and new e (rounds), into the next row's bits.
    let mut ca = AB::Expr::ZERO;
    let mut ce = AB::Expr::ZERO;
    for j in 0..4 {
        let t1 = e(H_LIMBS + j) + big_s1(j) + ch(j) + per[P_K + j].dup() + win(0, j);
        let sum_a = t1.dup() + big_s0(j) + maj(j) + ca.dup();
        let out_a = carry3(CARRY_A + 3 * j);
        b.assert_zero(round.dup() * (sum_a - pack16(&n, A_BITS, j) - out_a.dup() * two16.dup()));
        ca = out_a;
        let sum_e = t1 + e(D_LIMBS + j) + ce.dup();
        let out_e = carry3(CARRY_E + 3 * j);
        b.assert_zero(round.dup() * (sum_e - pack16(&n, E_BITS, j) - out_e.dup() * two16.dup()));
        ce = out_e;
    }
    // Register shifts and the constant chaining input (rounds 0..79 into the next row).
    for i in 0..64 {
        b.assert_zero(round.dup() * (ne(B_BITS + i) - e(A_BITS + i)));
        b.assert_zero(round.dup() * (ne(C_BITS + i) - e(B_BITS + i)));
        b.assert_zero(round.dup() * (ne(F_BITS + i) - e(E_BITS + i)));
        b.assert_zero(round.dup() * (ne(G_BITS + i) - e(F_BITS + i)));
    }
    for j in 0..4 {
        b.assert_zero(round.dup() * (ne(D_LIMBS + j) - pack16(&l, C_BITS, j)));
        b.assert_zero(round.dup() * (ne(H_LIMBS + j) - pack16(&l, G_BITS, j)));
    }
    for i in 0..32 {
        b.assert_zero(round.dup() * (ne(HIN + i) - e(HIN + i)));
    }
    // Message schedule (rounds 0..78): shift the window and append W_{t+16}.
    for k in 0..15 {
        for j in 0..4 {
            b.assert_zero(sched.dup() * (ne(WIN + 4 * k + j) - win(k + 1, j)));
        }
    }
    let mut cw = AB::Expr::ZERO;
    for j in 0..4 {
        let sum_w = small_s1(j) + win(9, j) + small_s0(j) + win(0, j) + cw.dup();
        let out_w = carry3(CARRY_W + 3 * j);
        b.assert_zero(sched.dup() * (sum_w - ne(WIN + 60 + j) - out_w.dup() * two16.dup()));
        cw = out_w;
        b.assert_zero(sched.dup() * (pack16(&l, W1_BITS, j) - win(1, j)));
        b.assert_zero(sched.dup() * (pack16(&l, W14_BITS, j) - win(14, j)));
        // S4c: window[0] held as bits on every round row.
        b.assert_zero(round.dup() * (pack16(&l, W0_BITS, j) - win(0, j)));
    }
    // Register value of word w (a..h), limb j.
    let state = |w: usize, j: usize| -> AB::Expr {
        match w {
            0 => pack16(&l, A_BITS, j),
            1 => pack16(&l, B_BITS, j),
            2 => pack16(&l, C_BITS, j),
            3 => e(D_LIMBS + j),
            4 => pack16(&l, E_BITS, j),
            5 => pack16(&l, F_BITS, j),
            6 => pack16(&l, G_BITS, j),
            _ => e(H_LIMBS + j),
        }
    };
    // Round 0: the registers start at the chaining input.
    for w in 0..8 {
        for j in 0..4 {
            b.assert_zero(per[P_R0].dup() * (state(w, j) - e(HIN + 4 * w + j)));
        }
    }
    // Finalization: H_out = H_in + registers (mod 2^64, one carry bit per limb).
    for w in 0..8 {
        let mut c = AB::Expr::ZERO;
        for j in 0..4 {
            let out = e(CARRY_FIN + 4 * w + j);
            b.assert_zero(per[P_FIN].dup() * (state(w, j) + e(HIN + 4 * w + j) + c.dup() - e(HOUT + 4 * w + j) - out.dup() * two16.dup()));
            c = out;
        }
    }

    // S4c. Links: a key block's output is the next compression's chaining input; a key block starts at
    // the IV; the block limbs fixed by the program take their values (P_WC = value + 1, or 0).
    for i in 0..32 {
        b.assert_zero(per[P_LINK].dup() * (ne(HIN + i) - e(HOUT + i)));
        b.assert_zero(per[P_IV].dup() * (e(HIN + i) - AB::Expr::from_u64(limb(IV[i / 4], i % 4))));
    }
    for i in 0..64 {
        let wc = per[P_WC + i].dup();
        b.assert_zero(wc.dup() * (e(WIN + i) + AB::Expr::ONE - wc));
    }
    // S4e. The path shape on round 4 of a CKD message block, where window[0] is word 4 and its bits are
    // window[0]'s bits: the fixed bits of bytes 33..37 take their values (P_BC = bit + 1, or 0).
    for i in 0..BC_BITS {
        let bc = per[P_BC + i].dup();
        b.assert_zero(bc.dup() * (bit(W0_BITS, BC_FIRST + i) + AB::Expr::ONE - bc));
    }
    for k in 0..9 {
        b.assert_zero(e(H_ID + k) - per[P_COPY + k].dup());
    }

    // Buses.
    let hid = e(H_ID);
    // Inner digest (finalization row of the inner message block) to the outer digest block's words 0..7.
    let digest = LookupBus::new(DIGEST);
    digest.table_entry(b, std::iter::once(hid.dup()).chain((0..32).map(|i| e(HOUT + i))).collect::<Vec<_>>(), e(M_DOUT));
    digest.lookup_key(b, std::iter::once(hid.dup()).chain((0..32).map(|i| e(WIN + i))).collect::<Vec<_>>(), Count::bounded(e(M_DIN), 1));
    // I_L (outer digest block's output words 0..3) to the key arithmetic.
    LookupBus::new(IL).table_entry(b, std::iter::once(hid.dup()).chain((0..16).map(|i| e(HOUT + i))).collect::<Vec<_>>(), e(M_IL));
    // I_R, word by word, to the next HMAC's two key blocks, where window[0] on rounds 0..3 is I_R XOR pad.
    let cc = LookupBus::new(CC);
    for w in 0..4 {
        let key: Vec<AB::Expr> = [hid.dup() + AB::Expr::ONE, AB::Expr::from_u64(w as u64)].into_iter()
            .chain((0..4).map(|j| e(HOUT + 16 + 4 * w + j))).collect();
        cc.table_entry(b, key, e(M_CC));
    }
    for (pad, m) in [(IPAD, M_CCI), (OPAD, M_CCO)] {
        let unpadded = |j: usize| limb_of(j, |i| if (pad >> i) & 1 == 1 { AB::Expr::ONE - bit(W0_BITS, i) } else { bit(W0_BITS, i) });
        let key: Vec<AB::Expr> = [hid.dup(), e(W_IDX)].into_iter().chain((0..4).map(unpadded)).collect();
        cc.lookup_key(b, key, Count::bounded(e(m), 1));
    }
    // The CKD message (parent key or point, and the index's first byte), from the field-operation table:
    // window limbs of words 0..3 and limb 3 of word 4, on round 0 of the inner message block.
    let data: Vec<AB::Expr> = std::iter::once(hid).chain(data_limbs().map(|i| e(WIN + i))).collect();
    LookupBus::new(DATA).lookup_key(b, data, Count::bounded(e(M_DATA), 1));
}

/// The window limbs that carry the CKD message from the field-operation table, in bus order.
pub fn data_limbs() -> impl Iterator<Item = usize> { (0..16).chain(std::iter::once(4 * 4 + 3)) }

fn be32(x: &num_bigint::BigUint) -> [u8; 32] {
    let bytes = x.to_bytes_be();
    let mut out = [0u8; 32];
    out[32 - bytes.len()..].copy_from_slice(&bytes);
    out
}

/// The 24 compressions and the six I_L values of a seed and a path (BIP-32: master HMAC keyed by
/// "Bitcoin seed", then CKDpriv). The message format follows the step, as the program lays it out:
/// steps 1..3 hash 0x00 || ser256(k), steps 4 and 5 serP(K). For a path of the shape that is BIP-32's;
/// for another path it is the best-effort witness of a negative control. Witness generation only; the
/// caller cross-checks the I_L values of a path of the shape against the `hmac` crate.
pub fn derive(seed: &[u8; 64], path: &[u32; 5]) -> (Vec<Compression>, Vec<num_bigint::BigUint>) {
    use num_bigint::BigUint;
    let n = crate::program::n();
    let (i, c) = hmac_compressions(MASTER_KEY, seed);
    let mut comps: Vec<Compression> = c.to_vec();
    let mut il = vec![BigUint::from_bytes_be(&i[..32])];
    let mut k = il[0].clone() % &n;
    let mut chain = i[32..].to_vec();
    for (step, &index) in path.iter().enumerate() {
        let mut data = Vec::with_capacity(37);
        if step < 3 {
            data.push(0);
            data.extend(be32(&k));
        } else {
            let (x, y) = crate::program::mul_point(&k);
            data.push(if y.bit(0) { 3 } else { 2 });
            data.extend(be32(&x));
        }
        data.extend(index.to_be_bytes());
        let (i, c) = hmac_compressions(&chain, &data);
        comps.extend(c);
        let l = BigUint::from_bytes_be(&i[..32]);
        k = (&l + &k) % &n;
        il.push(l);
        chain = i[32..].to_vec();
    }
    (comps, il)
}
