//! ML-DSA-44 signature verification (FIPS 204) for the Solana virtual machine.
//!
//! [`verify`] is ML-DSA.Verify (FIPS 204, Algorithms 3 and 8) for the parameter set ML-DSA-44, in the pure
//! variant with an empty context string. It needs `core`, `alloc` and the `sha3` crate, and has no unsafe code.
//!
//! Four rules of the virtual machine shape the code:
//!
//! * A function may use 4,096 bytes of stack. Polynomials live on the heap; the stack holds hash states and
//!   buffers of at most 192 bytes.
//! * The heap is 32 KiB and is never freed. One allocation of 7,168 bytes, seven polynomials, is the whole
//!   working memory. The matrix A (16 polynomials) is never stored: each coefficient of A is multiplied into the
//!   running sum as soon as it has been sampled.
//! * Every instruction costs one compute unit, a remainder as much as an addition. Coefficients are therefore
//!   plain residues modulo q (no Montgomery form), held as unsigned integers that may exceed q where the bounds
//!   stated at each function allow it, and brought back with `%` only where a product needs it.
//! * An instruction addresses memory as a register plus a constant. The seven polynomials are therefore stored
//!   coefficient by coefficient ([`Memory`]), so that every polynomial is at a constant distance from a pointer
//!   to one coefficient, and the innermost loops run a constant, small number of times ([`RUN`]).

#![forbid(unsafe_code)]

use alloc::vec;
use sha3::digest::{ExtendableOutput, Update, XofReader};
use sha3::{Shake128, Shake256};

/// Length of a public key: the seed rho, then t1 at 10 bits a coefficient.
pub const PUBLIC_KEY_LEN: usize = RHO_LEN + K * T1_POLY_LEN;
/// Length of a signature: c-tilde, then z at 18 bits a coefficient, then the hint.
pub const SIGNATURE_LEN: usize = C_TILDE_LEN + L * Z_POLY_LEN + HINT_LEN;

// The parameter set ML-DSA-44 (FIPS 204, Table 1). eta = 2 concerns key generation and signing only.
const N: usize = 256;
const Q: u64 = 8_380_417;
const D: u32 = 13;
const TAU: usize = 39;
const LAMBDA: usize = 128;
const GAMMA1: u64 = 1 << 17;
const GAMMA2: u64 = (Q - 1) / 88;
const K: usize = 4;
const L: usize = 4;
const BETA: u64 = 78;
const OMEGA: usize = 80;

const RHO_LEN: usize = 32;
const C_TILDE_LEN: usize = LAMBDA / 4;
const T1_POLY_LEN: usize = N * 10 / 8;
const Z_POLY_LEN: usize = N * 18 / 8;
const W1_POLY_LEN: usize = N * 6 / 8;
const HINT_LEN: usize = OMEGA + K;
const SHAKE128_RATE: usize = 168;
const SHAKE256_RATE: usize = 136;

/// 256^-1 mod q, the factor that completes the inverse transform (FIPS 204, Algorithm 42).
const INV_N: u64 = 8_347_681;

const _: () = assert!(PUBLIC_KEY_LEN == 1312 && SIGNATURE_LEN == 2420 && N as u64 * INV_N % Q == 1);

/// The working memory: seven polynomials of the ring Z_q[X]/(X^256 + 1), or their number-theoretic transforms
/// (NTT). Entry n holds the coefficient of X^n of each polynomial, in the fields below.
type Memory = [[u32; FIELDS]; N];

const FIELDS: usize = L + 3;
/// Fields 0 to L - 1: NTT(z).
const Z: usize = 0;
/// NTT(-c) for the challenge c.
const C: usize = L;
/// The polynomial in work for the current row of the matrix: NTT(t1 * 2^d), then w'_approx.
const T: usize = L + 1;
/// The running sum of the current row of A * NTT(z); zero between rows.
const SUM: usize = L + 2;

/// The number of steps of the innermost loops over coefficients. The compiler writes a loop that runs this
/// constant number of times as that many copies of its body, and each copy finds its coefficients at constant
/// distances from one pointer; a longer loop would compute an address at every step.
const RUN: usize = 16;

/// `ZETAS[k]` is zeta^BitRev8(k) mod q for the root of unity zeta = 1753 (FIPS 204, Appendix B).
static ZETAS: [u32; N] = {
    let mut table = [0u32; N];
    let mut k = 0;
    while k < N {
        let exponent = (k as u8).reverse_bits();
        let mut power = 1u64;
        let mut i = 0;
        while i < exponent {
            power = power * 1753 % Q;
            i += 1;
        }
        table[k] = power as u32;
        k += 1;
    }
    table
};

/// ML-DSA.Verify for ML-DSA-44 with an empty context string: true if `sig` is a valid signature of `message`
/// under the public key `pk`.
pub fn verify(pk: &[u8; PUBLIC_KEY_LEN], message: &[u8], sig: &[u8; SIGNATURE_LEN]) -> bool {
    // pkDecode and sigDecode (FIPS 204, Algorithms 23 and 27): the fields are read where they are.
    let Some((rho, t1_bytes)) = pk.split_first_chunk::<RHO_LEN>() else { return false };
    let Some((c_tilde, rest)) = sig.split_first_chunk::<C_TILDE_LEN>() else { return false };
    let Some((z_bytes, hint)) = rest.split_first_chunk::<{ L * Z_POLY_LEN }>() else { return false };
    let Ok(hint): Result<&[u8; HINT_LEN], _> = hint.try_into() else { return false };
    let (t1_bytes, _) = t1_bytes.as_chunks::<T1_POLY_LEN>();
    let (z_bytes, _) = z_bytes.as_chunks::<Z_POLY_LEN>();

    // A malformed hint rejects the signature.
    let Some(hint_ends) = hint_list_ends(hint) else { return false };

    // The only allocation; it starts as zeros.
    let mut memory = vec![[0u32; FIELDS]; N];
    let Ok(memory): Result<&mut Memory, _> = memory.as_mut_slice().try_into() else { return false };

    // z, with the bound on its infinity norm, then NTT(z).
    for (column, bytes) in z_bytes.iter().enumerate() {
        if !unpack_z(bytes, memory, Z + column) {
            return false;
        }
        ntt(memory, Z + column);
    }

    // tr = H(pk, 64) and the message representative mu = H(tr || M', 64) with M' = 0x00 || 0x00 || M: a zero
    // byte for the pure variant, the length of the empty context string, the message.
    let tr = shake256_64(&[pk]);
    let mu = shake256_64(&[&tr, &[0, 0], message]);

    // NTT(-c) for the challenge c = SampleInBall(c-tilde).
    sample_in_ball_negated(c_tilde, memory);
    ntt(memory, C);

    // w'_approx = NTT^-1(A * NTT(z) - NTT(c) * NTT(t1 * 2^d)) one row at a time, and the hash of
    // mu || w1Encode(UseHint(h, w'_approx)).
    let mut commitment = Shake256::default();
    commitment.update(&mu);
    let mut hints_from = 0;
    for (row, (t1_row, &hints_to)) in t1_bytes.iter().zip(&hint_ends).enumerate() {
        expand_a_mul_add::<0>(rho, row as u8, memory);
        expand_a_mul_add::<1>(rho, row as u8, memory);
        expand_a_mul_add::<2>(rho, row as u8, memory);
        expand_a_mul_add::<3>(rho, row as u8, memory);
        unpack_t1_scaled(t1_row, memory);
        ntt(memory, T);
        add_sum_and_product(memory);
        inv_ntt(memory, T);
        let Some(hints) = hint.get(hints_from..hints_to) else { return false };
        let mut w1 = [0u8; W1_POLY_LEN];
        use_hint_and_pack(memory, hints, &mut w1);
        commitment.update(&w1);
        hints_from = hints_to;
    }
    let mut c_tilde_prime = [0u8; C_TILDE_LEN];
    commitment.finalize_xof().read(&mut c_tilde_prime);
    c_tilde_prime == *c_tilde
}

/// The checks of HintBitUnpack (FIPS 204, Algorithm 21). The first OMEGA bytes of the hint hold K lists of
/// coefficient positions, one list for each polynomial, stored one after the other; byte OMEGA + i holds the
/// offset at which list i ends. Returns the K end offsets, or `None` for a malformed hint: an end offset that
/// goes backwards or beyond OMEGA, a list that is not strictly increasing, or a non-zero byte after the last list.
fn hint_list_ends(hint: &[u8; HINT_LEN]) -> Option<[usize; K]> {
    let (positions, end_bytes) = hint.split_at(OMEGA);
    let mut ends = [0usize; K];
    let mut index = 0usize;
    for (end_byte, end_slot) in end_bytes.iter().zip(ends.iter_mut()) {
        let end = usize::from(*end_byte);
        if end < index || end > OMEGA {
            return None;
        }
        if positions[index..end].windows(2).any(|pair| pair[0] >= pair[1]) {
            return None;
        }
        index = end;
        *end_slot = end;
    }
    if positions[index..].iter().any(|&byte| byte != 0) {
        return None;
    }
    Some(ends)
}

/// BitUnpack of one polynomial of z (FIPS 204, Algorithm 19: 18 bits a coefficient, z = gamma1 - bits) into
/// `field`, together with the check of the infinity norm, |z| < gamma1 - beta. Returns false if a coefficient
/// fails the check. The coefficients are stored as q + z, which lies between q - gamma1 and q + gamma1.
#[inline(never)]
fn unpack_z(bytes: &[u8; Z_POLY_LEN], memory: &mut Memory, field: usize) -> bool {
    const MASK: u64 = (1 << 18) - 1;
    if field >= FIELDS {
        return false;
    }
    let (groups, _) = bytes.as_chunks::<9>();
    let (entries, _) = memory.as_chunks_mut::<4>();
    for (group, entries) in groups.iter().zip(entries) {
        // Four coefficients in nine bytes.
        let [low @ .., high] = group;
        let low = u64::from_le_bytes(*low);
        let values = [low & MASK, (low >> 18) & MASK, (low >> 36) & MASK, (low >> 54) | (u64::from(*high) << 10)];
        for (value, entry) in values.iter().zip(entries) {
            // |gamma1 - value| < gamma1 - beta exactly when beta < value < 2 * gamma1 - beta.
            if value.wrapping_sub(BETA + 1) > 2 * GAMMA1 - 2 * BETA - 2 {
                return false;
            }
            entry[field] = (Q + GAMMA1 - value) as u32;
        }
    }
    true
}

/// SimpleBitUnpack of one polynomial of t1 (FIPS 204, Algorithm 18: 10 bits a coefficient), multiplied by 2^d,
/// into the field T. The largest result is 1023 * 2^13 = q - 1.
#[inline(never)]
fn unpack_t1_scaled(bytes: &[u8; T1_POLY_LEN], memory: &mut Memory) {
    const MASK: u64 = (1 << 10) - 1;
    let (groups, _) = bytes.as_chunks::<5>();
    let (entries, _) = memory.as_chunks_mut::<4>();
    for (group, entries) in groups.iter().zip(entries) {
        let [b0, b1, b2, b3, b4] = *group;
        let bits = u64::from(u32::from_le_bytes([b0, b1, b2, b3])) | (u64::from(b4) << 32);
        let values = [bits & MASK, (bits >> 10) & MASK, (bits >> 20) & MASK, bits >> 30];
        for (value, entry) in values.iter().zip(entries) {
            entry[T] = (value << D) as u32;
        }
    }
}

/// H(parts, 64): SHAKE256 of the concatenation of `parts`, 64 bytes of output.
#[inline(never)]
fn shake256_64(parts: &[&[u8]]) -> [u8; 64] {
    let mut hash = Shake256::default();
    for part in parts {
        hash.update(part);
    }
    let mut output = [0u8; 64];
    hash.finalize_xof().read(&mut output);
    output
}

/// The negated challenge, into the field C, which must hold zeros: -c mod q for c = SampleInBall(c-tilde)
/// (FIPS 204, Algorithm 29), a polynomial with TAU coefficients equal to 1 or q - 1 and all others zero. The
/// caller wants A*z - c*t; with -c it can add.
#[inline(never)]
fn sample_in_ball_negated(c_tilde: &[u8; C_TILDE_LEN], memory: &mut Memory) {
    let mut hash = Shake256::default();
    hash.update(c_tilde);
    let mut xof = hash.finalize_xof();
    let mut block = [0u8; SHAKE256_RATE];
    xof.read(&mut block);
    let [s0, s1, s2, s3, s4, s5, s6, s7, ..] = block;
    let mut signs = u64::from_le_bytes([s0, s1, s2, s3, s4, s5, s6, s7]);
    let mut next = 8;
    for i in N - TAU..N {
        // A byte j <= i, by rejection.
        let j = loop {
            if next == SHAKE256_RATE {
                xof.read(&mut block);
                next = 0;
            }
            let byte = usize::from(block[next]);
            next += 1;
            if byte <= i {
                break byte;
            }
        };
        memory[i][C] = memory[j][C];
        // c_j = (-1)^sign, so -c_j is q - 1 for sign 0 and 1 for sign 1.
        memory[j][C] = if signs & 1 == 0 { (Q - 1) as u32 } else { 1 };
        signs >>= 1;
    }
}

/// Adds A[row][COLUMN] * NTT(z[COLUMN]) to the field SUM, coefficient by coefficient, modulo q. The polynomial
/// A[row][COLUMN] = RejNTTPoly(rho || COLUMN || row) (FIPS 204, Algorithms 30 and 32) is not stored: 23-bit
/// candidates come from SHAKE128, three bytes each, and every candidate below q is the next coefficient.
/// The field of z may hold any 32-bit values; SUM stays below q.
#[inline(never)]
fn expand_a_mul_add<const COLUMN: usize>(rho: &[u8; RHO_LEN], row: u8, memory: &mut Memory) {
    const { assert!(COLUMN < L) };
    let mut hash = Shake128::default();
    hash.update(rho);
    hash.update(&[COLUMN as u8, row]);
    let mut xof = hash.finalize_xof();
    let mut block = [0u8; SHAKE128_RATE];
    let mut entries = memory.iter_mut();
    let Some(mut entry) = entries.next() else { return };
    loop {
        xof.read(&mut block);
        // Eight candidates in 24 bytes, read as three 64-bit words; the top bit of every third byte is dropped.
        for bytes in block.as_chunks::<24>().0 {
            let (words, _) = bytes.as_chunks::<8>();
            let (w0, w1, w2) =
                (u64::from_le_bytes(words[0]), u64::from_le_bytes(words[1]), u64::from_le_bytes(words[2]));
            let candidates =
                [w0, w0 >> 24, (w0 >> 48) | (w1 << 16), w1 >> 8, w1 >> 32, (w1 >> 56) | (w2 << 8), w2 >> 16, w2 >> 40];
            for candidate in candidates {
                let a = candidate & 0x7f_ffff;
                if a < Q {
                    entry[SUM] = ((u64::from(entry[SUM]) + a * u64::from(entry[Z + COLUMN])) % Q) as u32;
                    match entries.next() {
                        Some(next) => entry = next,
                        None => return,
                    }
                }
            }
        }
    }
}

/// T = (SUM + C * T) mod q and SUM = 0, coefficient by coefficient: the row sum of A * NTT(z) plus
/// NTT(-c) * NTT(t1 * 2^d). C and T may hold any 32-bit values; T leaves below q.
#[inline(never)]
fn add_sum_and_product(memory: &mut Memory) {
    for entries in memory.as_chunks_mut::<RUN>().0 {
        for entry in entries {
            entry[T] = ((u64::from(entry[SUM]) + u64::from(entry[C]) * u64::from(entry[T]) % Q) % Q) as u32;
            entry[SUM] = 0;
        }
    }
}

/// NTT (FIPS 204, Algorithm 41) of the polynomial in `field`, in place. Every butterfly adds at most q to its
/// two coefficients, so coefficients that enter below 2q leave below 10q after the eight layers, a 27-bit
/// number; the result is not reduced.
#[inline(never)]
fn ntt(memory: &mut Memory, field: usize) {
    if field >= FIELDS {
        return;
    }
    ntt_layer::<128>(memory, field, &ZETAS[1..2]);
    ntt_layer::<64>(memory, field, &ZETAS[2..4]);
    ntt_layer::<32>(memory, field, &ZETAS[4..8]);
    ntt_layer::<16>(memory, field, &ZETAS[8..16]);
    ntt_layer::<8>(memory, field, &ZETAS[16..32]);
    ntt_layer::<4>(memory, field, &ZETAS[32..64]);
    ntt_layer::<2>(memory, field, &ZETAS[64..128]);
    ntt_layer::<1>(memory, field, &ZETAS[128..256]);
}

/// The layer of the NTT whose butterflies join coefficients `LEN` apart; `zetas` has one entry for each block of
/// `2 * LEN` coefficients. `LEN` is a constant, and the two innermost loops together run [`RUN`] butterflies.
#[inline(always)]
fn ntt_layer<const LEN: usize>(memory: &mut Memory, field: usize, zetas: &[u32]) {
    let (blocks_in_group, pairs_in_run) = layer_shape(LEN);
    let groups = memory.chunks_exact_mut(2 * LEN * blocks_in_group).zip(zetas.chunks_exact(blocks_in_group));
    for (group, zetas) in groups {
        for (block, &zeta) in group.chunks_exact_mut(2 * LEN).zip(zetas) {
            let zeta = u64::from(zeta);
            let (low, high) = block.split_at_mut(LEN);
            for (low, high) in low.chunks_exact_mut(pairs_in_run).zip(high.chunks_exact_mut(pairs_in_run)) {
                for (x, y) in low.iter_mut().zip(high) {
                    let t = zeta * u64::from(y[field]) % Q;
                    let u = u64::from(x[field]);
                    x[field] = (u + t) as u32;
                    // t is below q, so the difference does not wrap.
                    y[field] = (u + Q).wrapping_sub(t) as u32;
                }
            }
        }
    }
}

/// How a layer of a transform splits its work so that its innermost loops run [`RUN`] butterflies: the number
/// of blocks of `2 * len` coefficients that are taken together, and the number of butterflies of one block
/// that are taken together. The layer with a zeta for every butterfly takes half as many, or the compiler
/// would keep its loop over the blocks.
const fn layer_shape(len: usize) -> (usize, usize) {
    if len == 1 {
        (RUN / 2, 1)
    } else if len < RUN {
        (RUN / len, len)
    } else {
        (1, RUN)
    }
}

/// NTT^-1 (FIPS 204, Algorithm 42) of the polynomial in `field` without its last step, the multiplication by
/// 256^-1: the result is 256 times the polynomial. In place. The coefficients must enter below q. In the layer
/// that joins coefficients `LEN` apart they are below `LEN * q`: a sum doubles that bound and a product is
/// reduced below q, so they leave below 256q, which is less than 2^31.
#[inline(never)]
fn inv_ntt(memory: &mut Memory, field: usize) {
    if field >= FIELDS {
        return;
    }
    inv_ntt_layer::<1>(memory, field, &ZETAS[128..256]);
    inv_ntt_layer::<2>(memory, field, &ZETAS[64..128]);
    inv_ntt_layer::<4>(memory, field, &ZETAS[32..64]);
    inv_ntt_layer::<8>(memory, field, &ZETAS[16..32]);
    inv_ntt_layer::<16>(memory, field, &ZETAS[8..16]);
    inv_ntt_layer::<32>(memory, field, &ZETAS[4..8]);
    inv_ntt_layer::<64>(memory, field, &ZETAS[2..4]);
    inv_ntt_layer::<128>(memory, field, &ZETAS[1..2]);
}

/// The layer of NTT^-1 whose butterflies join coefficients `LEN` apart; it takes its `zetas` from the last to
/// the first and negates them. The loops are those of [`ntt_layer`].
#[inline(always)]
fn inv_ntt_layer<const LEN: usize>(memory: &mut Memory, field: usize, zetas: &[u32]) {
    let bound = LEN as u64 * Q;
    let (blocks_in_group, pairs_in_run) = layer_shape(LEN);
    let groups = memory.chunks_exact_mut(2 * LEN * blocks_in_group).zip(zetas.rchunks_exact(blocks_in_group));
    for (group, zetas) in groups {
        for (block, &zeta) in group.chunks_exact_mut(2 * LEN).zip(zetas.iter().rev()) {
            // Every entry of ZETAS is below q.
            let minus_zeta = Q.wrapping_sub(u64::from(zeta));
            let (low, high) = block.split_at_mut(LEN);
            for (low, high) in low.chunks_exact_mut(pairs_in_run).zip(high.chunks_exact_mut(pairs_in_run)) {
                for (x, y) in low.iter_mut().zip(high) {
                    let t = u64::from(x[field]);
                    let v = u64::from(y[field]);
                    x[field] = (t + v) as u32;
                    // v is below the bound, so the difference does not wrap and is below 2 * bound <= 256q,
                    // which is less than 2^31; its product with a number below q is below 2^54.
                    y[field] = (minus_zeta.wrapping_mul((t + bound).wrapping_sub(v)) % Q) as u32;
                }
            }
        }
    }
}

/// HighBits of r with the hint applied: UseHint(hint, r) (FIPS 204, Algorithms 36, 37 and 40) for r below q.
/// Decompose writes r = r1 * 2 * gamma2 + r0 with -gamma2 < r0 <= gamma2, and r1 = 0 in place of r1 = 44.
#[inline(always)]
fn use_hint(r: u64, hint: bool) -> u64 {
    const M: u64 = (Q - 1) / (2 * GAMMA2);
    // 0..=44, where 44 stands for 0.
    let r1 = (r + (GAMMA2 - 1)) / (2 * GAMMA2);
    if !hint {
        r1 % M
    } else if r > r1 * (2 * GAMMA2) {
        // r0 > 0. For r1 = 44 this branch is not taken: r <= q - 1 = 44 * 2 * gamma2, and Decompose makes r0
        // negative.
        (r1 + 1) % M
    } else {
        (r1 + M - 1) % M
    }
}

/// One polynomial of w1Encode(UseHint(h, w'_approx)) (FIPS 204, Algorithms 28 and 40). The field T holds the
/// output of [`inv_ntt`], 256 times w'_approx; `hints` lists, in increasing order, the coefficients whose hint
/// bit is set. Each coefficient of the result has 6 bits.
#[inline(never)]
fn use_hint_and_pack(memory: &Memory, hints: &[u8], packed: &mut [u8; W1_POLY_LEN]) {
    let mut hints = hints.iter();
    // The position of the next coefficient with a hint; N when there is none.
    let mut next_hint = hints.next().map_or(N, |&position| usize::from(position));
    let (groups, _) = memory.as_chunks::<4>();
    let (outputs, _) = packed.as_chunks_mut::<3>();
    for group_index in 0..N / 4 {
        let (group, output) = (&groups[group_index], &mut outputs[group_index]);
        let first = 4 * group_index;
        let mut bits = 0u64;
        if next_hint >= first + 4 {
            // No hint in this group of four coefficients.
            for (i, entry) in group.iter().enumerate() {
                bits |= use_hint(INV_N * u64::from(entry[T]) % Q, false) << (6 * i);
            }
        } else {
            for (i, entry) in group.iter().enumerate() {
                let hint = next_hint == first + i;
                if hint {
                    next_hint = hints.next().map_or(N, |&position| usize::from(position));
                }
                bits |= use_hint(INV_N * u64::from(entry[T]) % Q, hint) << (6 * i);
            }
        }
        *output = [bits as u8, (bits >> 8) as u8, (bits >> 16) as u8];
    }
}

#[cfg(test)]
#[path = "mldsa44_tests.rs"]
mod tests;
