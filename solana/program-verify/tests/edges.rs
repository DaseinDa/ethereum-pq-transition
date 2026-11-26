//! Edge cases: `mldsa44::verify` against the `fips204` crate and against
//! a transcription of FIPS 204 written for this file alone (it shares no code with `src/mldsa44.rs`).
//!
//! The tests of `differential.rs` change signatures that a correct signer made, so a changed input fails the
//! last comparison whatever the other checks do. The cases here are built so that one check alone decides:
//!
//! * A public key whose t1 is zero makes w'_approx = A*z, whatever the challenge is. For such a key anyone can
//!   write a signature with any z and any hint h: c-tilde = H(mu || w1Encode(UseHint(h, A*z))). FIPS 204
//!   accepts it exactly when the infinity norm of z is below gamma1 - beta and the hint is well formed (the
//!   standard does not validate public keys, and neither verifier may). This gives z at and next to the bound,
//!   hints of every shape, malformed hints together with the c-tilde that a decoder without the checks of
//!   HintBitUnpack would compute, and coefficients of A*z placed on the special residues of Decompose and
//!   UseHint.
//! * Private keys written by hand (s1 = 0 and others) give signatures of the fips204 signer for public keys
//!   whose t1 is all zeros, 1023 in every coefficient, or a pattern of both.
//! * Other message formats: a context string, the pre-hash variant, a missing or an added prefix byte.
//!
//! Every answer must be the same from `mldsa44::verify`, from fips204 and from the transcription. Generators
//! have fixed seeds.

use std::collections::BTreeMap;
use std::sync::OnceLock;

use fips204::ml_dsa_44;
use fips204::traits::{KeyGen as _, SerDes as _, Signer as _, Verifier as _};
use pq_verify_in_vm::{mldsa44, process_instruction, LABEL};
use sha3::digest::{ExtendableOutput, Update, XofReader};
use sha3::{Shake128, Shake256};
use solana_program::{account_info::AccountInfo, program_error::ProgramError, pubkey::Pubkey};

// ML-DSA-44 (FIPS 204, Table 1).
const Q: i64 = 8_380_417;
const N: usize = 256;
const K: usize = 4;
const L: usize = 4;
const D: u32 = 13;
const TAU: usize = 39;
const GAMMA1: i64 = 1 << 17;
const GAMMA2: i64 = (Q - 1) / 88;
const BETA: i64 = 78;
const OMEGA: usize = 80;

const PK_LEN: usize = 1312;
const SK_LEN: usize = 2560;
const SIG_LEN: usize = 2420;
const Z_START: usize = 32;
const HINT_START: usize = 32 + L * 576;
const HINT_LEN: usize = OMEGA + K;

const SEED: u64 = 0x2026_1126_c0de_0000;

type Poly = [i64; N];
type Hint = [[bool; N]; K];

/// SplitMix64, a deterministic generator.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    /// A value from `low` to `high`, both included.
    fn range(&mut self, low: i64, high: i64) -> i64 {
        low + (self.next() % (high - low + 1) as u64) as i64
    }

    fn bytes(&mut self, len: usize) -> Vec<u8> {
        (0..len).map(|_| self.next() as u8).collect()
    }

    fn array<const M: usize>(&mut self) -> [u8; M] {
        core::array::from_fn(|_| self.next() as u8)
    }
}

// ---------------------------------------------------------------------------------------------------------
// FIPS 204, transcribed. Coefficients are integers from 0 to q - 1 unless a comment says otherwise.
// ---------------------------------------------------------------------------------------------------------

/// H(parts, out.len()): SHAKE256.
fn h256(parts: &[&[u8]], out: &mut [u8]) {
    let mut hash = Shake256::default();
    for part in parts {
        hash.update(part);
    }
    hash.finalize_xof().read(out);
}

fn h256_64(parts: &[&[u8]]) -> [u8; 64] {
    let mut out = [0u8; 64];
    h256(parts, &mut out);
    out
}

fn pow_mod(base: i64, mut exponent: u64) -> i64 {
    let mut base = base.rem_euclid(Q);
    let mut result = 1;
    while exponent > 0 {
        if exponent & 1 == 1 {
            result = result * base % Q;
        }
        base = base * base % Q;
        exponent >>= 1;
    }
    result
}

/// zetas[k] = 1753^BitRev8(k) mod q (FIPS 204, Appendix B).
fn zetas() -> &'static [i64; N] {
    static TABLE: OnceLock<[i64; N]> = OnceLock::new();
    TABLE.get_or_init(|| core::array::from_fn(|k| pow_mod(1753, u64::from((k as u8).reverse_bits()))))
}

/// Algorithm 41, NTT.
fn ntt(w: &Poly) -> Poly {
    let zetas = zetas();
    let mut w_hat = *w;
    let mut m = 0;
    let mut len = 128;
    while len >= 1 {
        let mut start = 0;
        while start < 256 {
            m += 1;
            let z = zetas[m];
            for j in start..start + len {
                let t = z * w_hat[j + len] % Q;
                w_hat[j + len] = (w_hat[j] - t).rem_euclid(Q);
                w_hat[j] = (w_hat[j] + t) % Q;
            }
            start += 2 * len;
        }
        len /= 2;
    }
    w_hat
}

/// Algorithm 42, the inverse of NTT.
fn inv_ntt(w_hat: &Poly) -> Poly {
    let zetas = zetas();
    let mut w = *w_hat;
    let mut m = 256;
    let mut len = 1;
    while len < 256 {
        let mut start = 0;
        while start < 256 {
            m -= 1;
            let z = Q - zetas[m];
            for j in start..start + len {
                let t = w[j];
                w[j] = (t + w[j + len]) % Q;
                w[j + len] = (t - w[j + len]).rem_euclid(Q);
                w[j + len] = z * w[j + len] % Q;
            }
            start += 2 * len;
        }
        len *= 2;
    }
    let f = 8_347_681;
    for coefficient in w.iter_mut() {
        *coefficient = f * *coefficient % Q;
    }
    w
}

/// Algorithm 32, ExpandA, with Algorithm 30 (RejNTTPoly) and Algorithm 14 (CoeffFromThreeBytes). Entry [r][s]
/// of the matrix is at index r * L + s.
fn expand_a(rho: &[u8; 32]) -> Vec<Poly> {
    let mut matrix = Vec::with_capacity(K * L);
    for r in 0..K {
        for s in 0..L {
            let mut g = Shake128::default();
            g.update(rho);
            g.update(&[s as u8]);
            g.update(&[r as u8]);
            let mut xof = g.finalize_xof();
            let mut a_hat = [0i64; N];
            let mut j = 0;
            while j < N {
                let mut b = [0u8; 3];
                xof.read(&mut b);
                let mut b2 = i64::from(b[2]);
                if b2 > 127 {
                    b2 -= 128;
                }
                let z = 65_536 * b2 + 256 * i64::from(b[1]) + i64::from(b[0]);
                if z < Q {
                    a_hat[j] = z;
                    j += 1;
                }
            }
            matrix.push(a_hat);
        }
    }
    matrix
}

/// Algorithm 29, SampleInBall: one byte at a time.
fn sample_in_ball(rho: &[u8]) -> Poly {
    let mut c = [0i64; N];
    let mut ctx = Shake256::default();
    ctx.update(rho);
    let mut xof = ctx.finalize_xof();
    let mut s = [0u8; 8];
    xof.read(&mut s);
    // h = BytesToBits(s)
    let h: Vec<u8> = s.iter().flat_map(|&byte| (0..8).map(move |i| (byte >> i) & 1)).collect();
    for i in 256 - TAU..256 {
        let mut j = [0u8; 1];
        xof.read(&mut j);
        while usize::from(j[0]) > i {
            xof.read(&mut j);
        }
        let j = usize::from(j[0]);
        c[i] = c[j];
        c[j] = if h[i + TAU - 256] == 0 { 1 } else { Q - 1 };
    }
    c
}

/// x mod+- alpha for an even alpha: the representative above -alpha/2 and at most alpha/2.
fn mod_pm(x: i64, alpha: i64) -> i64 {
    let r = x.rem_euclid(alpha);
    if r > alpha / 2 {
        r - alpha
    } else {
        r
    }
}

/// Algorithm 35, Power2Round.
fn power2round(r: i64) -> (i64, i64) {
    let r_plus = r.rem_euclid(Q);
    let r0 = mod_pm(r_plus, 1 << D);
    ((r_plus - r0) >> D, r0)
}

/// Algorithm 36, Decompose.
fn decompose(r: i64) -> (i64, i64) {
    let r_plus = r.rem_euclid(Q);
    let mut r0 = mod_pm(r_plus, 2 * GAMMA2);
    let r1;
    if r_plus - r0 == Q - 1 {
        r1 = 0;
        r0 -= 1;
    } else {
        r1 = (r_plus - r0) / (2 * GAMMA2);
    }
    (r1, r0)
}

/// Algorithm 40, UseHint.
fn use_hint(h: bool, r: i64) -> i64 {
    let m = (Q - 1) / (2 * GAMMA2);
    let (r1, r0) = decompose(r);
    if h && r0 > 0 {
        return (r1 + 1).rem_euclid(m);
    }
    if h && r0 <= 0 {
        return (r1 - 1).rem_euclid(m);
    }
    r1
}

/// IntegerToBits on `width` bits for every value, then BitsToBytes (Algorithms 9 and 12).
fn pack_bits(values: &[i64], width: usize) -> Vec<u8> {
    let mut bits = Vec::with_capacity(values.len() * width);
    for &value in values {
        assert!((0..1i64 << width).contains(&value), "{value} does not fit {width} bits");
        for i in 0..width {
            bits.push(((value >> i) & 1) as u8);
        }
    }
    assert_eq!(bits.len() % 8, 0);
    bits.chunks(8).map(|byte| byte.iter().enumerate().fold(0u8, |sum, (i, &bit)| sum | (bit << i))).collect()
}

/// BytesToBits, then BitsToInteger on fields of `width` bits (Algorithms 13 and 10).
fn unpack_bits(bytes: &[u8], width: usize) -> Vec<i64> {
    let bits: Vec<i64> = bytes.iter().flat_map(|&byte| (0..8).map(move |i| i64::from((byte >> i) & 1))).collect();
    assert_eq!(bits.len() % width, 0);
    bits.chunks(width).map(|field| field.iter().enumerate().fold(0i64, |sum, (i, &bit)| sum | (bit << i))).collect()
}

/// BitPack(z[i], gamma1 - 1, gamma1) for the four polynomials of z (Algorithm 17): gamma1 - z on 18 bits.
/// The coefficients are signed here, from -gamma1 + 1 to gamma1.
fn pack_z(z: &[Poly; L]) -> Vec<u8> {
    let values: Vec<i64> = z.iter().flatten().map(|&coefficient| GAMMA1 - coefficient).collect();
    pack_bits(&values, 18)
}

/// BitUnpack of the four polynomials of z (Algorithm 19), signed coefficients.
fn unpack_z(sig: &[u8; SIG_LEN]) -> [Poly; L] {
    let values = unpack_bits(&sig[Z_START..HINT_START], 18);
    core::array::from_fn(|s| core::array::from_fn(|n| GAMMA1 - values[s * N + n]))
}

/// Algorithm 20, HintBitPack.
fn hint_bit_pack(h: &Hint) -> [u8; HINT_LEN] {
    assert!(h.iter().flatten().filter(|&&bit| bit).count() <= OMEGA);
    let mut y = [0u8; HINT_LEN];
    let mut index = 0;
    for i in 0..K {
        for j in 0..N {
            if h[i][j] {
                y[index] = j as u8;
                index += 1;
            }
        }
        y[OMEGA + i] = index as u8;
    }
    y
}

/// Algorithm 21, HintBitUnpack.
fn hint_bit_unpack(y: &[u8]) -> Option<Hint> {
    assert_eq!(y.len(), HINT_LEN);
    let mut h = [[false; N]; K];
    let mut index = 0usize;
    for i in 0..K {
        if usize::from(y[OMEGA + i]) < index || usize::from(y[OMEGA + i]) > OMEGA {
            return None;
        }
        let first = index;
        while index < usize::from(y[OMEGA + i]) {
            if index > first {
                if y[index - 1] >= y[index] {
                    return None;
                }
            }
            h[i][usize::from(y[index])] = true;
            index += 1;
        }
    }
    for i in index..OMEGA {
        if y[i] != 0 {
            return None;
        }
    }
    Some(h)
}

/// NTT^-1(A-hat o NTT(z)): the product A*z. The coefficients of z are signed.
fn a_times(a_hat: &[Poly], z: &[Poly; L]) -> [Poly; K] {
    let z_hat: Vec<Poly> = z.iter().map(|poly| ntt(&poly.map(|coefficient| coefficient.rem_euclid(Q)))).collect();
    core::array::from_fn(|r| {
        let mut sum = [0i64; N];
        for s in 0..L {
            for n in 0..N {
                sum[n] = (sum[n] + a_hat[r * L + s][n] * z_hat[s][n]) % Q;
            }
        }
        inv_ntt(&sum)
    })
}

/// c-tilde' = H(mu || w1Encode(UseHint(h, w)), 32) (Algorithm 8, steps 10 and 12; Algorithm 28).
fn commitment(mu: &[u8; 64], w: &[Poly; K], h: &Hint) -> [u8; 32] {
    let mut w1 = Vec::with_capacity(K * N);
    for i in 0..K {
        for n in 0..N {
            w1.push(use_hint(h[i][n], w[i][n]));
        }
    }
    let mut c_tilde = [0u8; 32];
    h256(&[mu, &pack_bits(&w1, 6)], &mut c_tilde);
    c_tilde
}

/// mu = H(tr || M', 64) for the pure variant with an empty context string: M' = 0x00 || 0x00 || M.
fn mu_pure(tr: &[u8; 64], message: &[u8]) -> [u8; 64] {
    h256_64(&[tr, &[0, 0], message])
}

/// Algorithms 3 and 8, ML-DSA.Verify with an empty context string.
fn spec_verify(pk: &[u8; PK_LEN], message: &[u8], sig: &[u8; SIG_LEN]) -> bool {
    // pkDecode, sigDecode
    let rho: [u8; 32] = pk[..32].try_into().unwrap();
    let t1 = unpack_bits(&pk[32..], 10);
    let c_tilde: [u8; 32] = sig[..32].try_into().unwrap();
    let z = unpack_z(sig);
    let Some(h) = hint_bit_unpack(&sig[HINT_START..]) else { return false };

    let a_hat = expand_a(&rho);
    let tr = h256_64(&[pk]);
    let mu = mu_pure(&tr, message);
    let c_hat = ntt(&sample_in_ball(&c_tilde));
    let z_hat: Vec<Poly> = z.iter().map(|poly| ntt(&poly.map(|coefficient| coefficient.rem_euclid(Q)))).collect();
    // w'_approx = NTT^-1(A-hat o NTT(z) - NTT(c) o NTT(t1 * 2^d))
    let w_approx: [Poly; K] = core::array::from_fn(|r| {
        let t_hat = ntt(&core::array::from_fn(|n| (t1[r * N + n] << D) % Q));
        let mut sum = [0i64; N];
        for n in 0..N {
            for s in 0..L {
                sum[n] = (sum[n] + a_hat[r * L + s][n] * z_hat[s][n]) % Q;
            }
            sum[n] = (sum[n] - c_hat[n] * t_hat[n]).rem_euclid(Q);
        }
        inv_ntt(&sum)
    });
    let c_tilde_prime = commitment(&mu, &w_approx, &h);
    let norm = z.iter().flatten().map(|coefficient| coefficient.abs()).max().unwrap();
    norm < GAMMA1 - BETA && c_tilde == c_tilde_prime
}

// ---------------------------------------------------------------------------------------------------------
// The comparison.
// ---------------------------------------------------------------------------------------------------------

fn fips204_verify(pk: &[u8; PK_LEN], message: &[u8], sig: &[u8; SIG_LEN]) -> bool {
    match ml_dsa_44::PublicKey::try_from_bytes(*pk) {
        Ok(key) => key.verify(message, sig, &[]),
        Err(_) => false,
    }
}

/// Counts of comparisons and of accepted inputs, for each kind of input.
#[derive(Default)]
struct Tally(BTreeMap<&'static str, (usize, usize)>);

impl Tally {
    /// Runs the three verifiers on one input and requires the same answer from all; `intended` is the answer
    /// that the construction of the input should give.
    fn check(
        &mut self,
        case: &'static str,
        intended: Option<bool>,
        pk: &[u8; PK_LEN],
        message: &[u8],
        sig: &[u8; SIG_LEN],
    ) -> bool {
        let ours = mldsa44::verify(pk, message, sig);
        let theirs = fips204_verify(pk, message, sig);
        let spec = spec_verify(pk, message, sig);
        assert_eq!(ours, theirs, "{case}: mldsa44::verify says {ours}, fips204 says {theirs}, the transcription {spec}");
        assert_eq!(theirs, spec, "{case}: fips204 says {theirs}, the transcription of FIPS 204 says {spec}");
        if let Some(intended) = intended {
            assert_eq!(ours, intended, "{case}: all three say {ours}, the test intended {intended}");
        }
        let entry = self.0.entry(case).or_default();
        entry.0 += 1;
        entry.1 += usize::from(ours);
        ours
    }

    /// Prints the counts and returns the number of comparisons.
    fn report(&self, title: &str) -> usize {
        let comparisons: usize = self.0.values().map(|&(count, _)| count).sum();
        let accepted: usize = self.0.values().map(|&(_, accepted)| accepted).sum();
        let rejected = comparisons - accepted;
        let mut lines = format!("EDGES {title}: {comparisons} inputs, same answer from mldsa44::verify, fips204 and the transcription of FIPS 204 for each; {accepted} accepted, {rejected} rejected");
        for (case, (count, accepted)) in &self.0 {
            lines.push_str(&format!(" | {case}: {count} compared, {accepted} accepted"));
        }
        println!("{lines}");
        comparisons
    }
}

/// A message: the client's 1,356 bytes (label, 32-byte address, public key), a length at or next to a block
/// boundary of the hash, or a random length.
fn message(rng: &mut Rng, index: usize, pk: &[u8; PK_LEN]) -> Vec<u8> {
    match index % 3 {
        0 => [LABEL, &rng.bytes(32), pk].concat(),
        1 => {
            let len = [0usize, 1, 69, 70, 71, 135, 136, 137, 1356][rng.below(9)];
            rng.bytes(len)
        }
        _ => {
            let len = rng.below(3000);
            rng.bytes(len)
        }
    }
}

// ---------------------------------------------------------------------------------------------------------
// Signatures that anyone can write for a public key with t1 = 0.
// ---------------------------------------------------------------------------------------------------------

struct OpenKey {
    pk: [u8; PK_LEN],
    tr: [u8; 64],
    /// ExpandA(rho) and the same sixteen polynomials outside the NTT domain.
    a_hat: Vec<Poly>,
    a: Vec<Poly>,
}

impl OpenKey {
    fn new(rho: [u8; 32]) -> Self {
        let mut pk = [0u8; PK_LEN];
        pk[..32].copy_from_slice(&rho);
        let a_hat = expand_a(&rho);
        let a = a_hat.iter().map(inv_ntt).collect();
        Self { pk, tr: h256_64(&[&pk]), a_hat, a }
    }

    /// The signature with these z and hint bytes whose c-tilde fits the hint `h`.
    fn sign(&self, mu: &[u8; 64], z: &[Poly; L], y: &[u8; HINT_LEN], h: &Hint) -> [u8; SIG_LEN] {
        assemble(&commitment(mu, &a_times(&self.a_hat, z), h), z, y)
    }
}

fn assemble(c_tilde: &[u8; 32], z: &[Poly; L], y: &[u8; HINT_LEN]) -> [u8; SIG_LEN] {
    [c_tilde.as_slice(), &pack_z(z), y].concat().try_into().unwrap()
}

/// z with every coefficient inside the bound of the infinity norm.
fn random_z(rng: &mut Rng) -> [Poly; L] {
    let largest = GAMMA1 - BETA - 1;
    core::array::from_fn(|_| core::array::from_fn(|_| rng.range(-largest, largest)))
}

/// A hint with `counts[i]` bits set in polynomial i: at random places (style 0), at the lowest positions
/// (style 1) or at the highest (style 2).
fn hint_with_counts(rng: &mut Rng, counts: [usize; K], style: usize) -> Hint {
    let mut h = [[false; N]; K];
    for (poly, &count) in h.iter_mut().zip(&counts) {
        match style {
            1 => poly[..count].fill(true),
            2 => poly[N - count..].fill(true),
            _ => {
                let mut set = 0;
                while set < count {
                    let position = rng.below(N);
                    if !poly[position] {
                        poly[position] = true;
                        set += 1;
                    }
                }
            }
        }
    }
    h
}

/// Counts for the four polynomials with a random sum of at most `most`.
fn random_counts(rng: &mut Rng, most: usize) -> [usize; K] {
    let mut counts = [0; K];
    for _ in 0..rng.below(most + 1) {
        counts[rng.below(K)] += 1;
    }
    counts
}

/// What a decoder without the checks of HintBitUnpack reads from `y`: every stored position sets its bit,
/// whatever the order, a repetition or the bytes after the lists. An end offset below the previous one gives
/// an empty list; the next list then starts at the previous offset, or at the lower one (`restart`). An end
/// offset above omega is cut to omega, or the list runs on into the four offset bytes (`run_on`).
fn lenient_hint(y: &[u8; HINT_LEN], restart: bool, run_on: bool) -> Hint {
    let mut h = [[false; N]; K];
    let mut index = 0usize;
    let limit = if run_on { HINT_LEN } else { OMEGA };
    for i in 0..K {
        let end = usize::from(y[OMEGA + i]).min(limit);
        for j in index..end {
            h[i][usize::from(y[j])] = true;
        }
        if end > index || restart {
            index = end;
        }
    }
    h
}

// ---------------------------------------------------------------------------------------------------------
// Tests.
// ---------------------------------------------------------------------------------------------------------

/// The transcription and the helpers of this file agree with fips204 on signatures of the fips204 signer.
#[test]
fn transcription_agrees_with_the_fips204_signer() {
    let mut rng = Rng(SEED + 1);
    let mut tally = Tally::default();
    for index in 0..60 {
        let (pk, sk) = ml_dsa_44::KG::keygen_from_seed(&rng.array());
        let pk = pk.into_bytes();
        let message = message(&mut rng, index, &pk);
        let sig = sk.try_sign_with_seed(&rng.array(), &message, &[]).expect("signing");
        tally.check("signature of the fips204 signer", Some(true), &pk, &message, &sig);
        let mut bad = sig;
        bad[rng.below(32)] ^= 1 << rng.below(8);
        tally.check("signature of the fips204 signer, one bit of c-tilde flipped", Some(false), &pk, &message, &bad);
        // The encodings of this file give the same bytes.
        assert_eq!(pack_z(&unpack_z(&sig)), sig[Z_START..HINT_START]);
        let h = hint_bit_unpack(&sig[HINT_START..]).expect("hint of a valid signature");
        assert_eq!(hint_bit_pack(&h), sig[HINT_START..]);
        assert_eq!(lenient_hint(&hint_bit_pack(&h), false, false), h);
        assert_eq!(lenient_hint(&hint_bit_pack(&h), true, true), h);
    }
    assert_eq!(tally.report("transcription against the fips204 signer"), 120);
}

/// The bound on the infinity norm of z: gamma1 - beta - 1 = 130,993 is the largest accepted magnitude.
#[test]
fn z_norm_bound_decides_alone() {
    let mut rng = Rng(SEED + 2);
    let mut tally = Tally::default();
    let limit = GAMMA1 - BETA;
    assert_eq!(limit, 130_994);
    // One coefficient of z, the answer of FIPS 204, the name of the case.
    let single: [(i64, bool, &'static str); 15] = [
        (limit - 1, true, "z: one coefficient at +(gamma1-beta-1), the largest accepted"),
        (-(limit - 1), true, "z: one coefficient at -(gamma1-beta-1), the largest accepted"),
        (limit - 2, true, "z: one coefficient at +-(gamma1-beta-2)"),
        (-(limit - 2), true, "z: one coefficient at +-(gamma1-beta-2)"),
        (limit, false, "z: one coefficient at +(gamma1-beta), the smallest rejected"),
        (-limit, false, "z: one coefficient at -(gamma1-beta), the smallest rejected"),
        (limit + 1, false, "z: one coefficient at +-(gamma1-beta+1)"),
        (-(limit + 1), false, "z: one coefficient at +-(gamma1-beta+1)"),
        (GAMMA1 - 1, false, "z: one coefficient at an end of the 18-bit range"),
        (GAMMA1, false, "z: one coefficient at an end of the 18-bit range"),
        (-GAMMA1 + 1, false, "z: one coefficient at an end of the 18-bit range"),
        (-GAMMA1 + 2, false, "z: one coefficient at an end of the 18-bit range"),
        (0, true, "z: one coefficient at 0 or +-1"),
        (1, true, "z: one coefficient at 0 or +-1"),
        (-1, true, "z: one coefficient at 0 or +-1"),
    ];
    for key_index in 0..3 {
        let key = OpenKey::new(rng.array());
        let message = message(&mut rng, key_index, &key.pk);
        let mu = mu_pure(&key.tr, &message);
        let no_hint = [[false; N]; K];
        let no_hint_bytes = [0u8; HINT_LEN];

        for column in 0..L {
            for position in [0, 255, rng.below(N)] {
                for (round, (value, intended, case)) in single.into_iter().enumerate() {
                    let mut z = random_z(&mut rng);
                    z[column][position] = value;
                    // With a hint in every second round.
                    let counts = random_counts(&mut rng, OMEGA);
                    let h = if round % 2 == 0 { no_hint } else { hint_with_counts(&mut rng, counts, 0) };
                    let sig = key.sign(&mu, &z, &hint_bit_pack(&h), &h);
                    tally.check(case, Some(intended), &key.pk, &message, &sig);
                }
            }
        }

        // The same value in every coefficient (the last entry alternates the sign).
        let whole: [(i64, bool, &'static str); 8] = [
            (limit - 1, true, "z: every coefficient at +(gamma1-beta-1)"),
            (-(limit - 1), true, "z: every coefficient at -(gamma1-beta-1)"),
            (0, true, "z: every coefficient zero"),
            (limit, false, "z: every coefficient at +(gamma1-beta)"),
            (-limit, false, "z: every coefficient at -(gamma1-beta)"),
            (-GAMMA1 + 1, false, "z: all bytes 0xff, with the c-tilde that fits"),
            (GAMMA1, false, "z: all bytes 0x00, with the c-tilde that fits"),
            (limit - 1, true, "z: coefficients alternate between +(gamma1-beta-1) and -(gamma1-beta-1)"),
        ];
        for (index, (value, intended, case)) in whole.into_iter().enumerate() {
            let z: [Poly; L] =
                core::array::from_fn(|_| core::array::from_fn(|n| if index == 7 && n % 2 == 1 { -value } else { value }));
            let sig = key.sign(&mu, &z, &no_hint_bytes, &no_hint);
            if value == -GAMMA1 + 1 {
                assert!(sig[Z_START..HINT_START].iter().all(|&byte| byte == 0xff));
            }
            if value == GAMMA1 {
                assert!(sig[Z_START..HINT_START].iter().all(|&byte| byte == 0));
            }
            tally.check(case, Some(intended), &key.pk, &message, &sig);
        }
        // The same value in every coefficient of one polynomial.
        for column in 0..L {
            for (value, intended, case) in [
                (-GAMMA1 + 1, false, "z: one polynomial all bytes 0xff, with the c-tilde that fits"),
                (limit - 1, true, "z: one polynomial with every coefficient at +(gamma1-beta-1)"),
                (-limit, false, "z: one polynomial with every coefficient at -(gamma1-beta)"),
            ] {
                let mut z = random_z(&mut rng);
                z[column] = [value; N];
                let sig = key.sign(&mu, &z, &no_hint_bytes, &no_hint);
                tally.check(case, Some(intended), &key.pk, &message, &sig);
            }
        }
    }
    assert_eq!(tally.report("z at the bound of the infinity norm"), 3 * (4 * 3 * 15 + 8 + 4 * 3));
    assert_eq!(tally.0["z: one coefficient at +(gamma1-beta-1), the largest accepted"], (36, 36));
    assert_eq!(tally.0["z: one coefficient at +(gamma1-beta), the smallest rejected"], (36, 0));
    assert_eq!(tally.0["z: one coefficient at -(gamma1-beta-1), the largest accepted"], (36, 36));
    assert_eq!(tally.0["z: one coefficient at -(gamma1-beta), the smallest rejected"], (36, 0));
}

/// Hints: every well-formed encoding is accepted, every malformed one is rejected although its c-tilde is the
/// one that a decoder without the checks would compute.
#[test]
fn hint_encoding_decides_alone() {
    let mut rng = Rng(SEED + 3);
    let mut tally = Tally::default();
    for key_index in 0..3 {
        let key = OpenKey::new(rng.array());
        let message = message(&mut rng, key_index, &key.pk);
        let mu = mu_pure(&key.tr, &message);

        // Well-formed hints with these numbers of bits in the four polynomials.
        let shapes: [[usize; K]; 16] = [
            [0, 0, 0, 0],
            [80, 0, 0, 0],
            [0, 80, 0, 0],
            [0, 0, 80, 0],
            [0, 0, 0, 80],
            [20, 20, 20, 20],
            [79, 1, 0, 0],
            [1, 0, 0, 79],
            [0, 0, 0, 1],
            [1, 0, 0, 0],
            [40, 40, 0, 0],
            [0, 40, 0, 40],
            [1, 1, 1, 1],
            [79, 0, 0, 0],
            [27, 26, 27, 0],
            [0, 1, 78, 1],
        ];
        for counts in shapes {
            for style in 0..3 {
                let h = hint_with_counts(&mut rng, counts, style);
                let y = hint_bit_pack(&h);
                assert_eq!(hint_bit_unpack(&y), Some(h));
                let case = if counts.iter().sum::<usize>() == OMEGA {
                    "hint: well formed, omega = 80 bits in all"
                } else if counts.contains(&0) {
                    "hint: well formed, with empty lists"
                } else {
                    "hint: well formed, no empty list"
                };
                let sig = key.sign(&mu, &random_z(&mut rng), &y, &h);
                tally.check(case, Some(true), &key.pk, &message, &sig);
            }
        }
        for _ in 0..40 {
            let counts = random_counts(&mut rng, OMEGA);
            let h = hint_with_counts(&mut rng, counts, 0);
            let sig = key.sign(&mu, &random_z(&mut rng), &hint_bit_pack(&h), &h);
            tally.check("hint: well formed, random", Some(true), &key.pk, &message, &sig);
        }

        // Hint bytes that are well formed although the positions do not increase from one list to the next:
        // the order is checked inside a list only. (positions, end offsets)
        let ascending: Vec<u8> = (0..80).collect();
        let four_runs: Vec<u8> = (0..80).map(|i| i % 20).collect();
        let high: Vec<u8> = (176..=255).collect();
        let raw: [(&[u8], [u8; K]); 10] = [
            (&[255, 255, 255, 255], [1, 2, 3, 4]),
            (&[5, 5, 5, 5], [1, 2, 3, 4]),
            (&[200, 100, 50, 0], [1, 2, 3, 4]),
            (&[0, 255, 0, 255, 0, 255, 0, 255], [2, 4, 6, 8]),
            (&ascending, [80, 80, 80, 80]),
            (&ascending, [0, 0, 0, 80]),
            (&ascending, [0, 80, 80, 80]),
            (&four_runs, [20, 40, 60, 80]),
            (&high, [80, 80, 80, 80]),
            (&[0], [0, 0, 0, 1]),
        ];
        for (positions, ends) in raw {
            let mut y = [0u8; HINT_LEN];
            y[..positions.len()].copy_from_slice(positions);
            y[OMEGA..].copy_from_slice(&ends);
            let h = hint_bit_unpack(&y).expect("a well-formed hint");
            assert_eq!(lenient_hint(&y, false, false), h);
            let sig = key.sign(&mu, &random_z(&mut rng), &y, &h);
            tally.check("hint: well formed, written as bytes (order across lists free)", Some(true), &key.pk, &message, &sig);
        }

        // Malformed hints, each made from a well-formed one whose lists have 2 to 19 positions.
        for _ in 0..40 {
            let counts: [usize; K] = core::array::from_fn(|_| 2 + rng.below(18));
            let h = hint_with_counts(&mut rng, counts, 0);
            let base = hint_bit_pack(&h);
            let ends: [usize; K] = core::array::from_fn(|i| usize::from(base[OMEGA + i]));
            let starts = [0, ends[0], ends[1], ends[2]];
            let used = ends[K - 1];
            assert!(used <= 76);
            let list = rng.below(K);
            let mut cases: Vec<(&'static str, [u8; HINT_LEN])> = Vec::new();

            let at = starts[list] + 1 + rng.below(counts[list] - 1);
            let mut y = base;
            y.swap(at - 1, at);
            cases.push(("hint: two neighbouring positions of a list swapped (same bits)", y));

            let at = starts[list] + rng.below(counts[list]);
            let mut y = base;
            y.copy_within(at..used, at + 1);
            for end in &mut y[OMEGA + list..] {
                *end += 1;
            }
            assert_eq!(y[at], y[at + 1]);
            cases.push(("hint: a position stored twice (same bits)", y));

            let at = starts[list] + 1 + rng.below(counts[list] - 1);
            let mut y = base;
            y[at] = y[at - 1];
            cases.push(("hint: a position replaced by the one before it", y));

            let mut y = base;
            y[starts[list]..ends[list]].reverse();
            cases.push(("hint: a list in decreasing order (same bits)", y));

            let mut y = base;
            y[used] = 1 + rng.below(255) as u8;
            cases.push(("hint: a non-zero byte after the lists (same bits)", y));
            let mut y = base;
            y[OMEGA - 1] = 1 + rng.below(255) as u8;
            cases.push(("hint: a non-zero byte after the lists (same bits)", y));

            let mut y = base;
            y[OMEGA + K - 1] = (OMEGA + 1 + rng.below(4)) as u8;
            cases.push(("hint: last end offset 81 to 84", y));
            let mut y = base;
            y[OMEGA + rng.below(K)] = (OMEGA + 1 + rng.below(255 - OMEGA)) as u8;
            cases.push(("hint: an end offset above omega", y));

            let i = 1 + rng.below(K - 1);
            let mut y = base;
            y[OMEGA + i] = rng.below(ends[i - 1]) as u8;
            cases.push(("hint: an end offset below the one before it", y));
            let mut y = base;
            y.swap(OMEGA, OMEGA + 1);
            cases.push(("hint: the first two end offsets exchanged", y));

            for (case, y) in cases {
                assert!(hint_bit_unpack(&y).is_none(), "{case}: the hint of the test is well formed");
                let z = random_z(&mut rng);
                let w = a_times(&key.a_hat, &z);
                // One signature for each different c-tilde that a decoder without the checks would compute.
                let mut seen: Vec<[u8; 32]> = Vec::new();
                for (restart, run_on) in [(false, false), (true, false), (false, true), (true, true)] {
                    let c_tilde = commitment(&mu, &w, &lenient_hint(&y, restart, run_on));
                    if seen.contains(&c_tilde) {
                        continue;
                    }
                    seen.push(c_tilde);
                    tally.check(case, Some(false), &key.pk, &message, &assemble(&c_tilde, &z, &y));
                }
            }
        }
    }
    let comparisons = tally.report("hint encodings");
    assert!(comparisons >= 3 * (16 * 3 + 40 + 10 + 40 * 10));
    for (case, &(count, accepted)) in &tally.0 {
        assert_eq!(accepted, if case.contains("well formed") { count } else { 0 }, "{case}");
    }
}

/// A coefficient of w'_approx on each special residue of Decompose and UseHint, without and with its hint bit.
#[test]
fn use_hint_special_residues_in_a_whole_verification() {
    let mut rng = Rng(SEED + 4);
    let mut tally = Tally::default();
    let g = GAMMA2;
    assert_eq!((g, 44 * 2 * g), (95_232, Q - 1));
    // The residue r, UseHint(0, r), UseHint(1, r).
    let residues: [(i64, i64, i64); 16] = [
        (0, 0, 43),
        (1, 0, 1),
        (g, 0, 1),
        (g + 1, 1, 0),
        (2 * g - 1, 1, 0),
        (2 * g, 1, 0),
        (2 * g + 1, 1, 2),
        (22 * 2 * g, 22, 21),
        (21 * 2 * g + g, 21, 22),
        (21 * 2 * g + g + 1, 22, 21),
        (43 * 2 * g, 43, 42),
        (43 * 2 * g + 1, 43, 0),
        (43 * 2 * g + g, 43, 0),
        // r+ - r0 = q - 1: Decompose gives r1 = 0 and a negative r0.
        (Q - g, 0, 43),
        (Q - 2, 0, 43),
        (Q - 1, 0, 43),
    ];
    for &(r, without, with) in &residues {
        assert_eq!((use_hint(false, r), use_hint(true, r)), (without, with), "UseHint of the transcription at {r}");
    }
    for key_index in 0..2 {
        let key = OpenKey::new(rng.array());
        let message = message(&mut rng, key_index, &key.pk);
        let mu = mu_pure(&key.tr, &message);
        for (row, n) in [(0usize, 0usize), (1, 17), (2, 128), (3, 255)] {
            for &(target, _, _) in &residues {
                // z with zeros in the constant coefficients of its first two polynomials; adding d0 and d1
                // there adds d0 * a[row][0][n] + d1 * a[row][1][n] to coefficient n of row `row` of A*z.
                let mut z = random_z(&mut rng);
                z[0][0] = 0;
                z[1][0] = 0;
                let w = a_times(&key.a_hat, &z);
                let (alpha, beta) = (key.a[row * L][n], key.a[row * L + 1][n]);
                assert_ne!(beta, 0);
                let beta_inverse = pow_mod(beta, (Q - 2) as u64);
                let delta = (target - w[row][n]).rem_euclid(Q);
                let mut found = false;
                for step in 0..40_000i64 {
                    let d0 = if step % 2 == 0 { step / 2 } else { -(step + 1) / 2 };
                    let mut d1 = (delta - d0 * alpha).rem_euclid(Q) * beta_inverse % Q;
                    if d1 > Q / 2 {
                        d1 -= Q;
                    }
                    if d1.abs() <= 100_000 {
                        z[0][0] = d0;
                        z[1][0] = d1;
                        found = true;
                        break;
                    }
                }
                assert!(found, "no small change of z reaches the residue");
                let w = a_times(&key.a_hat, &z);
                assert_eq!(w[row][n], target);

                for hint_bit in [false, true] {
                    // Other hint bits at random, at most 15 in each polynomial.
                    let counts: [usize; K] = core::array::from_fn(|_| rng.below(16));
                    let mut h = hint_with_counts(&mut rng, counts, 0);
                    h[row][n] = hint_bit;
                    let y = hint_bit_pack(&h);
                    let sig = assemble(&commitment(&mu, &w, &h), &z, &y);
                    let case = match (target > Q - 1 - g, hint_bit) {
                        (true, false) => "w' coefficient with r+ - r0 = q - 1, no hint bit",
                        (true, true) => "w' coefficient with r+ - r0 = q - 1, hint bit set",
                        (false, false) => "w' coefficient at an edge of Decompose, no hint bit",
                        (false, true) => "w' coefficient at an edge of Decompose, hint bit set",
                    };
                    tally.check(case, Some(true), &key.pk, &message, &sig);
                }
            }
        }
    }
    assert_eq!(tally.report("special residues of Decompose and UseHint"), 2 * 4 * 16 * 2);
}

/// A key pair from rho, K, s1 and s2 (Algorithm 6 from its step 3 on; skEncode and pkEncode, Algorithms 24
/// and 22). The coefficients of s1 and s2 are signed, from -2 to 2.
fn custom_key(rho: [u8; 32], cap_k: [u8; 32], s1: &[Poly; L], s2: &[Poly; K]) -> ([u8; PK_LEN], [u8; SK_LEN]) {
    let as1 = a_times(&expand_a(&rho), s1);
    let (mut t1, mut t0) = (Vec::with_capacity(K * N), Vec::with_capacity(K * N));
    for r in 0..K {
        for n in 0..N {
            let (high, low) = power2round(as1[r][n] + s2[r][n]);
            t1.push(high);
            t0.push(low);
        }
    }
    let mut pk = [0u8; PK_LEN];
    pk[..32].copy_from_slice(&rho);
    pk[32..].copy_from_slice(&pack_bits(&t1, 10));
    let tr = h256_64(&[&pk]);
    // BitPack(s, eta, eta) stores eta - s on 3 bits; BitPack(t0, 2^(d-1) - 1, 2^(d-1)) stores 2^(d-1) - t0 on
    // 13 bits.
    let eta_minus = |polys: &[Poly]| -> Vec<i64> { polys.iter().flatten().map(|&coefficient| 2 - coefficient).collect() };
    let top_minus: Vec<i64> = t0.iter().map(|&coefficient| (1 << (D - 1)) - coefficient).collect();
    let sk = [
        rho.as_slice(),
        &cap_k,
        &tr,
        &pack_bits(&eta_minus(s1), 3),
        &pack_bits(&eta_minus(s2), 3),
        &pack_bits(&top_minus, 13),
    ]
    .concat();
    (pk, sk.try_into().unwrap())
}

/// Signatures of the fips204 signer under private keys written by hand.
#[test]
fn keys_with_extreme_t1() {
    let mut rng = Rng(SEED + 5);
    let mut tally = Tally::default();
    let constant = |value: i64| -> [Poly; 4] { [[value; N]; 4] };
    let alternate =
        |even: i64, odd: i64| -> [Poly; 4] { [core::array::from_fn(|n| if n % 2 == 0 { even } else { odd }); 4] };
    let random_small =
        |rng: &mut Rng| -> [Poly; 4] { core::array::from_fn(|_| core::array::from_fn(|_| rng.range(-2, 2))) };
    // s1, s2, what the public key is, whether t0 is zero (then no hint bit is ever set).
    let mut keys: Vec<([Poly; L], [Poly; K], &'static str, bool)> = vec![
        (constant(0), constant(0), "key with t1 = 0 (s1 = 0, s2 = 0)", true),
        (constant(0), constant(-1), "key with t1 = 1023 everywhere (s1 = 0, s2 = -1)", true),
        (constant(0), constant(-2), "key with t1 = 1023 everywhere (s1 = 0, s2 = -2)", false),
        (constant(0), constant(2), "key with t1 = 0 and t0 = 2 (s1 = 0, s2 = 2)", false),
        (constant(0), alternate(-1, 1), "key with t1 alternating 1023 and 0 (s1 = 0)", false),
        (constant(0), alternate(2, -2), "key with t1 alternating 0 and 1023 (s1 = 0)", false),
        (constant(2), constant(-2), "key with s1 = 2 and s2 = -2 everywhere", false),
        (constant(-2), constant(2), "key with s1 = -2 and s2 = 2 everywhere", false),
    ];
    for _ in 0..6 {
        keys.push((random_small(&mut rng), random_small(&mut rng), "key from random s1 and s2", false));
    }
    let mut inputs = 0;
    for (key_index, (s1, s2, case, t0_is_zero)) in keys.into_iter().enumerate() {
        let rho: [u8; 32] = rng.array();
        let (pk, sk_bytes) = custom_key(rho, rng.array(), &s1, &s2);
        let sk = ml_dsa_44::PrivateKey::try_from_bytes(sk_bytes).expect("a private key in range");
        // fips204 derives the same public key from s1 and s2.
        assert_eq!(sk.get_public_key().into_bytes(), pk, "{case}");
        match key_index {
            0 | 3 => assert!(pk[32..].iter().all(|&byte| byte == 0)),
            1 | 2 => assert!(pk[32..].iter().all(|&byte| byte == 0xff)),
            _ => {}
        }
        let open = OpenKey::new(rho);
        for index in 0..6 {
            let message = message(&mut rng, index, &pk);
            let sig = sk.try_sign_with_seed(&rng.array(), &message, &[]).expect("signing");
            tally.check(case, Some(true), &pk, &message, &sig);
            if t0_is_zero {
                assert!(sig[HINT_START..].iter().all(|&byte| byte == 0), "{case}: a hint bit is set");
            }
            if key_index == 0 {
                // The signature that this file writes for the same z is the signer's, byte for byte.
                assert_eq!(pk, open.pk);
                let no_hint = [[false; N]; K];
                let written = open.sign(&mu_pure(&open.tr, &message), &unpack_z(&sig), &[0; HINT_LEN], &no_hint);
                assert_eq!(written, sig);
            }
            let mut bad = sig;
            bad[rng.below(32)] ^= 1 << rng.below(8);
            tally.check("hand-written key: one bit of c-tilde flipped", Some(false), &pk, &message, &bad);
            let mut longer = message.clone();
            longer.push(0);
            tally.check("hand-written key: message one byte longer", Some(false), &pk, &longer, &sig);
            inputs += 3;
            if sig[HINT_START + OMEGA + K - 1] < OMEGA as u8 {
                let mut bad = sig;
                bad[HINT_START + OMEGA - 1] = 1;
                tally.check("hand-written key: non-zero byte after the hint lists", Some(false), &pk, &message, &bad);
                inputs += 1;
            }
        }
    }
    assert_eq!(tally.report("keys written by hand"), inputs);
    assert!(inputs >= 14 * 6 * 3);
}

/// The message format: M' = 0x00 || 0x00 || M and tr = H(pk, 64), nothing else.
#[test]
fn message_format_decides_alone() {
    let mut rng = Rng(SEED + 6);
    let mut tally = Tally::default();
    let oid = fips204::pre_hash::SHA2_512;
    // Signatures of the fips204 signer for other formats.
    for index in 0..20 {
        let (pk_key, sk) = ml_dsa_44::KG::keygen_from_seed(&rng.array());
        let pk = pk_key.clone().into_bytes();
        let message = message(&mut rng, index, &pk);
        let context_len = 1 + rng.below(8);
        let context = rng.bytes(context_len);
        let with_context = sk.try_sign_with_seed(&rng.array(), &message, &context).expect("signing");
        assert!(pk_key.verify(&message, &with_context, &context));
        tally.check("signature made with a context string", Some(false), &pk, &message, &with_context);
        let joined = [context.as_slice(), &message].concat();
        tally.check("signature made with a context string, context put before the message", Some(false), &pk, &joined, &with_context);

        let digest: [u8; 64] = rng.array();
        let pre_hashed = sk.try_hash_sign_with_seed(&rng.array(), &digest, &[], &oid).expect("signing");
        assert!(pk_key.hash_verify(&digest, &pre_hashed, &[], &oid));
        tally.check("signature of the pre-hash variant, digest as message", Some(false), &pk, &digest, &pre_hashed);
        let joined = [&oid[..], &digest].concat();
        tally.check("signature of the pre-hash variant, OID and digest as message", Some(false), &pk, &joined, &pre_hashed);

        // A pure signature of M is what an interface without the prefix would accept for 0x00 || 0x00 || M.
        let sig = sk.try_sign_with_seed(&rng.array(), &message, &[]).expect("signing");
        tally.check("pure signature", Some(true), &pk, &message, &sig);
        let prefixed = [&[0u8, 0][..], &message].concat();
        tally.check("pure signature of M presented for 0x00 0x00 M", Some(false), &pk, &prefixed, &sig);
        let prefixed = [&[0u8][..], &message].concat();
        tally.check("pure signature of M presented for 0x00 M", Some(false), &pk, &prefixed, &sig);
    }
    // Signatures written for a key with t1 = 0 whose message representative is not the one of the standard.
    for key_index in 0..6 {
        let key = OpenKey::new(rng.array());
        let message = message(&mut rng, key_index, &key.pk);
        let mut tr32 = [0u8; 32];
        h256(&[&key.pk], &mut tr32);
        let representatives: [(&'static str, bool, [u8; 64]); 9] = [
            ("mu = H(tr || 0x00 || 0x00 || M), the standard", true, mu_pure(&key.tr, &message)),
            ("mu = H(tr || M), no prefix", false, h256_64(&[&key.tr, &message])),
            ("mu = H(tr || 0x00 || M), one prefix byte", false, h256_64(&[&key.tr, &[0], &message])),
            ("mu = H(tr || 0x00 0x00 0x00 || M), three prefix bytes", false, h256_64(&[&key.tr, &[0, 0, 0], &message])),
            ("mu = H(tr || 0x01 || 0x00 || M), prefix of the pre-hash variant", false, h256_64(&[&key.tr, &[1, 0], &message])),
            ("mu = H(tr || 0x00 || 0x01 || M), wrong context length", false, h256_64(&[&key.tr, &[0, 1], &message])),
            ("mu with a 32-byte tr", false, h256_64(&[&tr32, &[0, 0], &message])),
            ("mu = H(pk || 0x00 || 0x00 || M), key in place of tr", false, h256_64(&[&key.pk, &[0, 0], &message])),
            ("mu = H(0x00 || 0x00 || M), no tr", false, h256_64(&[&[0, 0], &message])),
        ];
        for (case, intended, mu) in representatives {
            let counts = random_counts(&mut rng, OMEGA);
            let h = hint_with_counts(&mut rng, counts, 0);
            let sig = key.sign(&mu, &random_z(&mut rng), &hint_bit_pack(&h), &h);
            tally.check(case, Some(intended), &key.pk, &message, &sig);
        }
    }
    assert_eq!(tally.report("message formats"), 20 * 7 + 6 * 9);
}

/// Inputs without structure, and well-formed signatures of nothing.
#[test]
fn inputs_without_a_signer() {
    let mut rng = Rng(SEED + 7);
    let mut tally = Tally::default();
    for index in 0..150 {
        let pk: [u8; PK_LEN] = rng.array();
        let message = message(&mut rng, index, &pk);
        let sig: [u8; SIG_LEN] = rng.array();
        tally.check("random key, random signature bytes", Some(false), &pk, &message, &sig);
    }
    for index in 0..150 {
        let (pk, _) = ml_dsa_44::KG::keygen_from_seed(&rng.array());
        let pk = pk.into_bytes();
        let message = message(&mut rng, index, &pk);
        // In range and well formed, so that the verification runs to its last comparison.
        let counts = random_counts(&mut rng, OMEGA);
        let h = hint_with_counts(&mut rng, counts, 0);
        let sig = assemble(&rng.array(), &random_z(&mut rng), &hint_bit_pack(&h));
        tally.check("real key, random c-tilde and z in range, well-formed hint", Some(false), &pk, &message, &sig);
    }
    for index in 0..150 {
        let key = OpenKey::new(rng.array());
        let message = message(&mut rng, index, &key.pk);
        let counts = random_counts(&mut rng, OMEGA);
        let h = hint_with_counts(&mut rng, counts, 0);
        let sig = key.sign(&mu_pure(&key.tr, &message), &random_z(&mut rng), &hint_bit_pack(&h), &h);
        tally.check("key with t1 = 0: written signature", Some(true), &key.pk, &message, &sig);
        let mut bad = sig;
        bad[rng.below(SIG_LEN)] ^= 1 << rng.below(8);
        tally.check("key with t1 = 0: written signature, one bit flipped anywhere", Some(false), &key.pk, &message, &bad);
        let mut other = key.pk;
        other[32 + rng.below(PK_LEN - 32)] ^= 1 << rng.below(8);
        tally.check("key with t1 = 0: written signature, one bit of t1 set", Some(false), &other, &message, &sig);
    }
    assert_eq!(tally.report("inputs without a signer"), 150 + 150 + 3 * 150);
}

/// The program's instruction rebuilds label || wallet address || public key and answers InvalidArgument for
/// the rejections above.
#[test]
fn program_instruction_on_written_signatures() {
    let mut rng = Rng(SEED + 8);
    let mut tally = Tally::default();
    let call = |wallet: &Pubkey, pk: &[u8; PK_LEN], sig: &[u8; SIG_LEN]| -> Result<(), ProgramError> {
        let program_id = Pubkey::new_from_array([9; 32]);
        let owner = Pubkey::new_from_array([0; 32]);
        let mut lamports = 1;
        let mut account_data = [];
        let accounts = [AccountInfo::new(wallet, true, true, &mut lamports, &mut account_data, &owner, false)];
        process_instruction(&program_id, &accounts, &[pk.as_slice(), sig].concat())
    };
    let limit = GAMMA1 - BETA;
    assert_eq!(LABEL, &b"pq-enroll-v1"[..]);
    for _ in 0..12 {
        let key = OpenKey::new(rng.array());
        let wallet = Pubkey::new_from_array(rng.array());
        let other_wallet = Pubkey::new_from_array(rng.array());
        let message = [LABEL, wallet.as_ref(), &key.pk].concat();
        assert_eq!(message.len(), 1356);
        let mu = mu_pure(&key.tr, &message);
        let counts: [usize; K] = core::array::from_fn(|_| 2 + rng.below(18));
        let h = hint_with_counts(&mut rng, counts, 0);
        let y = hint_bit_pack(&h);

        let sig = key.sign(&mu, &random_z(&mut rng), &y, &h);
        tally.check("program: written proof of possession", Some(true), &key.pk, &message, &sig);
        assert_eq!(call(&wallet, &key.pk, &sig), Ok(()));
        assert_eq!(call(&other_wallet, &key.pk, &sig), Err(ProgramError::InvalidArgument));
        // Valid signatures of the messages that other orders of the three parts would give.
        let others: [(&'static str, Vec<u8>); 3] = [
            ("program: proof for wallet || label || key", [wallet.as_ref(), LABEL, &key.pk].concat()),
            ("program: proof for label || key || wallet", [LABEL, &key.pk, wallet.as_ref()].concat()),
            ("program: proof for label || key", [LABEL, &key.pk].concat()),
        ];
        for (case, other) in others {
            let sig = key.sign(&mu_pure(&key.tr, &other), &random_z(&mut rng), &y, &h);
            tally.check(case, Some(true), &key.pk, &other, &sig);
            assert_eq!(call(&wallet, &key.pk, &sig), Err(ProgramError::InvalidArgument), "{case}");
        }

        let mut z = random_z(&mut rng);
        z[rng.below(L)][rng.below(N)] = if rng.below(2) == 0 { limit } else { -limit };
        let sig = key.sign(&mu, &z, &y, &h);
        tally.check("program: z at gamma1 - beta", Some(false), &key.pk, &message, &sig);
        assert_eq!(call(&wallet, &key.pk, &sig), Err(ProgramError::InvalidArgument));
        let mut z = random_z(&mut rng);
        z[rng.below(L)][rng.below(N)] = if rng.below(2) == 0 { limit - 1 } else { -(limit - 1) };
        let sig = key.sign(&mu, &z, &y, &h);
        tally.check("program: z at gamma1 - beta - 1", Some(true), &key.pk, &message, &sig);
        assert_eq!(call(&wallet, &key.pk, &sig), Ok(()));

        let mut swapped = y;
        swapped.swap(0, 1);
        let sig = key.sign(&mu, &random_z(&mut rng), &swapped, &h);
        tally.check("program: two hint positions swapped", Some(false), &key.pk, &message, &sig);
        assert_eq!(call(&wallet, &key.pk, &sig), Err(ProgramError::InvalidArgument));
        let mut trailing = y;
        trailing[OMEGA - 1] = 7;
        let sig = key.sign(&mu, &random_z(&mut rng), &trailing, &h);
        tally.check("program: non-zero byte after the hint lists", Some(false), &key.pk, &message, &sig);
        assert_eq!(call(&wallet, &key.pk, &sig), Err(ProgramError::InvalidArgument));
    }
    assert_eq!(tally.report("program instruction"), 12 * 8);
}
