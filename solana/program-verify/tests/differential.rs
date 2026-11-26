//! Differential tests: `mldsa44::verify` against the `fips204` crate.
//!
//! Each test generates keys, messages and signatures with `fips204` from a generator with a fixed seed. For
//! every pair of key and message the unmodified signature must verify, and a set of mutated inputs must get
//! the same answer from both verifiers.

use std::collections::BTreeMap;
use std::ops::Range;

use fips204::ml_dsa_44;
use fips204::traits::{KeyGen as _, SerDes as _, Signer as _, Verifier as _};
use pq_verify_in_vm::mldsa44;

const PK_LEN: usize = mldsa44::PUBLIC_KEY_LEN;
const SIG_LEN: usize = mldsa44::SIGNATURE_LEN;

// The layout of a signature: c-tilde, four polynomials of z at 18 bits a coefficient, the hint (OMEGA bytes
// of positions and K end offsets). The layout of a public key: rho, four polynomials of t1 at 10 bits.
const C_TILDE: Range<usize> = 0..32;
const Z: Range<usize> = 32..32 + 4 * 576;
const HINT: Range<usize> = 32 + 4 * 576..SIG_LEN;
const OMEGA: usize = 80;
const K: usize = 4;
const RHO: Range<usize> = 0..32;
const T1: Range<usize> = 32..PK_LEN;

/// The label of the message that the client signs: label, 32-byte address, public key, 1,356 bytes in all.
const LABEL: &[u8] = b"pq-enroll-v1";

/// Pairs of key and message in each of the tests below.
const PAIRS_PER_TEST: usize = 2000;

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

    fn bytes(&mut self, len: usize) -> Vec<u8> {
        (0..len).map(|_| self.next() as u8).collect()
    }

    fn seed(&mut self) -> [u8; 32] {
        self.bytes(32).try_into().unwrap()
    }
}

fn reference(pk: &[u8; PK_LEN], message: &[u8], sig: &[u8; SIG_LEN]) -> bool {
    match ml_dsa_44::PublicKey::try_from_bytes(*pk) {
        Ok(key) => key.verify(message, sig, &[]),
        Err(_) => false,
    }
}

/// Counts of comparisons and of accepted inputs, for each kind of input.
#[derive(Default)]
struct Tally(BTreeMap<&'static str, (usize, usize)>);

impl Tally {
    /// Runs both verifiers on one input, requires the same answer from both and returns it.
    fn compare(&mut self, case: &'static str, pk: &[u8; PK_LEN], message: &[u8], sig: &[u8; SIG_LEN]) -> bool {
        let ours = mldsa44::verify(pk, message, sig);
        let theirs = reference(pk, message, sig);
        assert_eq!(ours, theirs, "{case}: mldsa44::verify says {ours}, fips204 says {theirs}");
        let entry = self.0.entry(case).or_default();
        entry.0 += 1;
        entry.1 += usize::from(ours);
        ours
    }

    /// The same, for an input that no correct verifier accepts.
    fn rejected(&mut self, case: &'static str, pk: &[u8; PK_LEN], message: &[u8], sig: &[u8; SIG_LEN]) {
        assert!(!self.compare(case, pk, message, sig), "{case}: accepted");
    }
}

/// A message: the client's 1,356 bytes for every fourth pair, otherwise random bytes of a length at or next
/// to a block boundary of the hash, or of a random length up to 5,000.
fn message(rng: &mut Rng, index: usize, pk: &[u8; PK_LEN]) -> Vec<u8> {
    const LENGTHS: [usize; 20] =
        [0, 1, 2, 31, 32, 33, 64, 69, 70, 71, 135, 136, 137, 205, 206, 207, 1355, 1356, 1357, 4096];
    match index % 4 {
        0 => [LABEL, &rng.bytes(32), pk].concat(),
        1 => {
            let len = LENGTHS[rng.below(LENGTHS.len())];
            rng.bytes(len)
        }
        _ => {
            let len = rng.below(5001);
            rng.bytes(len)
        }
    }
}

fn differential(seed: u64) {
    let mut rng = Rng(seed);
    let mut tally = Tally::default();
    let mut client_shaped = 0;
    let mut other_pk = ml_dsa_44::KG::keygen_from_seed(&rng.seed()).0.into_bytes();
    for index in 0..PAIRS_PER_TEST {
        let (pk, sk) = ml_dsa_44::KG::keygen_from_seed(&rng.seed());
        let pk = pk.into_bytes();
        let message = message(&mut rng, index, &pk);
        client_shaped += usize::from(message.len() == 1356 && message.starts_with(LABEL) && message.ends_with(&pk));
        let sig = sk.try_sign_with_seed(&rng.seed(), &message, &[]).expect("signing");

        assert!(tally.compare("valid signature", &pk, &message, &sig), "a valid signature was rejected");

        // One flipped bit at a random position of c-tilde, of z, of the hint.
        for (case, field) in
            [("bit flipped in c-tilde", C_TILDE), ("bit flipped in z", Z), ("bit flipped in hint", HINT)]
        {
            let mut bad = sig;
            bad[field.start + rng.below(field.len())] ^= 1 << rng.below(8);
            tally.rejected(case, &pk, &message, &bad);
        }

        // A wrong message: one bit flipped (one byte added to an empty message), and one byte more or less.
        let mut wrong = message.clone();
        if wrong.is_empty() {
            wrong.push(rng.next() as u8);
        } else {
            let at = rng.below(wrong.len());
            wrong[at] ^= 1 << rng.below(8);
        }
        tally.rejected("message with a flipped bit", &pk, &wrong, &sig);
        let mut wrong = message.clone();
        if wrong.is_empty() || rng.below(2) == 0 {
            wrong.push(0);
        } else {
            wrong.pop();
        }
        tally.rejected("message one byte longer or shorter", &pk, &wrong, &sig);

        // Another key: the key of the previous pair, and this key with one bit flipped, in rho, in the lowest
        // bit of a coefficient of t1 (the smallest change of A*z - c*t1*2^d that a key can make), and anywhere
        // in t1. Every change of the key changes tr = H(pk) and with it the message representative.
        tally.rejected("another key", &other_pk, &message, &sig);
        let mut bad_pk = pk;
        bad_pk[RHO.start + rng.below(RHO.len())] ^= 1 << rng.below(8);
        tally.rejected("key with a flipped bit in rho", &bad_pk, &message, &sig);
        let mut bad_pk = pk;
        let bit = 10 * rng.below(K * 256);
        bad_pk[T1.start + bit / 8] ^= 1 << (bit % 8);
        tally.rejected("key with the lowest bit of a t1 coefficient flipped", &bad_pk, &message, &sig);
        let mut bad_pk = pk;
        bad_pk[T1.start + rng.below(T1.len())] ^= 1 << rng.below(8);
        tally.rejected("key with a flipped bit in t1", &bad_pk, &message, &sig);

        // The hint of a valid signature: list i of positions is hint[ends[i - 1]..ends[i]].
        let hint = &sig[HINT];
        let ends: [usize; K] = core::array::from_fn(|i| usize::from(hint[OMEGA + i]));
        let used = ends[K - 1];
        // Positions out of order: two neighbours of one list swapped, and one position repeated.
        let neighbours: Vec<usize> = (1..used).filter(|at| !ends.contains(at)).collect();
        if !neighbours.is_empty() {
            let at = neighbours[rng.below(neighbours.len())];
            let mut bad = sig;
            bad.swap(HINT.start + at - 1, HINT.start + at);
            tally.rejected("hint positions out of order", &pk, &message, &bad);
            let at = neighbours[rng.below(neighbours.len())];
            let mut bad = sig;
            bad[HINT.start + at] = bad[HINT.start + at - 1];
            tally.rejected("hint position repeated", &pk, &message, &bad);
        }
        // Offsets out of range: an end offset above OMEGA, an end offset below the one before it, a non-zero
        // byte after the last list, and a last list that runs one byte further than the signer wrote.
        let mut bad = sig;
        bad[HINT.start + OMEGA + rng.below(K)] = (OMEGA + 1 + rng.below(255 - OMEGA)) as u8;
        tally.rejected("hint end offset above omega", &pk, &message, &bad);
        let after_non_empty: Vec<usize> = (1..K).filter(|&i| ends[i - 1] > 0).collect();
        if !after_non_empty.is_empty() {
            let i = after_non_empty[rng.below(after_non_empty.len())];
            let mut bad = sig;
            bad[HINT.start + OMEGA + i] = rng.below(ends[i - 1]) as u8;
            tally.rejected("hint end offset going backwards", &pk, &message, &bad);
        }
        if used < OMEGA {
            let mut bad = sig;
            bad[HINT.start + used + rng.below(OMEGA - used)] = 1 + rng.below(255) as u8;
            tally.rejected("hint with a non-zero byte after the lists", &pk, &message, &bad);
            let mut bad = sig;
            bad[HINT.start + OMEGA + K - 1] = (used + 1) as u8;
            tally.rejected("hint with the last list one byte longer", &pk, &message, &bad);
        }

        // z with every bit set: in all four polynomials, in one polynomial, in one coefficient.
        let mut bad = sig;
        bad[Z].fill(0xff);
        tally.rejected("z all 0xff", &pk, &message, &bad);
        let mut bad = sig;
        let polynomial = Z.start + 576 * rng.below(4);
        bad[polynomial..polynomial + 576].fill(0xff);
        tally.rejected("one polynomial of z all 0xff", &pk, &message, &bad);
        let mut bad = sig;
        let bit = 18 * rng.below(4 * 256);
        for bit in bit..bit + 18 {
            bad[Z.start + bit / 8] |= 1 << (bit % 8);
        }
        tally.rejected("one coefficient of z all ones", &pk, &message, &bad);

        other_pk = pk;
    }

    let comparisons: usize = tally.0.values().map(|&(count, _)| count).sum();
    let accepted: usize = tally.0.values().map(|&(_, accepted)| accepted).sum();
    assert_eq!(tally.0["valid signature"], (PAIRS_PER_TEST, PAIRS_PER_TEST));
    assert_eq!(client_shaped, PAIRS_PER_TEST.div_ceil(4));
    let mut lines = format!(
        "differential seed {seed:#x}: {PAIRS_PER_TEST} pairs of key and message ({client_shaped} with the client's \
         1,356-byte message), {comparisons} comparisons with fips204, all equal; {accepted} inputs accepted by both"
    );
    for (case, (count, accepted)) in &tally.0 {
        lines.push_str(&format!("\n    {case}: {count} compared, {accepted} accepted"));
    }
    println!("{lines}");
}

#[test]
fn differential_1() {
    differential(0x2026_1126_0000_0001);
}

#[test]
fn differential_2() {
    differential(0x2026_1126_0000_0002);
}

#[test]
fn differential_3() {
    differential(0x2026_1126_0000_0003);
}

#[test]
fn differential_4() {
    differential(0x2026_1126_0000_0004);
}

#[test]
fn differential_5() {
    differential(0x2026_1126_0000_0005);
}
