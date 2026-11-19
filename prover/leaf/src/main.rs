//! L5 leaf L0' v2 (2026-10-31): L0' (the S5 leaf relation, spec §16.3 over the 198-byte `PI_bytes`, layout 2, in the
//! configuration the kernel layer B verifies) with two changes:
//! - change 1, C4a for every periodic column: the byte-pair table's 2 columns and the SHA-512 table's 123 columns are
//!   committed as those tables' preprocessed traces (`air.rs`, `sha.rs`), under the one key commitment that already
//!   holds the field-operation program. No periodic column remains. The program digest is computed as in S5 and
//!   equals S5's;
//! - change 2, next-row subset openings: the batch prover and verifier are `p3_batch_stark_c3n` (the C3 copy of
//!   p3-batch-stark plus code/l5-leaf-l0p2-20261031/p3-batch-stark-c3n.diff). Each table opens at zeta*g only the main,
//!   preprocessed and permutation columns that its AIR's symbolic constraints read at the next row; the prover and the
//!   verifier each derive the sets from the AIR, never from the proof.
//! Everything else is L0''s: Poseidon2-16 with eight-element digests, a width-16 rate-8 duplex challenger, cap height 5,
//! blowup 2^6, 43 queries, arity at most 4, HidingFriPcs with 8 random codewords and 8-element salts, no grinding, C3,
//! and a deterministic key generation whose preprocessed commitment is the verifying key (`vk.json`). The transcript
//! prefix keeps S5's four absorptions with v2 values: a new domain separator, the AIR digest over the changed sources,
//! and a descriptor extended by the C3n layout tag and the two new preprocessed widths.
//! Research configuration (verifier_version 0x80000007 is not allocated; the witness generator is variable-time).
//! loop-internal self-review; not independently reviewed.
//!
//! Modes (each its own process): prove --out DIR | prove-c3 --out DIR | verify --dir DIR |
//! controls --dir DIR --c3-dir DIR --out DIR | breakdown PROOF OUT.json [METRICS.json] |
//! breakdown-c3 PROOF OUT.json [METRICS.json] | shape --out OUT.json | count --dir DIR --c3-dir DIR --out OUT.json
#![recursion_limit = "256"]

mod air;
mod air_shape;
mod instance;
mod keccak;
mod program;
mod sha;
mod size_accounting;
// Pipeline (code/pq-proof-pipeline-20261101): L0' v2's proof for a given statement.
mod pipeline;

#[path = "../../memory_io.rs"]
mod memory_io;
use memory_io as fs;
use std::{io::Write, path::Path, sync::Arc, time::Instant};
use std::panic::{AssertUnwindSafe, catch_unwind};

use p3_batch_stark_c3n::{BatchProof, CommonData, NextRowColumns, OmittedFill, ProverData, StarkInstance,
    next_row_columns_for_batch, prove_batch, prove_batch_with_next_row_columns, verify_batch,
    verify_batch_with_next_row_columns};
use p3_challenger::{CanObserve, DuplexChallenger};
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::{Field, PrimeCharacteristicRing, PrimeField32, extension::BinomialExtensionField};
use p3_fri::{FriParameters, HidingFriPcs};
use p3_koala_bear::{KoalaBear as F, Poseidon2KoalaBear, default_koalabear_poseidon2_16};
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::MerkleTreeHidingMmcs;
use p3_symmetric::{MerkleCap, PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::StarkConfig;
use rand::{SeedableRng, rngs::{StdRng, SysRng}};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use tiny_keccak::{Hasher, Keccak};

use air::{Ag1Air, BytePairAir, FieldOpAir, KeccakTableAir, ShaAir};
use num_bigint::BigUint;
use p3_keccak_air::{NUM_KECCAK_COLS, output_limb};
use program::{Ckd, EcOverride, HEIGHT, LIMBS, PAIR_HEIGHT, PUBLIC_BLOCKS, col};

pub type EF = BinomialExtensionField<F, 8>;
pub type Perm = Poseidon2KoalaBear<16>;
pub type Hash = PaddingFreeSponge<Perm, 16, 8, 8>;
pub type Compress = TruncatedPermutation<Perm, 2, 8, 16>;
pub type Mmcs = MerkleTreeHidingMmcs<<F as Field>::Packing, <F as Field>::Packing, Hash, Compress, StdRng, 2, 8, 8>;
pub type ChMmcs = ExtensionMmcs<F, EF, Mmcs>;
pub type Pcs = HidingFriPcs<F, Radix2DitParallel<F>, Mmcs, ChMmcs, StdRng>;
pub type Challenger = DuplexChallenger<F, Perm, 16, 8>;
/// One configuration type serves all three batch libraries (stock, C3, C3n): they use p3-uni-stark's `StarkConfig`.
pub type Config = StarkConfig<Pcs, EF, Challenger>;
pub type Cap = MerkleCap<F, [F; 8]>;

const DOMAIN: &[u8] = b"PQ-MIGRATE-RESEARCH-L5-LEAF-L0P-v2";
const AIR_LABEL: &[u8] = b"PQ-MIGRATE-L5-LEAF-L0P-AIR-v2";
/// The salts of the public preprocessed tree come from an RNG seeded with Keccak-256 of this label, the AIR digest and
/// the program digest, so that the verifying key is a deterministic function of the program.
const SALT_SEED_LABEL: &[u8] = b"PQ-MIGRATE-L5-LEAF-L0P-PREPROCESSED-SALT-SEED-v2";
pub const QUERIES: usize = 43;
pub const LOG_BLOWUP: usize = 6;
pub const MAX_LOG_ARITY: usize = 2;
pub const LOG_FINAL_POLY_LEN: usize = 0;
pub const CAP_HEIGHT: usize = 5;
pub const RANDOM_CODEWORDS: usize = 8;
pub const SALT_ELEMS: usize = 8;
pub const DIGEST_ELEMS: usize = 8;
/// The batch layout's tag in the descriptor: C3 (one tree for the quotient chunks and the randomization polynomials)
/// with next-row subset openings (C3n). L0' v1 had 3 (C3).
const LAYOUT_C3N: usize = 4;
pub const REVIEW: &str = "loop-internal self-review; not independently reviewed";
pub const TIER: &str = "research measurement on a candidate configuration (real-backend component tier)";
const AIR_SOURCES: [&[u8]; 4] = [include_bytes!("air.rs"), include_bytes!("program.rs"), include_bytes!("keccak.rs"), include_bytes!("sha.rs")];
/// S5's program digest (99342283:results/ag1-stack-20261028/data/relation-p1-run/controls.json, params.program_digest).
const S5_PROGRAM_DIGEST: &str = "b5c607936d9fbed32ed393b767e67dbd76d2a0ffe8454317bd17b16916aa9b0a";
pub const TABLES: [&str; 4] = ["FieldOp", "BytePair", "Keccak", "Sha"];

/// The transcript prefix as the verifier (or, for prover-side controls, the prover) builds it: honest, or one of its
/// four absorptions substituted or omitted (S5's set, unchanged).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Binding { Expected, WrongDomain, WrongAirDigest, WrongDescriptor, WrongProgram, NoDomain, NoAirDigest, NoDescriptor, NoProgram }
const SUBSTITUTED: [Binding; 4] = [Binding::WrongDomain, Binding::WrongAirDigest, Binding::WrongDescriptor, Binding::WrongProgram];
const OMITTED: [Binding; 4] = [Binding::NoDomain, Binding::NoAirDigest, Binding::NoDescriptor, Binding::NoProgram];

pub fn keccak256(parts: &[&[u8]]) -> [u8; 32] {
    let mut h = Keccak::v256();
    for p in parts { h.update(p); }
    let mut out = [0; 32];
    h.finalize(&mut out);
    out
}
pub fn hex(bytes: &[u8]) -> String { bytes.iter().map(|b| format!("{b:02x}")).collect() }
fn air_digest() -> [u8; 32] {
    let mut parts: Vec<&[u8]> = vec![AIR_LABEL];
    parts.extend(AIR_SOURCES);
    keccak256(&parts)
}
/// S5's 22 entries with L0''s values (the last marks the unsound variant, as in S5), then L0''s additions (Poseidon2
/// width, sponge rate, digest elements, Merkle cap height, the layout tag, the field-operation preprocessed width), then
/// v2's: the byte-pair and SHA-512 preprocessed widths.
fn descriptor(canonical_bits: bool) -> Vec<usize> {
    vec![1, 8, 8, LOG_FINAL_POLY_LEN, RANDOM_CODEWORDS, LOG_BLOWUP, QUERIES, MAX_LOG_ARITY, 0, 0, 0, 0, HEIGHT, col::WIDTH, PAIR_HEIGHT,
         PUBLIC_BLOCKS * LIMBS, keccak::HEIGHT, NUM_KECCAK_COLS, keccak::PI_BYTES, sha::HEIGHT, sha::WIDTH, canonical_bits as usize,
         16, 8, DIGEST_ELEMS, CAP_HEIGHT, LAYOUT_C3N, program::per::NUM, program::pair_col::WIDTH - 1, sha::NUM_PERIODIC]
}
pub fn degrees() -> Vec<usize> {
    [HEIGHT, PAIR_HEIGHT, keccak::HEIGHT, sha::HEIGHT].iter().map(|h| h.trailing_zeros() as usize + 1).collect()
}
/// Keccak-256 of the program, computed exactly as S5 computes it: every column of the field-operation program, then
/// the byte-pair table's and the SHA-512 table's columns (S5's periodic columns, all preprocessed in v2), in table order.
fn program_digest(airs: &[Ag1Air]) -> [u8; 32] {
    let mut h = Keccak::v256();
    for a in airs {
        let cols = match a { Ag1Air::FieldOp(x) => &x.program, Ag1Air::BytePair(x) => &x.program, Ag1Air::Sha(x) => &x.program, Ag1Air::Keccak(_) => continue };
        for c in cols.iter() { for v in c { h.update(&v.to_le_bytes()); } }
    }
    let mut out = [0; 32];
    h.finalize(&mut out);
    out
}
fn os_rng() -> StdRng { StdRng::try_from_rng(&mut SysRng).expect("operating-system entropy") }
pub fn peak_rss_kib() -> Option<u64> {
    let status = fs::read_to_string("/proc/self/status").ok()?;
    status.lines().find(|l| l.starts_with("VmHWM:"))?.split_whitespace().nth(1)?.parse().ok()
}
pub fn event(value: Value) { println!("{value}"); std::io::stdout().flush().unwrap(); }
pub fn save(out: &Path, name: &str, bytes: &[u8]) {
    memory_io::write_new(&out.join(name), bytes).unwrap();
}
fn observe_bytes<C: CanObserve<F>>(c: &mut C, bytes: &[u8]) {
    c.observe(F::from_usize(bytes.len()));
    for &b in bytes { c.observe(F::from_u8(b)); }
}
fn seeded(seed: &[u8; 32], k: u8) -> StdRng { StdRng::from_seed(keccak256(&[seed, &[k]])) }

/// The PCS of L0'. `rngs` are the input MMCS's salt RNG, the FRI MMCS's salt RNG and the PCS's own RNG (random rows,
/// random codewords, randomization polynomials).
pub fn pcs_with(rngs: [StdRng; 3]) -> Pcs {
    let [input_rng, fri_rng, pcs_rng] = rngs;
    let perm = default_koalabear_poseidon2_16();
    let mmcs = |rng| Mmcs::new(Hash::new(perm.clone()), Compress::new(perm.clone()), CAP_HEIGHT, rng);
    let fri = FriParameters { log_blowup: LOG_BLOWUP, log_final_poly_len: LOG_FINAL_POLY_LEN, max_log_arity: MAX_LOG_ARITY,
        num_queries: QUERIES, batch_proof_of_work_bits: 0, commit_proof_of_work_bits: 0, query_proof_of_work_bits: 0,
        mmcs: ChMmcs::new(mmcs(fri_rng)) };
    HidingFriPcs::new(Radix2DitParallel::default(), mmcs(input_rng), fri, RANDOM_CODEWORDS, pcs_rng)
}

/// The four prefix absorptions (S5's): domain, AIR digest, descriptor, program digest, honest or as `binding` says.
fn absorb_prefix<C: CanObserve<F>>(c: &mut C, binding: Binding, program: &[u8; 32], canonical_bits: bool) {
    if binding != Binding::NoDomain {
        observe_bytes(c, if binding == Binding::WrongDomain { b"PQ-MIGRATE-RESEARCH-WRONG" } else { DOMAIN });
    }
    let mut digest = air_digest();
    if binding == Binding::WrongAirDigest { digest[0] ^= 1; }
    if binding != Binding::NoAirDigest { observe_bytes(c, &digest); }
    let mut d = descriptor(canonical_bits);
    if binding == Binding::WrongDescriptor { d[6] += 1; }
    if binding != Binding::NoDescriptor {
        c.observe(F::from_usize(d.len()));
        for v in d { c.observe(F::from_usize(v)); }
    }
    let mut prog = *program;
    if binding == Binding::WrongProgram { prog[31] ^= 1; }
    if binding != Binding::NoProgram { observe_bytes(c, &prog); }
}

fn challenger(binding: Binding, program: &[u8; 32], canonical_bits: bool) -> Challenger {
    let mut c = Challenger::new(default_koalabear_poseidon2_16());
    absorb_prefix(&mut c, binding, program, canonical_bits);
    c
}

/// The challenger's Poseidon2-16 permutation with a call counter: each call is one duplexing of the transcript, one
/// row of the kernel layer B's transcript region (budget.py's duplex rule). Measurement only (mode `count`).
#[derive(Clone)]
pub struct CountingPerm {
    inner: Perm,
    calls: Arc<std::sync::atomic::AtomicUsize>,
    /// Calls on packed lanes (the grinding search only; zero bits of grinding everywhere, so expected to stay 0).
    packed_calls: Arc<std::sync::atomic::AtomicUsize>,
}
/// One generic impl (the challenger's scalar state and the grinding search's packed lanes): a call on `[F; 16]` is a
/// duplexing; any other state type is a packed grinding call.
impl<T: Clone + 'static> p3_symmetric::Permutation<T> for CountingPerm
where
    Perm: p3_symmetric::Permutation<T>,
{
    fn permute_mut(&self, input: &mut T) {
        let counter = if std::any::TypeId::of::<T>() == std::any::TypeId::of::<[F; 16]>() { &self.calls } else { &self.packed_calls };
        counter.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        p3_symmetric::Permutation::permute_mut(&self.inner, input);
    }
}
impl<T: Clone + 'static> p3_symmetric::CryptographicPermutation<T> for CountingPerm where Perm: p3_symmetric::CryptographicPermutation<T> {}
pub type CountChallenger = DuplexChallenger<F, CountingPerm, 16, 8>;
/// L0''s configuration with the counting challenger: the same PCS, the same transcript, permutation calls counted.
pub type CountConfig = StarkConfig<Pcs, EF, CountChallenger>;

/// The proving or verifying configuration: operating-system randomness for the hiding PCS.
fn config(binding: Binding, program: &[u8; 32], canonical_bits: bool) -> Config {
    StarkConfig::new(pcs_with([os_rng(), os_rng(), os_rng()]), challenger(binding, program, canonical_bits))
}

/// The key-generation configuration: the same PCS with every RNG seeded from `seed`. Only the input MMCS's salts are
/// drawn by key generation (`HidingFriPcs::commit_preprocessing` pads the public trace with zero rows and adds no
/// random codewords), so the preprocessed commitment is a deterministic function of the program and the seed.
fn keygen_config(seed: &[u8; 32]) -> Config {
    StarkConfig::new(pcs_with([seeded(seed, 0), seeded(seed, 1), seeded(seed, 2)]), Challenger::new(default_koalabear_poseidon2_16()))
}
fn salt_seed(program: &[u8; 32]) -> [u8; 32] { keccak256(&[SALT_SEED_LABEL, &air_digest(), program]) }

pub fn config_record() -> Value {
    json!({"field": "KoalaBear, p = 2^31 - 2^24 + 1", "challenge_field": "BinomialExtensionField<KoalaBear, 8> (EF8)",
        "hash": "Poseidon2KoalaBear<16> with default_koalabear_poseidon2_16 constants: PaddingFreeSponge<_, 16, 8, 8> (rate 8, 8-element digest) for leaves, TruncatedPermutation<_, 2, 8, 16> for nodes",
        "mmcs": "MerkleTreeHidingMmcs<Packing, Packing, Hash, Compress, StdRng, 2, 8, 8> (binary, 8-element digests, 8-element salts)",
        "cap_height": CAP_HEIGHT, "challenger": "DuplexChallenger<KoalaBear, Poseidon2KoalaBear<16>, 16, 8> (width 16, rate 8)",
        "pcs": "HidingFriPcs<_, Radix2DitParallel, Mmcs, ExtensionMmcs<_, EF8, Mmcs>, StdRng>",
        "random_codewords": RANDOM_CODEWORDS, "salt_elements": SALT_ELEMS, "digest_elements": DIGEST_ELEMS,
        "log_blowup": LOG_BLOWUP, "num_queries": QUERIES, "max_log_arity": MAX_LOG_ARITY, "log_final_poly_len": LOG_FINAL_POLY_LEN,
        "pow_bits": {"fri_batch": 0, "fri_commit": 0, "fri_query": 0, "lookup": 0, "ood": 0},
        "batch_layout": "C3n (p3_batch_stark_c3n): C3 (the quotient chunks and each instance's randomization polynomial in one tree) with next-row subset openings",
        "preprocessed": "C4a for every program column: the field-operation table's 51, the byte-pair table's 2 and the SHA-512 table's 123; deterministic salts (seeded RNG) since the data is public",
        "periodic_columns": 0,
        "domain_separator": String::from_utf8_lossy(DOMAIN), "air_digest_label": String::from_utf8_lossy(AIR_LABEL),
        "salt_seed_label": String::from_utf8_lossy(SALT_SEED_LABEL)})
}

pub struct Built {
    pub airs: Vec<Ag1Air>,
    public: Vec<Vec<F>>,
    prog: program::Program,
    pub digest: [u8; 32],
    pub canonical_bits: bool,
    /// The message the Keccak table hashes: x || y of k5's point as the program computes it.
    message: [u8; 64],
    /// The statement's PI_bytes (the Keccak table's public values).
    pi: [u8; keccak::PI_BYTES],
    /// The 24 SHA-512 compressions of the witness's derivation.
    comps: Vec<sha::Compression>,
    /// The SHA-512 table's program (`sha::periodic`), its preprocessed trace in v2.
    sha_program: Arc<Vec<Vec<u64>>>,
}

/// One changed cell of an honest trace (malicious-prover controls).
#[derive(Clone, Copy, Debug)]
enum Fault { FieldOp(usize, usize), Keccak(usize, usize), Sha(usize, usize) }

/// A statement's witness and claim (S5's, unchanged).
#[derive(Clone, Default)]
struct Witness {
    seed: Option<[u8; 64]>,
    path: Option<[u32; 5]>,
    il: Option<(usize, BigUint)>,
    ec: Option<EcOverride>,
    address: Option<[u8; 20]>,
    nonce: Option<u64>,
    pi_edit: Option<PiEdit>,
}

/// A change to a PI_bytes field outside the relation (cross-statement and fresh-coin controls, S5).
#[derive(Clone, Copy, Debug)]
enum PiEdit {
    /// expiry (bytes 129..137, big-endian u64) plus one, the cross-statement field of the 2026-10-27 corpus.
    ExpiryPlusOne,
    /// bit 0 of the last byte of fee_sponsor (bytes 170..190), the fresh-coin field of that corpus.
    FeeSponsorBit,
}

fn be32(x: &BigUint) -> [u8; 32] {
    let bytes = x.to_bytes_be();
    let mut out = [0u8; 32];
    out[32 - bytes.len()..].copy_from_slice(&bytes);
    out
}

fn message_of(point: &program::Point) -> [u8; 64] {
    let mut m = [0u8; 64];
    m[..32].copy_from_slice(&be32(&point.0));
    m[32..].copy_from_slice(&be32(&point.1));
    m
}

pub fn build() -> Built {
    let b = build_with(&Witness::default(), false);
    let d = instance::derive();
    let ckd = Ckd { il: d.il.clone(), force_key: None };
    assert_eq!(program::derive_keys(&ckd), d.keys.to_vec(), "key arithmetic differs from the reference derivation");
    assert_eq!(hex(&keccak::address(&b.message)), instance::EXPECTED_ADDRESS_HEX, "address differs from the research fixture");
    assert_eq!(hex(&b.digest), S5_PROGRAM_DIGEST, "the program differs from S5's");
    b
}

/// A program and witness for a statement; `lenient` gives a false statement its best-effort witness (S5's).
fn build_with(w: &Witness, lenient: bool) -> Built {
    let seed = w.seed.unwrap_or_else(instance::seed);
    let path = w.path.unwrap_or(instance::PATH);
    let (comps, il) = sha::derive(&seed, &path);
    if sha::fits_shape(&path) {
        assert_eq!(il, instance::derive_with(&seed, &path).il.to_vec(), "SHA-table I_L values differ from the hmac crate");
    } else {
        assert!(lenient, "a path outside the shape is a negative control");
    }
    let mut il: [BigUint; 6] = il.try_into().unwrap();
    if let Some((j, v)) = &w.il { il[*j] = v.clone(); }
    let mut prog = program::build(&Ckd { il, force_key: None }, w.ec.as_ref(), lenient);
    prog.index_first = std::array::from_fn(|s| if s == 0 { 0 } else { (path[s - 1] >> 24) as u64 });
    let message = message_of(&prog.pubkey);
    let address = w.address.unwrap_or_else(|| keccak::address(&message));
    let sha_program = Arc::new(sha::periodic());
    let canonical_bits = true;
    let airs = vec![
        Ag1Air::FieldOp(FieldOpAir { program: Arc::new(program::periodic(&prog)), p_limbs: program::p_limbs(),
            n_limbs: program::n_limbs(), canonical_bits }),
        Ag1Air::BytePair(BytePairAir { program: Arc::new(program::pair_periodic()) }),
        Ag1Air::Keccak(KeccakTableAir),
        Ag1Air::Sha(ShaAir { program: sha_program.clone() }),
    ];
    let mut pi = keccak::pi_bytes(&address, w.nonce.unwrap_or(0));
    match w.pi_edit {
        Some(PiEdit::ExpiryPlusOne) => {
            let expiry = u64::from_be_bytes(pi[129..137].try_into().unwrap()) + 1;
            pi[129..137].copy_from_slice(&expiry.to_be_bytes());
        }
        Some(PiEdit::FeeSponsorBit) => pi[189] ^= 1,
        None => {}
    }
    let public = vec![vec![], vec![], pi.iter().map(|&v| F::from_u8(v)).collect(), vec![]];
    let digest = program_digest(&airs);
    Built { airs, public, prog, digest, canonical_bits, message, pi, comps, sha_program }
}

/// Key generation with a given salt seed: the preprocessed commitment (C4a, now three matrices) and the packed lookups.
fn keygen_with(b: &Built, seed: &[u8; 32]) -> ProverData<Config> {
    ProverData::from_airs_and_degrees(&keygen_config(seed), &b.airs, &degrees()).expect("key generation")
}
/// L0''s key generation: the salt seed is derived from the AIR digest and the program digest.
pub fn keygen(b: &Built) -> ProverData<Config> { keygen_with(b, &salt_seed(&b.digest)) }
/// The same key through the C3 copy (the old-layout proofs): its key generation is the C3n copy's, unchanged.
fn keygen_c3(b: &Built) -> p3_batch_stark_c3::ProverData<Config> {
    p3_batch_stark_c3::ProverData::from_airs_and_degrees(&keygen_config(&salt_seed(&b.digest)), &b.airs, &degrees())
        .expect("C3 key generation")
}

fn preprocessed_cap(common: &CommonData<Config>) -> &Cap {
    &common.preprocessed.as_ref().expect("C4a: a preprocessed commitment").commitment
}
fn cap_values(cap: &Cap) -> Vec<Vec<u32>> {
    cap.roots().iter().map(|d| d.iter().map(|x| x.as_canonical_u32()).collect()).collect()
}

/// The next-row column sets of the research statement's tables, derived from the AIRs and the key's lookups.
pub fn next_rows(b: &Built, common: &CommonData<Config>) -> Vec<NextRowColumns> {
    next_row_columns_for_batch(b.airs.iter(), common)
}
pub fn next_rows_record(rows: &[NextRowColumns]) -> Value {
    json!(rows.iter().zip(TABLES).map(|(r, t)| json!({"table": t,
        "main_width": r.main_width, "main_next_row_columns": r.main,
        "preprocessed_width": r.preprocessed_width, "preprocessed_next_row_columns": r.preprocessed,
        "permutation_ef8_width": r.permutation_width, "permutation_next_row_ef8_columns": r.permutation})).collect::<Vec<_>>())
}

/// The verifying key's record: what a verifier of L0' v2 (B included) pins. The commitment is the 2^5-entry cap of the
/// public preprocessed tree; the rest identifies the statement's prefix and shape.
fn vk_record(b: &Built, common: &CommonData<Config>) -> Value {
    let g = common.preprocessed.as_ref().expect("C4a: a preprocessed commitment");
    let enc = postcard::to_allocvec(&g.commitment).unwrap();
    let instances: Vec<Value> = g.instances.iter().zip(TABLES).map(|(m, t)| match m {
        Some(m) => json!({"table": t, "matrix_index": m.matrix_index, "width": m.width, "degree_bits": m.degree_bits}),
        None => Value::Null,
    }).collect();
    json!({"schema": "l5-leaf-l0p2/vk/v1", "review": REVIEW,
        "preprocessed": {"commitment_postcard_hex": hex(&enc), "commitment_keccak256": hex(&keccak256(&[&enc])),
            "cap_height": g.commitment.height(), "cap_roots": g.commitment.num_roots(), "cap": cap_values(&g.commitment),
            "matrix_to_instance": g.matrix_to_instance, "instances": instances,
            "salt_seed": hex(&salt_seed(&b.digest)),
            "salt_seed_derivation": "Keccak-256(salt_seed_label || air_digest || program_digest); the input MMCS's salt RNG is StdRng::from_seed(Keccak-256(salt_seed || 0x00))"},
        "air_digest": hex(&air_digest()), "program_digest": hex(&b.digest), "descriptor": descriptor(b.canonical_bits),
        "domain": String::from_utf8_lossy(DOMAIN), "degree_bits": degrees(), "public_values": keccak::PI_BYTES,
        "next_row_columns": next_rows_record(&next_rows(b, common)),
        "configuration": config_record()})
}

/// The four traces of a statement, with an optional malicious-prover fault.
fn traces(b: &Built, fault: Option<Fault>) -> ([RowMajorMatrix<F>; 4], f64) {
    let start = Instant::now();
    let field_fault = match fault { Some(Fault::FieldOp(r, c)) => Some((r, c)), _ => None };
    let keccak_fault = match fault { Some(Fault::Keccak(r, c)) => Some((r, c)), _ => None };
    let sha_fault = match fault { Some(Fault::Sha(r, c)) => Some((r, c)), _ => None };
    let (t, mult) = program::traces(&b.prog, field_fault);
    let main = RowMajorMatrix::new(t.into_iter().map(F::from_u64).collect(), col::WIDTH);
    let pair = RowMajorMatrix::new(mult.into_iter().map(F::from_u64).collect(), program::pair_col::WIDTH);
    let kec = keccak::trace::<F>(&b.message, keccak_fault);
    let sha = sha::trace::<F>(&b.comps, &b.sha_program, sha_fault);
    ([main, pair, kec, sha], start.elapsed().as_secs_f64() * 1e3)
}

/// Prove with the prover's transcript prefix built as `binding` says (prover-side controls, S5) and the given key.
/// `layout`: the next-row column sets (None: derived, as `prove_batch` does).
fn prove_with_layout(b: &Built, fault: Option<Fault>, binding: Binding, data: &ProverData<Config>,
                     layout: Option<&[NextRowColumns]>) -> (BatchProof<Config>, f64, f64) {
    let ([main, pair, kec, sha], gen_ms) = traces(b, fault);
    let cfg = config(binding, &b.digest, b.canonical_bits);
    let traces = [&main, &pair, &kec, &sha];
    let instances = StarkInstance::new_multiple(&b.airs, &traces, &b.public);
    let start = Instant::now();
    let proof = match layout {
        None => prove_batch(&cfg, &instances, data).expect("prover"),
        Some(l) => prove_batch_with_next_row_columns(&cfg, &instances, data, l).expect("prover"),
    };
    (proof, gen_ms, start.elapsed().as_secs_f64() * 1e3)
}
fn prove_with(b: &Built, fault: Option<Fault>, binding: Binding, data: &ProverData<Config>) -> (BatchProof<Config>, f64, f64) {
    prove_with_layout(b, fault, binding, data, None)
}

fn verify_proof(b: &Built, binding: Binding, proof: &BatchProof<Config>, public: &[Vec<F>], common: &CommonData<Config>) -> Result<(), String> {
    if proof.degree_bits != degrees() { return Err(format!("shape: degree_bits {:?}", proof.degree_bits)); }
    let cfg = config(binding, &b.digest, b.canonical_bits);
    verify_batch(&cfg, &b.airs, proof, public, common).map_err(|e| format!("backend: {e:?}"))
}
/// The verifier with caller-given next-row column sets and fill of the omitted entries (controls only).
fn verify_with_layout(b: &Built, proof: &BatchProof<Config>, common: &CommonData<Config>, layout: &[NextRowColumns],
                      fill: OmittedFill) -> Result<(), String> {
    if proof.degree_bits != degrees() { return Err(format!("shape: degree_bits {:?}", proof.degree_bits)); }
    let cfg = config(Binding::Expected, &b.digest, b.canonical_bits);
    verify_batch_with_next_row_columns(&cfg, &b.airs, proof, &b.public, common, layout, fill).map_err(|e| format!("backend: {e:?}"))
}

pub fn decode_strict(encoded: &[u8]) -> Result<BatchProof<Config>, String> {
    let (proof, rest) = postcard::take_from_bytes::<BatchProof<Config>>(encoded).map_err(|e| format!("decode: {e:?}"))?;
    if !rest.is_empty() { return Err("trailing bytes".into()); }
    Ok(proof)
}

fn len<T: serde::Serialize>(value: &T) -> usize { postcard::to_allocvec(value).unwrap().len() }

/// S5's coarse breakdown, unchanged (the size accounting checks it against its exact partition).
pub fn breakdown(proof: &BatchProof<Config>) -> Value {
    let (random_openings, fri) = &proof.opening_proof;
    let input_values: usize = fri.input_openings.iter().map(|o| len(&o.opened_values)).sum();
    let input_paths: usize = fri.input_openings.iter().map(|o| len(&o.opening_proof)).sum();
    let fold_values: usize = fri.commit_phase_openings.iter().map(|s| len(&s.sibling_values)).sum();
    let fold_paths: usize = fri.commit_phase_openings.iter().map(|s| len(&s.opening_proof)).sum();
    json!({"total": len(proof), "commitments": len(&proof.commitments), "ood_opened_values": len(&proof.opened_values),
        "random_codeword_openings": len(random_openings), "input_openings_values": input_values,
        "input_openings_merkle": input_paths, "fold_sibling_values": fold_values, "fold_merkle": fold_paths,
        "fold_rounds": fri.commit_phase_openings.len(), "input_rounds": fri.input_openings.len(),
        "lookup_terminals": len(&proof.lookup_terminals)})
}

fn params(b: &Built) -> Value {
    let rows = &b.prog.ckd_rows;
    json!({"component": "narrow ownership relation (spec §16.3) over the 198-byte PI_bytes (layout 2), path indices private with the five-level shape (S5's relation, unchanged); L0' v2: every program column preprocessed (C4a for all, no periodic column), Poseidon2-16 with eight-element digests, cap height 5, blowup 2^6, 43 queries, C3 batch layout with next-row subset openings (C3n)",
        "path_shape": "44', 60', a' = a + 2^31, c in {0, 1}, i < 2^31",
        "field_op_width": col::WIDTH, "field_op_height": HEIGHT, "field_op_preprocessed_width": program::per::NUM,
        "byte_pair_preprocessed_width": program::pair_col::WIDTH - 1, "sha_preprocessed_width": sha::NUM_PERIODIC,
        "periodic_columns": 0,
        "program_rows": b.prog.rows.len(),
        "key_arithmetic_rows": rows.tie_start - rows.start, "tie_rows": rows.keccak_start - rows.tie_start,
        "keccak_input_rows": rows.data_start - rows.keccak_start, "hmac_data_rows": b.prog.rows.len() - rows.data_start,
        "canonical_bits": b.canonical_bits, "sha_width": sha::WIDTH, "sha_height": sha::HEIGHT, "sha_compressions": sha::COMPRESSIONS,
        "keccak_width": NUM_KECCAK_COLS, "keccak_height": keccak::HEIGHT, "address": hex(&keccak::address(&b.message)),
        "byte_pair_height": PAIR_HEIGHT, "public_values": PUBLIC_BLOCKS * LIMBS + keccak::PI_BYTES, "pi_bytes": hex(&b.pi),
        "research_verifier_version": format!("{:#010x}", keccak::RESEARCH_VERIFIER_VERSION), "profile": "L0' v2",
        "queries": QUERIES, "log_blowup": LOG_BLOWUP, "max_log_arity": MAX_LOG_ARITY, "log_final_poly_len": LOG_FINAL_POLY_LEN,
        "extension_degree": 8, "hash": "Poseidon2 width 16, 8-element digest", "cap_height": CAP_HEIGHT,
        "random_codewords": RANDOM_CODEWORDS, "salt_elements": SALT_ELEMS, "grinding_bits": 0, "batch_layout": "C3n",
        "air_digest": hex(&air_digest()), "program_digest": hex(&b.digest), "descriptor": descriptor(b.canonical_bits)})
}

/// The verifying key as the fresh-process verifier and the controls use it: key generation recomputed from the
/// program, compared with the pinned record (`vk.json` of the run).
fn checked_key(b: &Built, dir: &Path) -> (ProverData<Config>, f64, Result<(), String>) {
    let start = Instant::now();
    let data = keygen(b);
    let ms = start.elapsed().as_secs_f64() * 1e3;
    let pinned: Value = serde_json::from_slice(&fs::read(dir.join("vk.json")).expect("vk.json")).expect("vk.json is JSON");
    let ours = vk_record(b, &data.common);
    let same = pinned["preprocessed"] == ours["preprocessed"] && pinned["air_digest"] == ours["air_digest"]
        && pinned["program_digest"] == ours["program_digest"] && pinned["descriptor"] == ours["descriptor"]
        && pinned["next_row_columns"] == ours["next_row_columns"];
    (data, ms, if same { Ok(()) } else { Err("the recomputed verifying key differs from the pinned vk.json".into()) })
}

/// EF8 claims the PCS absorbs for a proof (the OOD values the proof carries plus 8 per random-codeword matrix-point).
fn claims(p: &BatchProof<Config>) -> usize {
    let ood: usize = p.opened_values.instances.iter().map(|x| {
        let o = &x.base_opened_values;
        o.trace_local.len() + o.trace_next.as_ref().map_or(0, Vec::len) + o.quotient_chunks.len() * 8 + o.random.as_ref().map_or(0, Vec::len)
            + o.preprocessed.as_ref().map_or(0, |p| p.local.len() + p.next.as_ref().map_or(0, Vec::len))
            + x.permutation_local.len() + x.permutation_next.len()
    }).sum();
    let codewords: usize = p.opening_proof.0.iter().flat_map(|r| r.iter()).flat_map(|m| m.iter()).map(Vec::len).sum();
    ood + codewords
}

fn prove_mode(out: &Path) {
    fs::create_dir(out).expect("fresh output directory required");
    let start = Instant::now();
    let b = build();
    let build_ms = start.elapsed().as_secs_f64() * 1e3;
    let start = Instant::now();
    let data = keygen(&b);
    let keygen_ms = start.elapsed().as_secs_f64() * 1e3;
    let start = Instant::now();
    let layout = next_rows(&b, &data.common);
    let derive_ms = start.elapsed().as_secs_f64() * 1e3;
    let rss_before = peak_rss_kib();
    let (proof, gen_ms, prove_ms) = prove_with(&b, None, Binding::Expected, &data);
    let rss_after = peak_rss_kib();
    let start = Instant::now();
    verify_proof(&b, Binding::Expected, &proof, &b.public, &data.common).expect("honest proof must verify");
    let verify_ms = start.elapsed().as_secs_f64() * 1e3;
    let encoded = postcard::to_allocvec(&proof).unwrap();
    save(out, "l0p2.postcard", &encoded);
    let vk = vk_record(&b, &data.common);
    save(out, "vk.json", &serde_json::to_vec_pretty(&vk).unwrap());
    let metrics = json!({"schema": "l5-leaf-l0p2/prove/v1", "review": REVIEW, "tier": TIER, "n": 1, "params": params(&b),
        "configuration": config_record(), "proof_bytes": encoded.len(), "proof_keccak256": hex(&keccak256(&[&encoded])),
        "proof_sha256": sha256_hex(&encoded),
        "vk_preprocessed_commitment_keccak256": vk["preprocessed"]["commitment_keccak256"],
        "next_row_columns": next_rows_record(&layout), "claims_ef8": claims(&proof),
        "program_and_witness_ms": build_ms, "keygen_ms": keygen_ms, "next_row_derivation_ms": derive_ms, "trace_ms": gen_ms,
        "prove_ms": prove_ms, "verify_in_process_ms": verify_ms, "degree_bits": proof.degree_bits,
        "peak_rss_kib_before_prove": rss_before, "peak_rss_kib_after_prove": rss_after,
        "rayon_threads": std::env::var("RAYON_NUM_THREADS").ok(), "breakdown": breakdown(&proof)});
    save(out, "metrics.json", &serde_json::to_vec_pretty(&metrics).unwrap());
    event(json!({"phase": "prove_done", "metrics": metrics}));
}

/// The same statement and the same key proven with the C3 copy (every next-row column of a reading table opened, as
/// in L0' v1): change 1 alone, and the old-layout proof of the cross-layout controls.
fn prove_c3_mode(out: &Path) {
    fs::create_dir(out).expect("fresh output directory required");
    let b = build();
    let start = Instant::now();
    let key = keygen_c3(&b);
    let keygen_ms = start.elapsed().as_secs_f64() * 1e3;
    let c3n_key = keygen(&b);
    assert_eq!(key.common.preprocessed.as_ref().unwrap().commitment, *preprocessed_cap(&c3n_key.common), "the C3 and C3n keys commit alike");
    drop(c3n_key);
    let ([main, pair, kec, sha], gen_ms) = traces(&b, None);
    let cfg = config(Binding::Expected, &b.digest, b.canonical_bits);
    let traces = [&main, &pair, &kec, &sha];
    let instances = p3_batch_stark_c3::StarkInstance::new_multiple(&b.airs, &traces, &b.public);
    let rss_before = peak_rss_kib();
    let start = Instant::now();
    let proof = p3_batch_stark_c3::prove_batch(&cfg, &instances, &key).expect("C3 prover");
    let prove_ms = start.elapsed().as_secs_f64() * 1e3;
    let rss_after = peak_rss_kib();
    drop(instances);
    let start = Instant::now();
    p3_batch_stark_c3::verify_batch(&config(Binding::Expected, &b.digest, b.canonical_bits), &b.airs, &proof, &b.public, &key.common)
        .expect("the C3 proof must verify with the C3 verifier");
    let verify_ms = start.elapsed().as_secs_f64() * 1e3;
    let encoded = postcard::to_allocvec(&proof).unwrap();
    save(out, "l0p2-c3.postcard", &encoded);
    let as_c3n = decode_strict(&encoded).expect("the C3 proof decodes as the C3n type");
    let metrics = json!({"schema": "l5-leaf-l0p2/prove-c3/v1", "review": REVIEW, "tier": TIER, "n": 1, "params": params(&b),
        "what": "L0' v2's statement and key (change 1) proven with p3_batch_stark_c3 (L0' v1's batch layout: every next-row column of a reading table opened); the old-layout proof",
        "proof_bytes": encoded.len(), "proof_sha256": sha256_hex(&encoded), "proof_keccak256": hex(&keccak256(&[&encoded])),
        "claims_ef8": claims(&as_c3n), "keygen_ms": keygen_ms, "trace_ms": gen_ms, "prove_ms": prove_ms,
        "verify_in_process_ms_c3_verifier": verify_ms, "degree_bits": proof.degree_bits,
        "peak_rss_kib_before_prove": rss_before, "peak_rss_kib_after_prove": rss_after,
        "rayon_threads": std::env::var("RAYON_NUM_THREADS").ok(), "breakdown": breakdown(&as_c3n)});
    save(out, "metrics.json", &serde_json::to_vec_pretty(&metrics).unwrap());
    event(json!({"phase": "prove_c3_done", "metrics": metrics}));
}

fn verify_mode(dir: &Path) {
    let start = Instant::now();
    let b = build();
    let build_ms = start.elapsed().as_secs_f64() * 1e3;
    let (data, keygen_ms, key) = checked_key(&b, dir);
    key.expect("the verifying key");
    let encoded = fs::read(dir.join("l0p2.postcard")).unwrap();
    let start = Instant::now();
    let proof = decode_strict(&encoded).expect("strict decoding");
    let decode_ms = start.elapsed().as_secs_f64() * 1e3;
    let start = Instant::now();
    let r = verify_proof(&b, Binding::Expected, &proof, &b.public, &data.common);
    let verify_ms = start.elapsed().as_secs_f64() * 1e3;
    event(json!({"phase": "separate_verify", "accepted": r.is_ok(), "error": r.as_ref().err(), "decode_ms": decode_ms,
        "verify_ms": verify_ms, "keygen_and_vk_check_ms": keygen_ms, "program_and_witness_ms": build_ms,
        "proof_bytes": encoded.len(), "proof_keccak256": hex(&keccak256(&[&encoded])), "proof_sha256": sha256_hex(&encoded),
        "peak_rss_kib": peak_rss_kib(),
        "rayon_threads": std::env::var("RAYON_NUM_THREADS").ok()}));
    if r.is_err() { std::process::exit(2); }
}

/// A verification (or a prover-side case) under the harness: a rejection is an `Err`; a panic anywhere is recorded
/// separately and never counts as a rejection.
fn guarded(f: impl FnOnce() -> Result<(), String>) -> (Result<(), String>, bool) {
    match catch_unwind(AssertUnwindSafe(f)) {
        Ok(r) => (r, false),
        Err(p) => {
            let msg = p.downcast_ref::<String>().cloned().or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string()));
            (Err(format!("panic: {}", msg.unwrap_or_default())), true)
        }
    }
}

pub fn sha256_hex(bytes: &[u8]) -> String { hex(&Sha256::digest(bytes)) }

type Outcome = ((Result<(), String>, bool), Option<String>);
/// A prover-side case under the harness: prove, record the SHA-256 of the proof's encoding, then verify.
fn proved(prove: impl FnOnce() -> BatchProof<Config>, check: impl FnOnce(&BatchProof<Config>) -> Result<(), String>) -> Outcome {
    let mut hash = None;
    let outcome = guarded(|| {
        let p = prove();
        hash = Some(sha256_hex(&postcard::to_allocvec(&p).unwrap()));
        check(&p)
    });
    (outcome, hash)
}

fn controls_mode(dir: &Path, c3_dir: &Path, out: &Path) {
    fs::create_dir(out).expect("fresh output directory required");
    let started = Instant::now();
    let b = build();
    let (data, _, key) = checked_key(&b, dir);
    key.expect("the verifying key");
    let common = &data.common;
    let layout = next_rows(&b, common);
    let encoded = fs::read(dir.join("l0p2.postcard")).unwrap();
    let mut proof = decode_strict(&encoded).unwrap();
    verify_proof(&b, Binding::Expected, &proof, &b.public, common).expect("positive control");
    let mut controls: Vec<Value> = vec![];
    // Each control records its verdict, the verifier's error, and for a prover-side case the SHA-256 of the proof it
    // produced (`proof_sha256`; the proofs themselves are not kept).
    let record_h = |controls: &mut Vec<Value>, family: &str, case: String, expect_reject: bool, outcome: (Result<(), String>, bool),
                    proof_sha256: Option<Value>| {
        let (r, panicked) = outcome;
        let rejected = r.is_err() && !panicked;
        let as_expected = if expect_reject { rejected } else { r.is_ok() };
        let entry = json!({"family": family, "case": case, "expected": if expect_reject {"reject"} else {"accept"},
            "rejected": rejected, "panicked": panicked, "as_expected": as_expected, "error": r.err(), "proof_sha256": proof_sha256});
        event(json!({"phase": "control", "control": entry}));
        controls.push(entry);
    };
    let record = |controls: &mut Vec<Value>, family: &str, case: String, expect_reject: bool, outcome: (Result<(), String>, bool)| {
        record_h(controls, family, case, expect_reject, outcome, None)
    };
    let hash_of = |p: &BatchProof<Config>| Some(json!(sha256_hex(&postcard::to_allocvec(p).unwrap())));
    let v = |binding: Binding, p: &BatchProof<Config>, public: &[Vec<F>]| guarded(|| verify_proof(&b, binding, p, public, common));
    // 1. PI_bytes: each of the 198 bytes with bit 0 flipped (S5).
    for i in 0..keccak::PI_BYTES {
        let mut wrong = b.public.clone();
        wrong[2][i] = F::from_u8(b.pi[i] ^ 1);
        record(&mut controls, "s5", format!("pi_byte{i}_bit0_flipped"), true, v(Binding::Expected, &proof, &wrong));
    }
    // 2. Transcript prefix, each absorption substituted and each omitted, on the verifier's side and on the prover's
    //    side (S5).
    for binding in SUBSTITUTED.into_iter().chain(OMITTED) {
        record(&mut controls, "s5", format!("verifier_transcript_{binding:?}"), true, v(binding, &proof, &b.public));
    }
    for binding in SUBSTITUTED.into_iter().chain(OMITTED) {
        let (outcome, h) = proved(|| prove_with(&b, None, binding, &data).0, |p| verify_proof(&b, Binding::Expected, p, &b.public, common));
        record_h(&mut controls, "s5", format!("prover_transcript_{binding:?}"), true, outcome, h.map(Value::from));
    }
    // 3. Malicious prover: one changed cell of an otherwise honest trace (S5's 30 faults).
    let arith_row = |n: usize| b.prog.rows.iter().enumerate().filter(|(_, r)| r.kind == program::Kind::Arith).nth(n).unwrap().0;
    let input_row = |n: usize| b.prog.rows.iter().enumerate().filter(|(_, r)| r.kind == program::Kind::Input).nth(n).unwrap().0;
    let bit_row = |n: usize| b.prog.rows.iter().enumerate().filter(|(_, r)| r.bit).nth(n).unwrap().0;
    let rows = &b.prog.ckd_rows;
    let comp = |c: usize, t: usize| c * sha::ROWS_PER_COMPRESSION + t;
    let faults = [
        ("result_limb_of_an_operation", Fault::FieldOp(arith_row(1000), col::R + 3)),
        ("operand_limb_of_an_operation", Fault::FieldOp(arith_row(4000), col::A + 17)),
        ("quotient_limb", Fault::FieldOp(arith_row(7000), col::Q)),
        ("carry_byte", Fault::FieldOp(arith_row(9000), col::CL + 30)),
        ("scalar_bit_input", Fault::FieldOp(input_row(100), col::R)),
        ("read_count", Fault::FieldOp(5, col::MULT)),
        ("ckd_il_slack_limb", Fault::FieldOp(rows.slack_il[2], col::R + 5)),
        ("ckd_key_slack_limb", Fault::FieldOp(rows.slack_key[3], col::R + 9)),
        ("ckd_inverse_limb", Fault::FieldOp(rows.inverse[1], col::R)),
        ("ckd_add_quotient_limb", Fault::FieldOp(rows.add[4], col::Q)),
        ("tie_horner_quotient_limb", Fault::FieldOp(rows.horner[100], col::Q)),
        ("tie_check_result_limb", Fault::FieldOp(rows.tie_check[1], col::R)),
        ("keccak_input_coordinate_slack_limb", Fault::FieldOp(rows.slack_coord[0], col::R + 4)),
        ("keccak_input_row_flag", Fault::FieldOp(rows.kec_row, col::KEC)),
        ("il_row_flag", Fault::FieldOp(rows.il_rows[3], col::KIL)),
        ("hmac_data_row_flag", Fault::FieldOp(rows.data_rows[1], col::KD)),
        ("data_row_index_byte", Fault::FieldOp(rows.data_rows[2], col::IDX0)),
        ("y_parity_bit_input", Fault::FieldOp(rows.parity_bit[0], col::R)),
        ("keccak_a_prime_bit", Fault::Keccak(5, keccak::A_PRIME + 7)),
        ("keccak_export_flag", Fault::Keccak(keccak::EXPORT_ROW, keccak::EXPORT)),
        ("keccak_output_limb", Fault::Keccak(keccak::EXPORT_ROW, output_limb(8))),
        ("sha_a_bit", Fault::Sha(comp(7, 5), sha::A_BITS + 3)),
        ("sha_w0_bit_of_a_ckd_key_block", Fault::Sha(comp(4, 0), sha::W0_BITS + 2)),
        ("sha_linked_chaining_input_limb", Fault::Sha(comp(1, 0), sha::HIN + 5)),
        ("sha_data_block_limb", Fault::Sha(comp(5, 0), sha::WIN + 2)),
        ("sha_free_index_bit_of_a_message_block", Fault::Sha(comp(13, 4), sha::W0_BITS + sha::BC_FIRST + 8 + 6)),
        ("sha_hmac_output_limb", Fault::Sha(comp(3, sha::ROUNDS), sha::HOUT + 1)),
        ("sha_digest_flag", Fault::Sha(comp(1, sha::ROUNDS), sha::M_DOUT)),
        ("leaf_scalar_bit_input", Fault::FieldOp(bit_row(512 + 100), col::R)),
        ("sha_master_key_block_limb", Fault::Sha(comp(0, 0), sha::WIN + 1)),
    ];
    for (name, fault) in faults {
        let (outcome, h) = proved(|| prove_with(&b, Some(fault), Binding::Expected, &data).0,
                                  |p| verify_proof(&b, Binding::Expected, p, &b.public, common));
        record_h(&mut controls, "s5", format!("witness_fault_{name}"), true, outcome, h.map(Value::from));
    }
    // 4. Statements, each proven with its best-effort witness and verified against its own claim (S5). A statement
    //    never changes the program, so it uses the research instance's verifying key.
    let d = instance::derive();
    let n = program::n();
    let p = program::p();
    let mut other_seed = instance::seed();
    other_seed[0] ^= 1;
    let (h44, h60, h7) = (44 | 1 << 31, 60 | 1 << 31, 7 | 1 << 31);
    let other_path = [h44, h60, h7, 1, 1];
    let largest = [h44, h60, u32::MAX, 0, (1 << 31) - 1];
    let unhardened_a = [h44, h60, 7, 1, 0];
    let c_two = [h44, h60, h7, 2, 0];
    let hardened_i = [h44, h60, h7, 1, 1 << 31];
    let first_45 = [45 | 1 << 31, h60, h7, 1, 0];
    let shift = ((&n - 1u8) * p.modpow(&(&n - 2u8), &n)) % &n;
    let shifted_bits = EcOverride { slot: 0, scalar: &d.keys[3] + 1u8, shift };
    let statements: Vec<(&str, Witness, bool)> = vec![
        ("another_seed_its_own_address", Witness { seed: Some(other_seed), ..Default::default() }, false),
        ("another_seed_claiming_the_fixture_address", Witness { seed: Some(other_seed), address: Some(d.address), ..Default::default() }, true),
        ("another_path_its_own_address", Witness { path: Some(other_path), ..Default::default() }, false),
        ("largest_a_and_i_c_zero_its_own_address", Witness { path: Some(largest), ..Default::default() }, false),
        ("a_without_the_hardened_bit_its_own_address", Witness { path: Some(unhardened_a), ..Default::default() }, true),
        ("c_equal_to_2_its_own_address", Witness { path: Some(c_two), ..Default::default() }, true),
        ("i_with_the_hardened_bit_its_own_address", Witness { path: Some(hardened_i), ..Default::default() }, true),
        ("first_index_45_hardened_its_own_address", Witness { path: Some(first_45), ..Default::default() }, true),
        ("p_shifted_scalar_bits_of_k3", Witness { ec: Some(shifted_bits), address: Some(d.address), ..Default::default() }, true),
        ("field_op_il_differs_from_the_hmac_output", Witness { il: Some((3, &d.il[3] + 1u8)), address: Some(d.address), ..Default::default() }, true),
    ];
    for (name, w, expect_reject) in statements {
        let s = build_with(&w, true);
        assert_eq!(s.digest, b.digest, "a statement must not change the program");
        let (outcome, h) = proved(|| prove_with(&s, None, Binding::Expected, &data).0,
                                  |p| verify_proof(&b, Binding::Expected, p, &s.public, common));
        record_h(&mut controls, "s5", format!("statement_{name}"), expect_reject, outcome, h.map(Value::from));
    }
    // Another statement differing only in migration_nonce, and the cross-statement pair for expiry + 1 (S5).
    let s = build_with(&Witness { nonce: Some(1), ..Default::default() }, false);
    let (other, _, _) = prove_with(&s, None, Binding::Expected, &data);
    record_h(&mut controls, "s5", "statement_another_migration_nonce_its_own_pi".into(), false, v(Binding::Expected, &other, &s.public), hash_of(&other));
    record_h(&mut controls, "s5", "cross_statement_proof_for_nonce_1_against_the_research_pi".into(), true, v(Binding::Expected, &other, &b.public), hash_of(&other));
    let s = build_with(&Witness { pi_edit: Some(PiEdit::ExpiryPlusOne), ..Default::default() }, false);
    let (other, _, _) = prove_with(&s, None, Binding::Expected, &data);
    record_h(&mut controls, "s5", "statement_expiry_plus_one_its_own_pi".into(), false, v(Binding::Expected, &other, &s.public), hash_of(&other));
    record_h(&mut controls, "s5", "cross_statement_proof_for_expiry_plus_one_against_the_research_pi".into(), true, v(Binding::Expected, &other, &b.public), hash_of(&other));
    // Fresh coins (S5): a second honest proof and one for PI_bytes differing only in fee_sponsor both verify, and the
    // three proofs' commitment sets all differ. Necessary for hiding; not a hiding argument.
    let (again, _, _) = prove_with(&b, None, Binding::Expected, &data);
    let s = build_with(&Witness { pi_edit: Some(PiEdit::FeeSponsorBit), ..Default::default() }, false);
    let (sponsor, _, _) = prove_with(&s, None, Binding::Expected, &data);
    let commitments = |p: &BatchProof<Config>| postcard::to_allocvec(&p.commitments).unwrap();
    let (c0, c1, c2) = (commitments(&proof), commitments(&again), commitments(&sponsor));
    let outcome = guarded(|| verify_proof(&b, Binding::Expected, &again, &b.public, common)
        .and_then(|_| verify_proof(&b, Binding::Expected, &sponsor, &s.public, common))
        .and_then(|_| if c0 != c1 && c0 != c2 && c1 != c2 { Ok(()) } else { Err("two commitment sets are equal".into()) }));
    let pair = json!([hash_of(&again), hash_of(&sponsor)]);
    record_h(&mut controls, "s5", "fresh_coins_three_commitment_sets_differ".into(), false, outcome, Some(pair));
    // 5. Shape and codec (S5).
    let correct = proof.degree_bits.clone();
    for (name, delta) in [("degree_bits_minus_one", -1i64), ("degree_bits_plus_one", 1)] {
        proof.degree_bits[0] = (correct[0] as i64 + delta) as usize;
        record(&mut controls, "s5", name.into(), true, v(Binding::Expected, &proof, &b.public));
    }
    proof.degree_bits = correct;
    let mut longer = encoded.clone();
    longer.push(0);
    record(&mut controls, "s5", "trailing_byte".into(), true, guarded(|| decode_strict(&longer).map(|_| ())));
    record(&mut controls, "s5", "truncated_by_one_byte".into(), true, guarded(|| decode_strict(&encoded[..encoded.len() - 1]).map(|_| ())));
    let s5_count = controls.len();

    // 6. L0' v1's own controls, adapted to v2 (family `l0p`): the verifying key, the preprocessed openings, C3, the
    //    stock layout.
    //    (a) the verifier's key: a cap entry changed; a key generated with another salt seed (same program).
    {
        let mut tampered = keygen(&b);
        let g = tampered.common.preprocessed.as_mut().unwrap();
        let mut roots = g.commitment.roots().to_vec();
        roots[7][3] += F::ONE;
        g.commitment = Cap::new(roots);
        record(&mut controls, "l0p", "vk_preprocessed_cap_entry_changed".into(), true,
               guarded(|| verify_proof(&b, Binding::Expected, &proof, &b.public, &tampered.common)));
        let other = keygen_with(&b, &keccak256(&[b"another salt seed"]));
        assert_ne!(preprocessed_cap(&other.common), preprocessed_cap(common));
        record(&mut controls, "l0p", "vk_preprocessed_other_salt_seed".into(), true,
               guarded(|| verify_proof(&b, Binding::Expected, &proof, &b.public, &other.common)));
        //  (b) the prover's key: another salt seed (its own consistent commitment and data, same program).
        let (outcome, h) = proved(|| prove_with(&b, None, Binding::Expected, &other).0,
                                  |p| verify_proof(&b, Binding::Expected, p, &b.public, common));
        record_h(&mut controls, "l0p", "prover_preprocessed_other_salt_seed".into(), true, outcome, h.map(Value::from));
    }
    //  (c) the prover commits a changed program: one constant limb on a padding row (row 16,000, where no selector is
    //      set, so the honest trace still satisfies every constraint), with its own consistent commitment, under the
    //      honest prefix; and the same changed data opened under the honest commitment.
    {
        let pad_row = 16_000usize;
        assert!(pad_row >= b.prog.rows.len(), "row 16,000 is a padding row");
        let mut changed_prog: Vec<Vec<u64>> = match &b.airs[0] { Ag1Air::FieldOp(a) => a.program.as_ref().clone(), _ => unreachable!() };
        changed_prog[program::per::CONST_LIMB][pad_row] = 77;
        let mut changed = build_with(&Witness::default(), false);
        if let Ag1Air::FieldOp(a) = &mut changed.airs[0] { a.program = Arc::new(changed_prog); }
        // The honest prefix: the program digest stays the honest one, so only the preprocessed data differ.
        changed.digest = b.digest;
        let changed_key = keygen(&changed);
        assert_ne!(preprocessed_cap(&changed_key.common), preprocessed_cap(common));
        let (outcome, h) = proved(|| prove_with(&changed, None, Binding::Expected, &changed_key).0,
                                  |p| verify_proof(&b, Binding::Expected, p, &b.public, common));
        record_h(&mut controls, "l0p", "prover_preprocessed_program_changed_own_commitment".into(), true, outcome, h.map(Value::from));
        let mut mixed = keygen(&changed);
        mixed.common.preprocessed.as_mut().unwrap().commitment = preprocessed_cap(common).clone();
        let (outcome, h) = proved(|| prove_with(&changed, None, Binding::Expected, &mixed).0,
                                  |p| verify_proof(&b, Binding::Expected, p, &b.public, common));
        record_h(&mut controls, "l0p", "prover_preprocessed_program_changed_under_the_honest_commitment".into(), true, outcome, h.map(Value::from));
    }
    //  (d) the proof's preprocessed values: an OOD value at zeta; a next-row opening of the preprocessed trace, which
    //      v2 does not open at zeta*g (v1: a value at zeta*g changed); an opened value in the preprocessed round's FRI
    //      input opening (batch 2 under C3).
    {
        let mut p = decode_strict(&encoded).unwrap();
        p.opened_values.instances[0].base_opened_values.preprocessed.as_mut().unwrap().local[program::per::CONST_LIMB] += EF::ONE;
        record(&mut controls, "l0p", "ood_preprocessed_local_value_changed".into(), true, v(Binding::Expected, &p, &b.public));
        let mut p = decode_strict(&encoded).unwrap();
        let pre = p.opened_values.instances[0].base_opened_values.preprocessed.as_mut().unwrap();
        pre.next = Some(pre.local.clone());
        record(&mut controls, "l0p", "ood_preprocessed_next_value_added".into(), true, v(Binding::Expected, &p, &b.public));
        let mut p = decode_strict(&encoded).unwrap();
        p.opening_proof.1.input_openings[2].opened_values[0][0][program::per::ID_A] += F::ONE;
        record(&mut controls, "l0p", "fri_input_opening_preprocessed_value_changed".into(), true, v(Binding::Expected, &p, &b.public));
        //  (e) C3: the randomization polynomial's OOD value; a separate randomization commitment added.
        let mut p = decode_strict(&encoded).unwrap();
        p.opened_values.instances[2].base_opened_values.random.as_mut().unwrap()[0] += EF::ONE;
        record(&mut controls, "l0p", "c3_randomization_ood_value_changed".into(), true, v(Binding::Expected, &p, &b.public));
        let mut p = decode_strict(&encoded).unwrap();
        p.commitments.random = Some(p.commitments.quotient_chunks.clone());
        record(&mut controls, "l0p", "c3_separate_randomization_commitment_added".into(), true, v(Binding::Expected, &p, &b.public));
    }
    //  (f) Cross-layout with the stock layout: a stock-layout batch proof of the same statement (stock p3-batch-stark,
    //      the same key) against the C3n verifier; the honest C3n proof against the stock verifier. The stock proof is
    //      first accepted by the stock verifier.
    {
        let stock_key = p3_batch_stark::ProverData::<Config>::from_airs_and_degrees(&keygen_config(&salt_seed(&b.digest)), &b.airs, &degrees())
            .expect("stock key generation");
        let same_cap = stock_key.common.preprocessed.as_ref().unwrap().commitment == *preprocessed_cap(common);
        let ([main, pair, kec, sha_t], _) = traces(&b, None);
        let traces = [&main, &pair, &kec, &sha_t];
        let instances = p3_batch_stark::StarkInstance::new_multiple(&b.airs, &traces, &b.public);
        let cfg = config(Binding::Expected, &b.digest, b.canonical_bits);
        let stock = p3_batch_stark::prove_batch(&cfg, &instances, &stock_key).expect("stock prover");
        drop(instances);
        let stock_bytes = postcard::to_allocvec(&stock).unwrap();
        let stock_ok = guarded(|| p3_batch_stark::verify_batch(&config(Binding::Expected, &b.digest, b.canonical_bits), &b.airs, &stock,
            &b.public, &stock_key.common).map_err(|e| format!("backend: {e:?}"))
            .and_then(|_| if same_cap { Ok(()) } else { Err("stock key generation gave another commitment".into()) }));
        let stock_hash = Some(json!(sha256_hex(&stock_bytes)));
        record_h(&mut controls, "l0p", "stock_layout_proof_stock_verifier_same_key".into(), false, stock_ok, stock_hash.clone());
        let as_c3n = decode_strict(&stock_bytes).expect("the stock proof decodes as the C3n type");
        record_h(&mut controls, "l0p", "c3n_verifier_rejects_the_stock_layout_proof".into(), true, v(Binding::Expected, &as_c3n, &b.public), stock_hash);
        let as_stock = postcard::from_bytes::<p3_batch_stark::BatchProof<Config>>(&encoded).expect("the C3n proof decodes as the stock type");
        let outcome = guarded(|| p3_batch_stark::verify_batch(&config(Binding::Expected, &b.digest, b.canonical_bits), &b.airs, &as_stock,
            &b.public, &stock_key.common).map_err(|e| format!("backend: {e:?}")));
        record(&mut controls, "l0p", "stock_verifier_rejects_the_c3n_proof".into(), true, outcome);
    }
    let l0p_count = controls.len() - s5_count;

    // 7. v2's own controls (family `l0p2`).
    //  (a) Change 1, the new preprocessed bindings: the SHA-512 program changed on a padding row (row 2,000, past the
    //      24 compressions, where every selector is zero, so the honest trace still satisfies every constraint) with
    //      its own commitment under the honest prefix; the byte-pair and SHA-512 preprocessed values at zeta; a value of
    //      the SHA-512 matrix in the preprocessed round's FRI input opening.
    {
        let pad_row = 2_000usize;
        assert!(pad_row >= sha::COMPRESSIONS * sha::ROWS_PER_COMPRESSION, "row 2,000 is a SHA-512 padding row");
        let mut changed_prog: Vec<Vec<u64>> = b.sha_program.as_ref().clone();
        assert_eq!(changed_prog[sha::P_K][pad_row], 0);
        changed_prog[sha::P_K][pad_row] = 77;
        let mut changed = build_with(&Witness::default(), false);
        let changed_prog = Arc::new(changed_prog);
        if let Ag1Air::Sha(a) = &mut changed.airs[3] { a.program = changed_prog.clone(); }
        changed.sha_program = changed_prog;
        changed.digest = b.digest;
        let changed_key = keygen(&changed);
        assert_ne!(preprocessed_cap(&changed_key.common), preprocessed_cap(common));
        let (outcome, h) = proved(|| prove_with(&changed, None, Binding::Expected, &changed_key).0,
                                  |p| verify_proof(&b, Binding::Expected, p, &b.public, common));
        record_h(&mut controls, "l0p2", "prover_sha_program_changed_own_commitment".into(), true, outcome, h.map(Value::from));
        for (inst, column, name) in [(1usize, 0usize, "byte_pair"), (3, sha::P_ROUND, "sha")] {
            let mut p = decode_strict(&encoded).unwrap();
            p.opened_values.instances[inst].base_opened_values.preprocessed.as_mut().unwrap().local[column] += EF::ONE;
            record(&mut controls, "l0p2", format!("ood_preprocessed_local_value_changed_{name}"), true, v(Binding::Expected, &p, &b.public));
        }
        let mut p = decode_strict(&encoded).unwrap();
        p.opening_proof.1.input_openings[2].opened_values[0][2][sha::P_ROUND] += F::ONE;
        record(&mut controls, "l0p2", "fri_input_opening_preprocessed_value_changed_sha".into(), true, v(Binding::Expected, &p, &b.public));
    }
    //  (b) Change 2, the next-row openings on the wire: an extra and a missing next-row value (Keccak's main trace; the
    //      field-operation permutation trace), tampered next-row values (Keccak and SHA-512 main, the field-operation
    //      permutation), and next-row openings of a table that reads no next row (the field-operation main trace: an
    //      empty and a full-width opening; its preprocessed trace is covered by (d)).
    {
        let edit = |f: &dyn Fn(&mut BatchProof<Config>)| { let mut p = decode_strict(&encoded).unwrap(); f(&mut p); p };
        let cases: Vec<(&str, BatchProof<Config>)> = vec![
            ("keccak_next_row_opening_extra", edit(&|p| p.opened_values.instances[2].base_opened_values.trace_next.as_mut().unwrap().push(EF::ZERO))),
            ("keccak_next_row_opening_missing", edit(&|p| { p.opened_values.instances[2].base_opened_values.trace_next.as_mut().unwrap().pop(); })),
            ("keccak_next_row_value_tampered", edit(&|p| p.opened_values.instances[2].base_opened_values.trace_next.as_mut().unwrap()[0] += EF::ONE)),
            ("sha_next_row_value_tampered", edit(&|p| p.opened_values.instances[3].base_opened_values.trace_next.as_mut().unwrap()[0] += EF::ONE)),
            ("field_op_next_row_opening_added_empty", edit(&|p| p.opened_values.instances[0].base_opened_values.trace_next = Some(vec![]))),
            ("field_op_next_row_opening_added_full_width", edit(&|p| {
                let w = p.opened_values.instances[0].base_opened_values.trace_local.len();
                p.opened_values.instances[0].base_opened_values.trace_next = Some(vec![EF::ZERO; w]);
            })),
            ("permutation_next_row_opening_extra", edit(&|p| p.opened_values.instances[0].permutation_next.push(EF::ZERO))),
            ("permutation_next_row_opening_missing", edit(&|p| { p.opened_values.instances[0].permutation_next.pop(); })),
            ("permutation_next_row_value_tampered", edit(&|p| p.opened_values.instances[0].permutation_next[0] += EF::ONE)),
        ];
        for (name, p) in cases {
            record(&mut controls, "l0p2", name.into(), true, v(Binding::Expected, &p, &b.public));
        }
    }
    //  (c) The old full-opening layout (L0' v1's: p3_batch_stark_c3) against the new verifier, and the reverse: the C3
    //      proof of this statement with the same key (stage provec3) is accepted by the C3 verifier and rejected by the
    //      C3n verifier; the C3n proof is rejected by the C3 verifier.
    {
        let c3_bytes = fs::read(c3_dir.join("l0p2-c3.postcard")).expect("the C3 proof (stage provec3)");
        let c3_key = keygen_c3(&b);
        let c3_proof = postcard::from_bytes::<p3_batch_stark_c3::BatchProof<Config>>(&c3_bytes).expect("C3 proof");
        let c3_hash = Some(json!(sha256_hex(&c3_bytes)));
        let ok = guarded(|| p3_batch_stark_c3::verify_batch(&config(Binding::Expected, &b.digest, b.canonical_bits), &b.airs, &c3_proof,
            &b.public, &c3_key.common).map_err(|e| format!("backend: {e:?}")));
        record_h(&mut controls, "l0p2", "c3_layout_proof_c3_verifier_same_key".into(), false, ok, c3_hash.clone());
        let as_c3n = decode_strict(&c3_bytes).expect("the C3 proof decodes as the C3n type");
        record_h(&mut controls, "l0p2", "c3n_verifier_rejects_the_c3_full_opening_proof".into(), true, v(Binding::Expected, &as_c3n, &b.public), c3_hash);
        let as_c3 = postcard::from_bytes::<p3_batch_stark_c3::BatchProof<Config>>(&encoded).expect("the C3n proof decodes as the C3 type");
        let outcome = guarded(|| p3_batch_stark_c3::verify_batch(&config(Binding::Expected, &b.digest, b.canonical_bits), &b.airs, &as_c3,
            &b.public, &c3_key.common).map_err(|e| format!("backend: {e:?}")));
        record(&mut controls, "l0p2", "c3_verifier_rejects_the_c3n_subset_proof".into(), true, outcome);
    }
    //  (d) Provers with other next-row sets (Keccak's main trace; the field-operation permutation trace), each proof
    //      self-consistent: one unread column added, one read column removed, one read column swapped for an unread one,
    //      against the derived verifier; and a removed read column (main; the permutation accumulator) on both sides,
    //      which is the wrong set the derivation exists to prevent: the honest proof fails the constraint check. An
    //      unread column added on both sides is accepted (a superset is the library's behaviour).
    {
        let kec = &layout[2];
        let read = kec.main[0];
        let unread = (0..kec.main_width).find(|c| !kec.main.contains(c)).expect("Keccak has an unread column");
        let with_main = |cols: Vec<usize>| -> Vec<NextRowColumns> {
            let mut l = layout.clone();
            let mut c = cols;
            c.sort_unstable();
            c.dedup();
            l[2].main = c;
            l
        };
        let plus = with_main(kec.main.iter().copied().chain([unread]).collect());
        let minus = with_main(kec.main.iter().copied().filter(|&c| c != read).collect());
        let swapped = with_main(kec.main.iter().copied().filter(|&c| c != read).chain([unread]).collect());
        let mut perm_empty = layout.clone();
        perm_empty[0].permutation = vec![];
        let fo_unread = 0usize;
        let mut fo_plus = layout.clone();
        assert!(fo_plus[0].main.is_empty(), "the field-operation table reads no next row");
        fo_plus[0].main = vec![fo_unread];
        let cases: Vec<(String, Vec<NextRowColumns>, bool, bool)> = vec![
            (format!("prover_keccak_next_row_set_plus_unread_column_{unread}"), plus.clone(), false, true),
            (format!("prover_keccak_next_row_set_minus_read_column_{read}"), minus.clone(), false, true),
            (format!("prover_keccak_next_row_set_read_column_{read}_swapped_for_unread_{unread}"), swapped, false, true),
            (format!("prover_and_verifier_keccak_set_minus_read_column_{read}"), minus, true, true),
            ("prover_and_verifier_field_op_permutation_set_without_the_accumulator".into(), perm_empty, true, true),
            (format!("prover_and_verifier_field_op_set_plus_unread_column_{fo_unread}"), fo_plus, true, false),
        ];
        for (name, l, both, expect_reject) in cases {
            let (outcome, h) = proved(|| prove_with_layout(&b, None, Binding::Expected, &data, Some(&l)).0, |p| {
                if both { verify_with_layout(&b, p, common, &l, OmittedFill::Zero) } else { verify_proof(&b, Binding::Expected, p, &b.public, common) }
            });
            record_h(&mut controls, "l0p2", name, expect_reject, outcome, h.map(Value::from));
        }
    }
    //  (e) The omitted next-row entries are read by no constraint, on the real verification path: the honest proof
    //      verifies with every omitted entry (main, preprocessed, permutation; every table) set to pseudorandom values
    //      instead of zero, for two seeds.
    for seed in [1u64, 0x5eed_c3a1] {
        record(&mut controls, "l0p2", format!("honest_proof_omitted_next_row_entries_pseudorandom_seed_{seed:#x}"), false,
               guarded(|| verify_with_layout(&b, &proof, common, &layout, OmittedFill::Pseudorandom(seed))));
    }
    let all_ok = controls.iter().all(|c| c["as_expected"] == json!(true));
    let panics = controls.iter().filter(|c| c["panicked"] == json!(true)).count();
    let summary = json!({"schema": "l5-leaf-l0p2/controls/v1", "review": REVIEW, "tier": TIER, "params": params(&b),
        "next_row_columns": next_rows_record(&layout),
        "proof_keccak256": hex(&keccak256(&[&encoded])), "controls": controls, "count": controls.len(),
        "s5_corpus_count": s5_count, "l0p_count": l0p_count, "l0p2_count": controls.len() - s5_count - l0p_count, "panics": panics,
        "all_as_expected": all_ok, "elapsed_s": started.elapsed().as_secs_f64(), "peak_rss_kib": peak_rss_kib()});
    save(out, "controls.json", &serde_json::to_vec_pretty(&summary).unwrap());
    event(json!({"phase": "controls_done", "count": summary["count"], "s5": s5_count, "all_as_expected": all_ok, "panics": panics}));
    assert!(all_ok, "a control did not behave as expected");
}

/// Transcript rows that a verifier spends on one proof, measured: the duplexings of its challenger (one Poseidon2-16
/// permutation each), for the prefix and for the batch verifier, on the C3n proof and on the same statement's C3 proof
/// (stage provec3). The kernel layer B replays exactly these duplexings in its transcript region; budget.py models them
/// (the duplex rule on an event list, with S5's measured residual for what is not a claim, a commitment or the final
/// polynomial).
fn count_mode(dir: &Path, c3_dir: &Path, out: &Path) {
    use std::sync::atomic::Ordering::SeqCst;
    assert!(!out.exists(), "refusing to overwrite {}", out.display());
    let b = build();
    let calls = Arc::new(std::sync::atomic::AtomicUsize::new(0));
    let packed_calls = Arc::new(std::sync::atomic::AtomicUsize::new(0));
    let perm = CountingPerm { inner: default_koalabear_poseidon2_16(), calls: calls.clone(), packed_calls: packed_calls.clone() };
    let seed = salt_seed(&b.digest);
    // A fresh seeded configuration per key generation: the PCS's salt RNG advances with each commitment.
    let kcfg = || -> CountConfig {
        StarkConfig::new(pcs_with([seeded(&seed, 0), seeded(&seed, 1), seeded(&seed, 2)]), CountChallenger::new(perm.clone()))
    };
    let key = p3_batch_stark_c3n::ProverData::<CountConfig>::from_airs_and_degrees(&kcfg(), &b.airs, &degrees()).expect("key");
    let key_c3 = p3_batch_stark_c3::ProverData::<CountConfig>::from_airs_and_degrees(&kcfg(), &b.airs, &degrees()).expect("C3 key");
    let reference = keygen(&b);
    assert!(key.common.preprocessed.as_ref().unwrap().commitment == *preprocessed_cap(&reference.common)
        && key_c3.common.preprocessed.as_ref().unwrap().commitment == *preprocessed_cap(&reference.common), "the counting keys commit alike");
    drop(reference);
    let count = |run: &dyn Fn(&CountConfig) -> Result<(), String>| -> (usize, usize, Result<(), String>) {
        calls.store(0, SeqCst);
        let mut ch = CountChallenger::new(perm.clone());
        absorb_prefix(&mut ch, Binding::Expected, &b.digest, b.canonical_bits);
        let prefix = calls.load(SeqCst);
        let cfg: CountConfig = StarkConfig::new(pcs_with([os_rng(), os_rng(), os_rng()]), ch);
        calls.store(0, SeqCst);
        let r = run(&cfg);
        (prefix, calls.load(SeqCst), r)
    };
    let c3n_bytes = fs::read(dir.join("l0p2.postcard")).expect("the C3n proof");
    let c3_bytes = fs::read(c3_dir.join("l0p2-c3.postcard")).expect("the C3 proof");
    let c3n_proof: p3_batch_stark_c3n::BatchProof<CountConfig> = postcard::from_bytes(&c3n_bytes).expect("C3n proof");
    let c3_proof: p3_batch_stark_c3::BatchProof<CountConfig> = postcard::from_bytes(&c3_bytes).expect("C3 proof");
    let (prefix, rows_c3n, r_c3n) = count(&|cfg| p3_batch_stark_c3n::verify_batch(cfg, &b.airs, &c3n_proof, &b.public, &key.common)
        .map_err(|e| format!("{e:?}")));
    let (prefix_c3, rows_c3, r_c3) = count(&|cfg| p3_batch_stark_c3::verify_batch(cfg, &b.airs, &c3_proof, &b.public, &key_c3.common)
        .map_err(|e| format!("{e:?}")));
    assert_eq!(prefix, prefix_c3);
    let claims_c3n = claims(&decode_strict(&c3n_bytes).unwrap());
    let claims_c3 = claims(&decode_strict(&c3_bytes).unwrap());
    let prefix_elements = 1 + DOMAIN.len() + 1 + 32 + 1 + descriptor(b.canonical_bits).len() + 1 + 32;
    let doc = json!({"schema": "l5-leaf-l0p2/transcript-count/v1", "review": REVIEW, "tier": TIER,
        "what": "permutation calls of the verifier's DuplexChallenger<KoalaBear, Poseidon2-16, 16, 8> (one duplexing each: one row of B's transcript region), counted by wrapping the challenger's permutation; the PCS's and the Merkle trees' own hashes are not the challenger's and are not counted",
        "prefix": {"absorbed_elements": prefix_elements, "duplexings_during_absorption": prefix,
                   "note": "the prefix's last partial block is absorbed by the verifier's first duplexing, counted below"},
        "c3n": {"proof_sha256": sha256_hex(&c3n_bytes), "accepted": r_c3n.is_ok(), "error": r_c3n.err(),
                "verifier_duplexings": rows_c3n, "total_transcript_rows": prefix + rows_c3n, "claims_ef8": claims_c3n},
        "c3": {"proof_sha256": sha256_hex(&c3_bytes), "accepted": r_c3.is_ok(), "error": r_c3.err(),
               "verifier_duplexings": rows_c3, "total_transcript_rows": prefix + rows_c3, "claims_ef8": claims_c3},
        "difference_c3n_minus_c3": {"transcript_rows": rows_c3n as i64 - rows_c3 as i64, "claims_ef8": claims_c3n as i64 - claims_c3 as i64},
        "packed_permutation_calls": packed_calls.load(SeqCst)});
    let parent = out.parent().unwrap_or(Path::new("."));
    save(parent, out.file_name().unwrap().to_str().unwrap(), &serde_json::to_vec_pretty(&doc).unwrap());
    event(json!({"phase": "count_done", "doc": doc}));
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    // The library hiding budget, 2 (q + 8 x 2) rows, which the smallest table holds (S5's start-up check).
    assert!(2 * (QUERIES + 16) <= keccak::HEIGHT, "the hiding budget exceeds the Keccak table's rows");
    match args.iter().map(String::as_str).collect::<Vec<_>>().as_slice() {
        ["prove", "--out", out] => prove_mode(Path::new(out)),
        ["prove-c3", "--out", out] => prove_c3_mode(Path::new(out)),
        ["verify", "--dir", dir] => verify_mode(Path::new(dir)),
        ["controls", "--dir", dir, "--c3-dir", c3_dir, "--out", out] => controls_mode(Path::new(dir), Path::new(c3_dir), Path::new(out)),
        ["breakdown", rest @ ..] => size_accounting::cli(rest, false),
        ["breakdown-c3", rest @ ..] => size_accounting::cli(rest, true),
        ["shape", rest @ ..] => air_shape::cli(rest),
        ["count", "--dir", dir, "--c3-dir", c3_dir, "--out", out] => count_mode(Path::new(dir), Path::new(c3_dir), Path::new(out)),
        ["prove-statement", ..] | ["verify-statement", ..] => pipeline::cli(&args.iter().map(String::as_str).collect::<Vec<_>>()),
        _ => panic!("usage: prove --out DIR | prove-c3 --out DIR | verify --dir DIR | controls --dir DIR --c3-dir DIR --out DIR | breakdown PROOF OUT.json [METRICS.json] | breakdown-c3 PROOF OUT.json [METRICS.json] | shape --out OUT.json | count --dir DIR --c3-dir DIR --out OUT.json"),
    }
}
