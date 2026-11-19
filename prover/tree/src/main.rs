//! L5 layer F2 (2026-11-01): the final layer F, made smaller and proven. This binary is F1's with B's side unchanged
//! (B's files byte-identical to F1's: B's key, B's verifier-key digest and B's proofs are F1's) and F's side changed:
//! - (c) F's AIR reads the 14 bus-control values that were pure main copies from their periodic columns
//!   (`fkernel.rs`, `ftracegen.rs`; main width 257), F's LogUp check and prover generate the permutation trace with the
//!   periodic columns (`flcheck.rs`; p3_batch_stark_c3np, C3n plus `periodic_logup.rs`);
//! - (b) F opens its next-row sets by the break-even split rule (`fmodes.rs`: the main trace split, the permutation
//!   trace in full);
//! - (d) F's PCS takes its salts from a per-matrix seed (p3_merkle_tree_ps, the pinned p3-merkle-tree with
//!   `PrgSalts`);
//! - F's proof: `fprove.rs` (prove, fresh-process verify, proof-level controls; the (a) and (d) control modes) and
//!   `fbreakdown.rs` (F's exact byte partition).
//! F's modes: f-compile, f-schedule, f-trace, f-negative, f-controls, f-variants, f-child-variants (F1's, on F2's
//! layout), f-degree, f-salts, f-prove, f-verify, f-proof-controls. F1's description follows.
//!
//! L5 layer F1 (2026-11-01): the first half of the final layer F of the PQ-Migrate migration proof (L5). F verifies the
//! kernel layer B (B2's B for L0' v2), and F's proof is the one that goes on chain under MAX_PROOF_BYTES = 196,608 B.
//! This binary is B2's binary with two changes on B's side and F's modules added:
//! - **B re-proven under the kernel's child tail**: B's FRI parameters are B2's with Merkle cap height 5 (B2: 0) and
//!   maximum FRI arity 4 (B2: 8), blowup 2^6, 43 queries and a final polynomial of 4 coefficients kept, because the
//!   kernel (G1, B1, B2) verifies children with cap height 5 and arity 2 or 4. B's AIR, schedule and compiled program are
//!   B2's (kernel.rs, schedule.rs, compiler.rs byte-identical: the same AIR and program digests); B's key (its
//!   preprocessed commitment, now a cap of 32 digests) and verifier-key digest follow the new parameters.
//! - **F's modules** (`fkernel`, `fschedule`, `ftracegen`, `flcheck`, `fvariants`: B1's periodic-control kernel family,
//!   `fkernel.rs` byte-identical to B1's `kernel.rs`, the others with module paths renamed; `fchild`: B as F's child,
//!   proven with p3_batch_stark_c3; `fmodes`: F's modes). F's control is periodic (F is verified natively), its bus
//!   control values are main columns (p3-lookup reads no periodic column), and F's own proof parameters are the
//!   budget's: 2^14 rows, blowup 2^9, 29 queries, FRI arities [16, 8], final polynomial 2^8, cap height 0, hiding.
//!
//! B's modes (B2's): l0p2-native, compile, schedule, trace, g1b-child, l0p2-child, negative, controls, prove, verify,
//! proof-controls, children, variants. F's modes (fmodes.rs): f-compile, f-schedule, f-trace, f-negative, f-controls,
//! f-variants, f-child-variants.
//! Research measurement; loop-internal self-review; not independently reviewed.
#![recursion_limit = "256"]
#![allow(clippy::too_many_arguments, clippy::type_complexity)]

mod breakdown;
mod child;
mod compiler;
mod kernel;
mod l0p2;
mod lcheck;
mod replay;
mod schedule;
mod tracegen;
mod variants;
// F1: F's side (B1's periodic-control kernel family, B as the child); F2: changed and proven.
mod fbreakdown;
mod fchild;
mod fkernel;
mod flcheck;
mod fmodes;
mod fprove;
mod fschedule;
mod ftracegen;
mod fvariants;
// Pipeline (code/pq-proof-pipeline-20261101): B's proof for a given statement and F's verifier-key material.
mod material;
mod pipeline;
// L0' v2's AIR sources, byte-identical (apply_patch.py checks their SHA-256 against L0' v2's record).
#[path = "l0p2/air.rs"]
#[allow(dead_code)]
mod air;
#[path = "l0p2/instance.rs"]
#[allow(dead_code)]
mod instance;
#[path = "l0p2/keccak.rs"]
#[allow(dead_code)]
mod keccak;
#[path = "l0p2/program.rs"]
#[allow(dead_code)]
mod program;
#[path = "l0p2/sha.rs"]
#[allow(dead_code)]
mod sha;

use std::collections::BTreeMap;
#[path = "../../memory_io.rs"]
mod memory_io;
use memory_io as fs;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Instant;

use p3_air::symbolic::AirLayout;
use p3_air::{Air, BaseAir, RowWindow};
use p3_batch_stark_c3n::{BatchProof, CommonData, NextRowColumns, ProverData, StarkInstance, next_row_columns_for_batch};
use p3_challenger::{CanObserve, DuplexChallenger};
use p3_commit::{ExtensionMmcs, Pcs, PolynomialSpace};
use p3_dft::Radix2DitParallel;
use p3_field::{BasedVectorSpace, ExtensionField, Field, PrimeCharacteristicRing, PrimeField32, PrimeField64, extension::BinomialExtensionField};
use p3_fri::{FriParameters, FriShape, HidingFriPcs, PcsShape, fold_schedule};
use p3_koala_bear::{KoalaBear as F, Poseidon2KoalaBear, default_koalabear_poseidon2_16};
use p3_lookup::{InteractionBuilder, LogUpGadget, LookupProtocol};
use p3_matrix::Matrix;
use p3_matrix::dense::{RowMajorMatrix, RowMajorMatrixView};
use p3_matrix::stack::VerticalPair;
use p3_merkle_tree::MerkleTreeHidingMmcs;
use p3_symmetric::{MerkleCap, PaddingFreeSponge, TruncatedPermutation};
use rand::{RngExt, SeedableRng, rngs::{StdRng, SysRng}};
use serde_json::{Value, json};
use sha2::{Digest as _, Sha256};
use tiny_keccak::{Hasher, Keccak};

use child::{Fault, G1Air};
use compiler::{Input, Options, Program, TableConstraints, TableShape};
use schedule::{ChildSpec, PrefixItem, Schedule, TableSpec};
use tracegen::{ChildData, NativeG1, NativeTable, to_ef};

pub type EF = BinomialExtensionField<F, 8>;
pub type Perm = Poseidon2KoalaBear<16>;
pub type Hash = PaddingFreeSponge<Perm, 16, 8, 8>;
pub type Compress = TruncatedPermutation<Perm, 2, 8, 16>;
pub type Mmcs = MerkleTreeHidingMmcs<<F as Field>::Packing, <F as Field>::Packing, Hash, Compress, StdRng, 2, 8, 8>;
pub type ChMmcs = ExtensionMmcs<F, EF, Mmcs>;
pub type HPcs = HidingFriPcs<F, Radix2DitParallel<F>, Mmcs, ChMmcs, StdRng>;
pub type Challenger = DuplexChallenger<F, Perm, 16, 8>;
/// One configuration type serves the children (C3n) and the kernel (C3): p3-batch-stark uses p3-uni-stark's
/// `StarkConfig`.
pub type Config = p3_uni_stark::StarkConfig<HPcs, EF, Challenger>;
pub type ChildProof = BatchProof<Config>;
pub type Cap = MerkleCap<F, [F; 8]>;
/// F2: F's hiding MMCS (the pinned one with salts regenerated from a per-matrix seed, p3_merkle_tree_ps), F's PCS and
/// configuration; F's proof and key types (p3_batch_stark_c3np). B and L0' v2 keep `Mmcs` and `Config`.
pub type FMmcs = p3_merkle_tree_ps::MerkleTreeHidingMmcs<<F as Field>::Packing, <F as Field>::Packing, Hash, Compress, StdRng, 2, 8, 8>;
pub type FChMmcs = ExtensionMmcs<F, EF, FMmcs>;
pub type FHPcs = HidingFriPcs<F, Radix2DitParallel<F>, FMmcs, FChMmcs, StdRng>;
pub type FConfig = p3_uni_stark::StarkConfig<FHPcs, EF, Challenger>;
pub type FProof = p3_batch_stark_c3np::BatchProof<FConfig>;
pub type FData = p3_batch_stark_c3np::ProverData<FConfig>;
pub type FCommon = p3_batch_stark_c3np::CommonData<FConfig>;

// The child's FRI tail: L0' v2's (and the g1b child's): blowup 2^6, a constant final polynomial, arity at most 4, 43
// queries, 8 random codewords, 8-element salts and digests, cap height 5, no grinding.
pub const LOG_BLOWUP: usize = 6;
pub const LOG_FINAL_POLY_LEN: usize = 0;
pub const MAX_LOG_ARITY: usize = 2;
pub const QUERIES: usize = 43;
pub const RANDOM_CODEWORDS: usize = 8;
pub const SALT_ELEMS: usize = 8;
pub const DIGEST_ELEMS: usize = 8;
pub const CAP_HEIGHT: usize = 5;

// The g1b child's identity.
const G1B_DOMAIN: &[u8] = b"PQ-MIGRATE-RESEARCH-L5-B1-G1B-CHILD-v1";
const G1B_AIR_LABEL: &[u8] = b"PQ-MIGRATE-RESEARCH-L5-B1-G1B-AIR-v1";
const G1B_VK_LABEL: &[u8] = b"PQ-MIGRATE-RESEARCH-L5-B1-G1B-VK-v1";
const G1B_SALT_SEED_LABEL: &[u8] = b"PQ-MIGRATE-RESEARCH-L5-B1-G1B-PREPROCESSED-SALT-SEED-v1";
const CHILD_SOURCE: &[u8] = include_bytes!("child.rs");

// The kernel B's proof parameters. F1: B2's (blowup 2^6, 43 queries, final polynomial 2^2; hiding with 8 random codewords
// and 8-element salts; no grinding) with maximum arity 2^2 (B2: 2^3) and Merkle cap height 5 (B2: 0), the kernel's child
// tail, so that F (B1's kernel family: K2 builds butterflies for arity 2 and 4, every path ends at a cap of 2^5 entries)
// can verify B.
const B_DOMAIN: &[u8] = b"PQ-MIGRATE-RESEARCH-L5-B2-v1";
const B_VK_LABEL: &[u8] = b"PQ-MIGRATE-RESEARCH-L5-B2-VK-v1";
/// B2's preprocessed commitment, L0' v2's method: the salt seed is Keccak(label, B's AIR digest, B's program digest).
const B_AIR_LABEL: &[u8] = b"PQ-MIGRATE-RESEARCH-L5-B2-AIR-v1";
const B_PROGRAM_LABEL: &[u8] = b"PQ-MIGRATE-RESEARCH-L5-B2-PREPROCESSED-PROGRAM-v1";
const B_SALT_SEED_LABEL: &[u8] = b"PQ-MIGRATE-RESEARCH-L5-B2-PREPROCESSED-SALT-SEED-v1";
pub const K_LOG_BLOWUP: usize = 6;
pub const K_LOG_FINAL_POLY_LEN: usize = 2;
pub const K_MAX_LOG_ARITY: usize = 2;
pub const K_QUERIES: usize = 43;
pub const K_CAP_HEIGHT: usize = 5;
const KERNEL_SOURCE: &[u8] = include_bytes!("kernel.rs");
const SCHEDULE_SOURCE: &[u8] = include_bytes!("schedule.rs");
const COMPILER_SOURCE: &[u8] = include_bytes!("compiler.rs");
pub const SCHEMA: &str = "l5-layer-f2/v1";
pub const REVIEW: &str = "loop-internal self-review; not independently reviewed";
pub const TIER: &str = "research measurement; loop-internal self-review; not independently reviewed";
pub type KProof = p3_batch_stark_c3::BatchProof<Config>;
pub type KData = p3_batch_stark_c3::ProverData<Config>;
pub type KCommon = p3_batch_stark_c3::CommonData<Config>;

pub fn os_rng() -> StdRng {
    StdRng::try_from_rng(&mut SysRng).expect("operating-system entropy")
}
pub fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
fn unhex(s: &str) -> Vec<u8> {
    (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).expect("hex")).collect()
}
pub fn sha256_hex(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}
pub fn keccak256(parts: &[&[u8]]) -> [u8; 32] {
    let mut h = Keccak::v256();
    for p in parts {
        h.update(p);
    }
    let mut out = [0; 32];
    h.finalize(&mut out);
    out
}
pub fn ms(t: Instant) -> f64 {
    t.elapsed().as_secs_f64() * 1e3
}
pub fn peak_rss_kib() -> Option<u64> {
    let status = fs::read_to_string("/proc/self/status").ok()?;
    status.lines().find(|l| l.starts_with("VmHWM:"))?.split_whitespace().nth(1)?.parse().ok()
}
pub fn event(value: Value) {
    println!("{value}");
    std::io::stdout().flush().unwrap();
}
pub fn save(path: &Path, bytes: &[u8]) {
    memory_io::write_new(path, bytes)
        .unwrap_or_else(|e| panic!("{}: {e}", path.display()));
}
fn read_json(path: &Path) -> Value {
    serde_json::from_slice(&fs::read(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))).expect("json")
}
fn seeded(seed: &[u8; 32], k: u8) -> StdRng {
    StdRng::from_seed(keccak256(&[seed, &[k]]))
}
/// gzip (level 9, no name, mtime 0) of a byte string: a deterministic file.
pub fn gzip(bytes: &[u8]) -> Vec<u8> {
    use std::process::{Command, Stdio};
    let mut child = Command::new("gzip").args(["-9", "-n", "-c"]).stdin(Stdio::piped()).stdout(Stdio::piped()).spawn().expect("gzip");
    let mut stdin = child.stdin.take().unwrap();
    let data = bytes.to_vec();
    let writer = std::thread::spawn(move || stdin.write_all(&data).unwrap());
    let out = child.wait_with_output().expect("gzip output");
    writer.join().unwrap();
    assert!(out.status.success());
    out.stdout
}

// ---------- the children's AIRs ----------

/// The child's AIRs: the g1b child's three tables or L0' v2's four (`Ag1Air`, unchanged). Every method delegates.
#[derive(Clone, Debug)]
pub enum ChildAir {
    G1(G1Air),
    L0(air::Ag1Air),
}

impl<V: PrimeField64> BaseAir<V> for ChildAir {
    fn width(&self) -> usize {
        match self {
            Self::G1(a) => BaseAir::<V>::width(a),
            Self::L0(a) => BaseAir::<V>::width(a),
        }
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<V>> {
        match self {
            Self::G1(a) => BaseAir::<V>::preprocessed_trace(a),
            Self::L0(a) => BaseAir::<V>::preprocessed_trace(a),
        }
    }
    fn preprocessed_width(&self) -> usize {
        match self {
            Self::G1(a) => BaseAir::<V>::preprocessed_width(a),
            Self::L0(a) => BaseAir::<V>::preprocessed_width(a),
        }
    }
    fn num_periodic_columns(&self) -> usize {
        match self {
            Self::G1(a) => BaseAir::<V>::num_periodic_columns(a),
            Self::L0(a) => BaseAir::<V>::num_periodic_columns(a),
        }
    }
    fn periodic_columns(&self) -> std::borrow::Cow<'_, [Vec<V>]> {
        match self {
            Self::G1(a) => BaseAir::<V>::periodic_columns(a),
            Self::L0(a) => BaseAir::<V>::periodic_columns(a),
        }
    }
    fn periodic_periods(&self) -> Vec<usize> {
        match self {
            Self::G1(a) => BaseAir::<V>::periodic_periods(a),
            Self::L0(a) => BaseAir::<V>::periodic_periods(a),
        }
    }
    fn main_next_row_columns(&self) -> Vec<usize> {
        match self {
            Self::G1(a) => BaseAir::<V>::main_next_row_columns(a),
            Self::L0(a) => BaseAir::<V>::main_next_row_columns(a),
        }
    }
    fn preprocessed_next_row_columns(&self) -> Vec<usize> {
        match self {
            Self::G1(a) => BaseAir::<V>::preprocessed_next_row_columns(a),
            Self::L0(a) => BaseAir::<V>::preprocessed_next_row_columns(a),
        }
    }
    fn num_constraints(&self) -> Option<usize> {
        match self {
            Self::G1(a) => BaseAir::<V>::num_constraints(a),
            Self::L0(a) => BaseAir::<V>::num_constraints(a),
        }
    }
    fn max_constraint_degree(&self) -> Option<usize> {
        match self {
            Self::G1(a) => BaseAir::<V>::max_constraint_degree(a),
            Self::L0(a) => BaseAir::<V>::max_constraint_degree(a),
        }
    }
    fn num_public_values(&self) -> usize {
        match self {
            Self::G1(a) => BaseAir::<V>::num_public_values(a),
            Self::L0(a) => BaseAir::<V>::num_public_values(a),
        }
    }
    fn public_boundary_io(&self) -> &[p3_air::boundary::BoundaryPublic] {
        match self {
            Self::G1(a) => BaseAir::<V>::public_boundary_io(a),
            Self::L0(a) => BaseAir::<V>::public_boundary_io(a),
        }
    }
}

impl<AB: InteractionBuilder> Air<AB> for ChildAir
where
    AB::F: PrimeField64,
{
    fn eval(&self, b: &mut AB) {
        match self {
            Self::G1(a) => a.eval(b),
            Self::L0(a) => a.eval(b),
        }
    }
}

// ---------- the children's configuration and keys ----------

pub fn child_fri_params(rng: StdRng) -> FriParameters<ChMmcs> {
    let perm = default_koalabear_poseidon2_16();
    FriParameters {
        log_blowup: LOG_BLOWUP,
        log_final_poly_len: LOG_FINAL_POLY_LEN,
        max_log_arity: MAX_LOG_ARITY,
        num_queries: QUERIES,
        batch_proof_of_work_bits: 0,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 0,
        mmcs: ChMmcs::new(Mmcs::new(Hash::new(perm.clone()), Compress::new(perm), CAP_HEIGHT, rng)),
    }
}

/// The child's PCS (L0' v2's `pcs_with`). `rngs`: the input MMCS's salt RNG, the FRI MMCS's salt RNG and the PCS's own.
pub fn child_pcs(rngs: [StdRng; 3]) -> HPcs {
    let [input_rng, fri_rng, pcs_rng] = rngs;
    let perm = default_koalabear_poseidon2_16();
    HPcs::new(Radix2DitParallel::default(), Mmcs::new(Hash::new(perm.clone()), Compress::new(perm), CAP_HEIGHT, input_rng), child_fri_params(fri_rng), RANDOM_CODEWORDS, pcs_rng)
}

/// The child's configuration: its challenger pre-seeded with the prefix's field elements.
pub fn child_config(prefix: &[F]) -> Config {
    let mut c = Challenger::new(default_koalabear_poseidon2_16());
    for &v in prefix {
        c.observe(v);
    }
    p3_uni_stark::StarkConfig::new(child_pcs([os_rng(), os_rng(), os_rng()]), c)
}

/// The key-generation configuration: every RNG seeded (only the input MMCS's salts are drawn by key generation, so the
/// preprocessed commitment is a deterministic function of the program and the seed).
fn keygen_config(seed: &[u8; 32]) -> Config {
    p3_uni_stark::StarkConfig::new(child_pcs([seeded(seed, 0), seeded(seed, 1), seeded(seed, 2)]), Challenger::new(default_koalabear_poseidon2_16()))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    L0p2,
    G1b,
}

impl Kind {
    pub fn parse(s: &str) -> Kind {
        match s {
            "l0p2" => Kind::L0p2,
            "g1b" => Kind::G1b,
            other => panic!("unknown child {other}"),
        }
    }
    pub fn name(self) -> &'static str {
        match self {
            Kind::L0p2 => "l0p2",
            Kind::G1b => "g1b",
        }
    }
}

/// A child as B's verifier pins it: its AIRs and key, its tables, its prefix and how its statement maps to the kernel's
/// public values.
pub struct ChildDef {
    pub kind: Kind,
    pub name: String,
    pub airs: Vec<ChildAir>,
    pub data: ProverData<Config>,
    pub table_names: Vec<String>,
    /// log2 of each table's trace before the zero-knowledge extension.
    pub log_traces: Vec<usize>,
    /// Per table, the kernel public value each of its public values is.
    pub public_map: Vec<Vec<usize>>,
    pub num_public: usize,
    pub prefix: Vec<PrefixItem>,
    pub child_vk: [u8; 32],
    /// The honest statement's kernel public values (L0' v2's PI_bytes; the g1b child's PI198 bytes 0..16).
    pub statement: Vec<F>,
    pub record: Value,
}

impl ChildDef {
    pub fn degrees(&self) -> Vec<usize> {
        self.log_traces.iter().map(|l| l + 1).collect()
    }
    /// The tables' public values from the kernel's statement.
    pub fn tables_public(&self, pv: &[F]) -> Vec<Vec<F>> {
        self.public_map.iter().map(|m| m.iter().map(|&j| pv[j]).collect()).collect()
    }
    pub fn prefix_elements(&self, pv: &[F]) -> Vec<F> {
        schedule::prefix_elements(&self.prefix, pv)
    }
    pub fn pre_cap(&self) -> Vec<[F; 8]> {
        pre_cap_of(&self.data.common)
    }
}

fn pre_cap_of(common: &CommonData<Config>) -> Vec<[F; 8]> {
    common.preprocessed.as_ref().expect("a preprocessed commitment").commitment.roots().to_vec()
}

/// L0' v2 as B verifies it: the research statement's AIRs, the key recomputed from the program and checked against the
/// recorded vk.json (every pinning field), the four constant prefix absorptions, the Keccak table's 198 public values
/// (PI_bytes) as the kernel's statement.
pub fn l0p2_def(in_dir: &Path) -> ChildDef {
    let t = Instant::now();
    let b = l0p2::build();
    let build_ms = ms(t);
    let t = Instant::now();
    let data = ProverData::from_airs_and_degrees(&keygen_config(&l0p2::keygen_seed(&b)), &b.airs, &l0p2::degrees()).expect("L0' v2 key generation");
    let keygen_ms = ms(t);
    let next = next_row_columns_for_batch(b.airs.iter(), &data.common);
    let pinned = read_json(&in_dir.join("vk.json"));
    let vk_check = l0p2::check_vk(&b, &data.common, &next, &pinned);
    assert_eq!(vk_check["all_equal"], json!(true), "the recomputed L0' v2 key differs from vk.json: {vk_check}");
    let pre_cap = pre_cap_of(&data.common);
    let child_vk = l0p2::vk_digest(&b, &pre_cap, &next);
    let prefix = l0p2::prefix(&b);
    let airs: Vec<ChildAir> = b.airs.iter().cloned().map(ChildAir::L0).collect();
    let n_pub = b.pi.len();
    let record = json!({"build_ms": build_ms, "keygen_ms": keygen_ms, "vk_check_against_vk_json": vk_check, "shape": l0p2::shape_record(&b)});
    ChildDef {
        kind: Kind::L0p2,
        name: "L0' v2 (results/l5-leaf-l0p2-20261031): field operation 2^14, byte pair 2^16, Keccak 2^8, SHA-512 2^11; seven LogUp buses; C3n; cap 5; blowup 2^6; 43 queries; constant final polynomial".into(),
        airs,
        data,
        table_names: l0p2::TABLES.iter().map(|s| s.to_string()).collect(),
        log_traces: l0p2::degrees().iter().map(|d| d - 1).collect(),
        public_map: vec![vec![], vec![], (0..n_pub).collect(), vec![]],
        num_public: n_pub,
        prefix,
        child_vk,
        statement: b.pi.iter().map(|&v| F::from_u8(v)).collect(),
        record,
    }
}

fn g1b_salt_seed() -> [u8; 32] {
    keccak256(&[G1B_SALT_SEED_LABEL, CHILD_SOURCE])
}
fn g1b_air_digest() -> [u8; 32] {
    keccak256(&[G1B_AIR_LABEL, CHILD_SOURCE])
}
fn g1b_program_digest(prog: &[Vec<u64>]) -> [u8; 32] {
    let mut h = Keccak::v256();
    for c in prog {
        for v in c {
            h.update(&v.to_le_bytes());
        }
    }
    let mut out = [0u8; 32];
    h.finalize(&mut out);
    out
}
fn g1b_descriptor() -> Vec<usize> {
    let mut d: Vec<usize> = vec![];
    d.extend(child::LOGS);
    d.extend(child::WIDTHS);
    d.extend([child::PRE_A, child::PUB_B, child::PUB_C, child::PUB_B_FIRST, child::PUB_C_FIRST, LOG_BLOWUP, LOG_FINAL_POLY_LEN, MAX_LOG_ARITY, QUERIES,
        0, 0, 0, 0, 0, RANDOM_CODEWORDS, SALT_ELEMS, DIGEST_ELEMS, CAP_HEIGHT, 8, 16, 8]);
    d
}
pub fn g1b_keygen(airs: &[G1Air]) -> ProverData<Config> {
    let degrees: Vec<usize> = child::LOGS.iter().map(|l| l + 1).collect();
    ProverData::from_airs_and_degrees(&keygen_config(&g1b_salt_seed()), airs, &degrees).expect("g1b key generation")
}
/// The g1b child's verifier-key digest: label, descriptor, every pinned preprocessed cap entry, the AIR source (G1's
/// form).
fn g1b_vk_digest(pre_cap: &[[F; 8]]) -> [u8; 32] {
    let mut h = Keccak::v256();
    h.update(G1B_VK_LABEL);
    for v in g1b_descriptor() {
        h.update(&(v as u64).to_le_bytes());
    }
    for d in pre_cap {
        for v in d {
            h.update(&v.as_canonical_u32().to_le_bytes());
        }
    }
    h.update(CHILD_SOURCE);
    let mut out = [0u8; 32];
    h.finalize(&mut out);
    out
}
/// The g1b child's prefix: L0' v2's kind (four constant absorptions: domain, AIR digest, descriptor, program digest).
fn g1b_prefix() -> Vec<PrefixItem> {
    let d = g1b_descriptor();
    let mut fields = vec![F::from_usize(d.len())];
    fields.extend(d.iter().map(|&v| F::from_usize(v)));
    vec![
        PrefixItem::Bytes("domain_separator".into(), G1B_DOMAIN.to_vec()),
        PrefixItem::Bytes("air_digest".into(), g1b_air_digest().to_vec()),
        PrefixItem::Fields("descriptor".into(), fields),
        PrefixItem::Bytes("program_digest".into(), g1b_program_digest(&child::program_a()).to_vec()),
    ]
}
/// The g1b child's kernel statement for PI198: the tables' public values, B's (bytes 0..8) then C's (bytes 8..16).
pub fn g1b_statement(pi: &[u8]) -> Vec<F> {
    child::public_values(pi).into_iter().flatten().collect()
}

pub fn g1b_def(pi: &[u8]) -> ChildDef {
    let g1 = child::airs();
    let data = g1b_keygen(&g1);
    let pre_cap = pre_cap_of(&data.common);
    let child_vk = g1b_vk_digest(&pre_cap);
    ChildDef {
        kind: Kind::G1b,
        name: "g1b: G1's child in B's configuration: tables A (2^8, preprocessed), B (2^11), C (2^16), two LogUp buses, C3n next-row subsets, cap 5, blowup 2^6, 43 queries, arity <= 4, constant final polynomial, a constant prefix".into(),
        airs: g1.into_iter().map(ChildAir::G1).collect(),
        data,
        table_names: child::TABLE_NAMES.iter().map(|s| s.to_string()).collect(),
        log_traces: child::LOGS.to_vec(),
        public_map: vec![vec![], (0..child::PUB_B).collect(), (child::PUB_B..child::PUB_B + child::PUB_C).collect()],
        num_public: child::PUB_B + child::PUB_C,
        prefix: g1b_prefix(),
        child_vk,
        statement: g1b_statement(pi),
        record: json!({"air_digest": hex(&g1b_air_digest()), "program_digest": hex(&g1b_program_digest(&child::program_a())),
            "descriptor": g1b_descriptor(), "domain": String::from_utf8_lossy(G1B_DOMAIN), "salt_seed": hex(&g1b_salt_seed())}),
    }
}

pub fn child_def(kind: Kind, in_dir: &Path, pi: &[u8]) -> ChildDef {
    match kind {
        Kind::L0p2 => l0p2_def(in_dir),
        Kind::G1b => g1b_def(pi),
    }
}

fn layout_of(air: &ChildAir, pre_w: usize) -> AirLayout {
    AirLayout {
        preprocessed_width: pre_w,
        main_width: BaseAir::<F>::width(air),
        num_public_values: BaseAir::<F>::num_public_values(air),
        num_periodic_columns: 0,
        ..Default::default()
    }
}

/// The global bus index of every lookup of every table, the bus count and the widest tuple (C3n transcript.rs
/// l. 514-558: a global bus shares an index by name in first-appearance order, a local one takes a fresh index).
fn bus_layout(common: &CommonData<Config>) -> (Vec<Vec<usize>>, usize, usize, Vec<String>) {
    let mut names: Vec<String> = vec![];
    let mut next = 0;
    let mut width = 1;
    let mut out = vec![];
    for lk in &common.lookups {
        let mut v = vec![];
        for l in lk.iter() {
            width = width.max(l.elements.first().map(|e| e.len()).unwrap_or(1));
            match &l.kind {
                p3_lookup::Kind::Global(name) => {
                    let id = match names.iter().position(|n| n == name) {
                        Some(i) => i,
                        None => {
                            names.push(name.clone());
                            next += 1;
                            next - 1
                        }
                    };
                    v.push(id);
                }
                p3_lookup::Kind::Local => {
                    names.push(String::new());
                    next += 1;
                    v.push(next - 1);
                }
            }
        }
        out.push(v);
    }
    (out, next, width, names)
}

fn pre_width(common: &CommonData<Config>, i: usize) -> usize {
    common.preprocessed.as_ref().and_then(|g| g.instances[i].as_ref().map(|m| m.width)).unwrap_or(0)
}

/// Every table's symbolic constraints (base, extension), from the AIRs and the key's lookups.
pub fn symbolic(def: &ChildDef) -> Vec<(Vec<p3_air::symbolic::SymbolicExpression<F>>, Vec<p3_air::symbolic::SymbolicExpressionExt<F, EF>>)> {
    let gadget = LogUpGadget::new();
    def.airs
        .iter()
        .enumerate()
        .map(|(i, air)| {
            let lk: &[p3_lookup::Lookup<F>] = &def.data.common.lookups[i];
            p3_batch_stark_c3n::symbolic::get_symbolic_constraints::<F, EF, _, _>(air, layout_of(air, pre_width(&def.data.common, i)), lk, &gadget)
        })
        .collect()
}

/// Every table's shape (from the AIRs and the key), the compiled batch program and its file's hash.
pub fn compile_child(def: &ChildDef, opts: Options, drop_ext: Option<(usize, usize)>) -> (Vec<TableShape>, Program, [u8; 32]) {
    let gadget = LogUpGadget::new();
    let pcs = child_pcs([os_rng(), os_rng(), os_rng()]);
    let (buses, nbus, width, _) = bus_layout(&def.data.common);
    let mut shapes = vec![];
    let mut cons = symbolic(def);
    if let Some((t, k)) = drop_ext {
        cons[t].1.remove(k);
    }
    for (i, air) in def.airs.iter().enumerate() {
        let pre_w = pre_width(&def.data.common, i);
        let layout = layout_of(air, pre_w);
        let lk: &[p3_lookup::Lookup<F>] = &def.data.common.lookups[i];
        let init = <HPcs as Pcs<EF, Challenger>>::natural_domain_for_degree(&pcs, 1usize << def.log_traces[i]);
        let lqd = p3_batch_stark_c3n::symbolic::get_log_num_quotient_chunks_for_domain::<F, EF, _, _>(air, layout, init, lk, 1, &gadget);
        shapes.push(TableShape {
            name: def.table_names[i].clone(),
            log_trace: def.log_traces[i],
            log_ext: def.log_traces[i] + 1,
            width: BaseAir::<F>::width(air),
            num_public: BaseAir::<F>::num_public_values(air),
            preprocessed_width: pre_w,
            perm_width: if lk.is_empty() { 0 } else { lk.len() + 1 },
            lookup_bus: buses[i].clone(),
            log_quotient_degree: lqd,
            chunks: 1usize << (lqd + 1),
        });
    }
    let tc: Vec<TableConstraints> = cons.iter().map(|(b, e)| TableConstraints { base: b, ext: e }).collect();
    let p = compiler::compile(&shapes, &tc, nbus, width, opts);
    let digest: [u8; 32] = Sha256::digest(p.file_bytes(&hex(&def.child_vk))).into();
    (shapes, p, digest)
}

struct Rec(Vec<F>);
impl CanObserve<F> for Rec {
    fn observe(&mut self, v: F) {
        self.0.push(v);
    }
}

/// The child's shape, its three transcript seeds and its compiled program, from the configuration, the AIRs and the
/// key alone.
pub fn child_spec(def: &ChildDef) -> ChildSpec {
    let (shapes, program, program_sha256) = compile_child(def, Options::default(), None);
    spec_from(def, shapes, program, program_sha256)
}

pub fn spec_from(def: &ChildDef, shapes: Vec<TableShape>, program: Program, program_sha256: [u8; 32]) -> ChildSpec {
    let common = &def.data.common;
    let next = next_row_columns_for_batch(def.airs.iter(), common);
    let (buses, nbus, width, _) = bus_layout(common);
    let tables: Vec<TableSpec> = (0..def.airs.len())
        .map(|i| {
            let s = &shapes[i];
            TableSpec {
                name: s.name.clone(),
                log_trace: s.log_trace,
                width: s.width,
                pre_width: s.preprocessed_width,
                public: def.public_map[i].clone(),
                next_main: next[i].main.clone(),
                next_pre: next[i].preprocessed.clone(),
                next_perm: next[i].permutation.clone(),
                perm_width: s.perm_width,
                lookup_bus: buses[i].clone(),
                log_qd: s.log_quotient_degree,
                chunks: s.chunks,
            }
        })
        .collect();
    let mut heights: Vec<usize> = tables.iter().map(|t| t.log_trace + 1 + LOG_BLOWUP).collect::<std::collections::BTreeSet<_>>().into_iter().rev().collect();
    heights.dedup();
    let index_bits = heights[0];
    let arities = fold_schedule(&heights, LOG_BLOWUP + LOG_FINAL_POLY_LEN, MAX_LOG_ARITY);
    // The batch transcript's seed (C3n transcript.rs l. 421-467).
    let shape = p3_batch_stark_c3n::BatchShape {
        trace_widths: tables.iter().map(|t| t.width).collect(),
        public_value_counts: tables.iter().map(|t| t.public.len()).collect(),
        preprocessed_widths: tables.iter().map(|t| t.pre_width).collect(),
        has_preprocessed_commitment: common.preprocessed.is_some(),
        num_lookup_instances: tables.iter().filter(|t| t.perm_width > 0).count(),
        lookup_pow_bits: 0,
        has_randomization_commitment: true,
        ood_pow_bits: 0,
        next_row_columns: next.clone(),
    };
    let mut batch = Rec(vec![]);
    shape.domain_separator::<F, EF>().seed(&mut batch);
    let draft = ChildSpec {
        name: String::new(),
        tables: tables.clone(),
        rc: RANDOM_CODEWORDS,
        salt: SALT_ELEMS,
        log_blowup: LOG_BLOWUP,
        log_final_poly_len: LOG_FINAL_POLY_LEN,
        max_log_arity: MAX_LOG_ARITY,
        num_queries: QUERIES,
        index_bits,
        fri_log_arities: arities.clone(),
        prefix: def.prefix.clone(),
        num_public: def.num_public,
        seeds: [vec![], vec![], vec![]],
        child_vk: def.child_vk,
        pre_cap: def.pre_cap(),
        num_buses: nbus,
        max_message_width: width,
        program: Arc::new(program),
        program_sha256,
    };
    // The PCS's seed from the claimed-evaluation counts the trees fix (pcs_transcript.rs l. 98-164).
    let trees = schedule::trees(&draft);
    let counts: Vec<Vec<Vec<usize>>> = trees
        .iter()
        .filter(|t| matches!(t.kind, schedule::TreeKind::Input(_)))
        .map(|t| t.mats.iter().map(|m| m.points.iter().map(|_| m.width).collect()).collect())
        .collect();
    let mut pcs = Rec(vec![]);
    PcsShape { claimed_evaluation_counts: counts, batch_pow_bits: 0 }.domain_separator::<F, EF>().seed(&mut pcs);
    let mut fri = Rec(vec![]);
    FriShape::with_schedule(&child_fri_params(os_rng()), arities.clone(), index_bits).domain_separator::<F, EF>().seed(&mut fri);
    ChildSpec { name: def.name.clone(), seeds: [batch.0, pcs.0, fri.0], ..draft }
}

/// The same specification with another compiled program (the changed-program checks).
pub fn spec_with_program(spec: &ChildSpec, program: Program) -> ChildSpec {
    let mut s = spec.clone();
    s.program_sha256 = Sha256::digest(program.file_bytes(&hex(&spec.child_vk))).into();
    s.program = Arc::new(program);
    s
}

// ---------- B's preprocessed key and verifier key (B2) ----------

/// B's AIR digest: the sources that define B's constraint system and derive its preprocessed program (the kernel, the
/// schedule compiler, the constraint compiler).
pub fn b2_air_digest() -> [u8; 32] {
    keccak256(&[B_AIR_LABEL, KERNEL_SOURCE, SCHEDULE_SOURCE, COMPILER_SOURCE])
}

/// B's program digest: the table height, the main and preprocessed widths, the statement size, the transcript's first
/// absorbed count, every preprocessed column (its name, then its values as u32 little-endian) and the public-value
/// binding map (per lane, each (preprocessed selector, public value)).
pub fn b2_program_digest(s: &Schedule) -> [u8; 32] {
    let mut h = Keccak::v256();
    h.update(B_PROGRAM_LABEL);
    for v in [s.n, kernel::WIDTH, s.air.pre.len(), s.num_public, s.air.k0] {
        h.update(&(v as u64).to_le_bytes());
    }
    for (name, col) in s.air.pre_names.iter().zip(&s.air.pre) {
        h.update(&(name.len() as u64).to_le_bytes());
        h.update(name.as_bytes());
        h.update(&(col.len() as u64).to_le_bytes());
        let bytes: Vec<u8> = col.iter().flat_map(|v| v.as_canonical_u32().to_le_bytes()).collect();
        h.update(&bytes);
    }
    for lane in &s.air.pub_terms {
        h.update(&(lane.len() as u64).to_le_bytes());
        for &(sel, j) in lane {
            h.update(&(sel as u64).to_le_bytes());
            h.update(&(j as u64).to_le_bytes());
        }
    }
    let mut out = [0u8; 32];
    h.finalize(&mut out);
    out
}

/// The key generation's salt seed (L0' v2's method): Keccak(label, B's AIR digest, B's program digest).
pub fn b2_salt_seed(air: &[u8; 32], program: &[u8; 32]) -> [u8; 32] {
    keccak256(&[B_SALT_SEED_LABEL, air, program])
}

/// B's PCS (the kernel's FRI parameters) with given random number generators: the input MMCS's salts, the FRI MMCS's
/// salts, the PCS's own (the random codewords).
fn b2_pcs(rngs: [StdRng; 3]) -> HPcs {
    let [input_rng, fri_rng, pcs_rng] = rngs;
    let perm = default_koalabear_poseidon2_16();
    let fri = FriParameters {
        log_blowup: K_LOG_BLOWUP,
        log_final_poly_len: K_LOG_FINAL_POLY_LEN,
        max_log_arity: K_MAX_LOG_ARITY,
        num_queries: K_QUERIES,
        batch_proof_of_work_bits: 0,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 0,
        mmcs: ChMmcs::new(Mmcs::new(Hash::new(perm.clone()), Compress::new(perm.clone()), K_CAP_HEIGHT, fri_rng)),
    };
    HPcs::new(Radix2DitParallel::default(), Mmcs::new(Hash::new(perm.clone()), Compress::new(perm), K_CAP_HEIGHT, input_rng), fri, RANDOM_CODEWORDS, pcs_rng)
}

/// B's key-generation configuration: every random number generator seeded (key generation draws only the input
/// MMCS's salts, so the preprocessed commitment is a deterministic function of B's preprocessed trace and the seed).
fn b2_keygen_config(seed: &[u8; 32]) -> Config {
    p3_uni_stark::StarkConfig::new(b2_pcs([seeded(seed, 0), seeded(seed, 1), seeded(seed, 2)]), Challenger::new(default_koalabear_poseidon2_16()))
}

/// B's key: the digests its seed is derived from, and its commitment.
#[derive(Clone)]
pub struct BKey {
    pub air_digest: [u8; 32],
    pub program_digest: [u8; 32],
    pub salt_seed: [u8; 32],
    pub commitment: Cap,
    pub keygen_ms: f64,
}

/// B's key generation (p3_batch_stark_c3's own `ProverData::from_airs_and_degrees` with the seeded configuration): the
/// preprocessed commitment, the packed lookups and the prover data (the preprocessed trace's LDE and tree).
pub fn b2_keygen(s: &Schedule) -> (KData, BKey) {
    let air_digest = b2_air_digest();
    let program_digest = b2_program_digest(s);
    let salt_seed = b2_salt_seed(&air_digest, &program_digest);
    let t = Instant::now();
    let data = KData::from_airs_and_degrees(&b2_keygen_config(&salt_seed), std::slice::from_ref(&s.air), &[s.log_n + 1]).expect("B's key generation");
    let keygen_ms = ms(t);
    let commitment = data.common.preprocessed.as_ref().expect("B's preprocessed commitment").commitment.clone();
    (data, BKey { air_digest, program_digest, salt_seed, commitment, keygen_ms })
}

/// B's key from its pinned record (vk.json): the AIR and program digests recomputed from this schedule and compared,
/// the commitment taken from the record (the schedule stage computed it from the seed; the prove and verify modes
/// recompute it). For the trace-level modes, which prove nothing.
pub fn pinned_key(s: &Schedule, pinned: &Value) -> BKey {
    let air_digest = b2_air_digest();
    let program_digest = b2_program_digest(s);
    assert_eq!(pinned["air_digest"], json!(hex(&air_digest)), "B's AIR digest differs from the pinned one");
    assert_eq!(pinned["program_digest"], json!(hex(&program_digest)), "B's program digest differs from the pinned one");
    let roots: Vec<[F; 8]> = pinned["preprocessed"]["cap"]
        .as_array()
        .unwrap()
        .iter()
        .map(|d| core::array::from_fn(|k| F::from_u32(d[k].as_u64().unwrap() as u32)))
        .collect();
    BKey { air_digest, program_digest, salt_seed: b2_salt_seed(&air_digest, &program_digest), commitment: Cap::new(roots), keygen_ms: 0.0 }
}

fn cap_u32(cap: &Cap) -> Vec<Vec<u32>> {
    cap.roots().iter().map(|d| d.iter().map(|x| x.as_canonical_u32()).collect()).collect()
}

/// B's verifier-key digest: B's shape and parameters (B1's list, with the preprocessed width and no periodic column),
/// the child's shape and identity (as B1's), B's AIR digest, B's program digest (every preprocessed column and the
/// public-value binding map), the salt seed, **B's pinned preprocessed commitment** (every cap entry), the bus name, the
/// child's verifier-key digest and prefix, the compiled program's SHA-256 and the kernel's, schedule's and compiler's
/// sources.
pub fn b2_vk_digest(s: &Schedule, key: &BKey) -> [u8; 32] {
    let mut h = Keccak::v256();
    h.update(B_VK_LABEL);
    let c = &s.child;
    let mut d: Vec<u64> = vec![s.n as u64, kernel::WIDTH as u64, s.air.pre.len() as u64, 0, s.q as u64, s.num_public as u64,
        s.t_rows as u64, s.block_rows as u64, s.program.len() as u64, K_LOG_BLOWUP as u64, K_LOG_FINAL_POLY_LEN as u64,
        K_MAX_LOG_ARITY as u64, K_QUERIES as u64, RANDOM_CODEWORDS as u64, SALT_ELEMS as u64, DIGEST_ELEMS as u64, K_CAP_HEIGHT as u64,
        c.index_bits as u64, c.num_queries as u64, c.log_final_poly_len as u64, c.log_blowup as u64, CAP_HEIGHT as u64];
    d.extend(c.fri_log_arities.iter().map(|&a| a as u64));
    for t in &c.tables {
        d.extend([t.log_trace, t.width, t.pre_width, t.perm_width, t.chunks, t.log_qd].map(|v| v as u64));
        d.extend(t.public.iter().map(|&v| v as u64));
        d.extend(t.next_main.iter().chain(&t.next_pre).chain(&t.next_perm).map(|&v| v as u64));
        d.extend(t.lookup_bus.iter().map(|&v| v as u64));
    }
    for v in d {
        h.update(&v.to_le_bytes());
    }
    h.update(&key.air_digest);
    h.update(&key.program_digest);
    h.update(&key.salt_seed);
    for root in key.commitment.roots() {
        for v in root {
            h.update(&v.as_canonical_u32().to_le_bytes());
        }
    }
    h.update(kernel::BUS.as_bytes());
    h.update(&c.child_vk);
    for v in schedule::prefix_elements(&c.prefix, &vec![F::ZERO; c.num_public]) {
        h.update(&v.as_canonical_u32().to_le_bytes());
    }
    h.update(&c.program_sha256);
    h.update(KERNEL_SOURCE);
    h.update(SCHEDULE_SOURCE);
    h.update(COMPILER_SOURCE);
    let mut out = [0u8; 32];
    h.finalize(&mut out);
    out
}

/// B's proof parameters, as recorded.
pub fn b2_params() -> Value {
    json!({"prover": "p3_batch_stark_c3 (C3b's copy of p3-batch-stark 0.9.0-rc.1): one instance, its preprocessed trace committed by B's key (opened at zeta only), one named LogUp bus (global kind; its terminal must be zero)",
        "log_blowup": K_LOG_BLOWUP, "log_final_poly_len": K_LOG_FINAL_POLY_LEN, "max_log_arity": K_MAX_LOG_ARITY,
        "num_queries": K_QUERIES, "pow_bits": 0, "random_codewords": RANDOM_CODEWORDS, "salt_elements": SALT_ELEMS,
        "digest_elements": DIGEST_ELEMS, "cap_height": K_CAP_HEIGHT, "extension_degree": 8,
        "hash": "Poseidon2KoalaBear<16>: PaddingFreeSponge<_,16,8,8> leaves, TruncatedPermutation<_,2,8,16> nodes, DuplexChallenger<_,_,16,8>"})
}

/// B's verifying key as a record (vk.json): the preprocessed commitment (postcard bytes, Keccak-256, every cap entry, the
/// instance metadata), the salt seed and the digests it is derived from, B's verifier-key digest, the shape, the packed
/// lookups and the FRI parameters.
pub fn b2_vk_json(s: &Schedule, common: &KCommon, key: &BKey, vk: &[u8; 32]) -> Value {
    let g = common.preprocessed.as_ref().expect("B's preprocessed commitment");
    let enc = postcard::to_allocvec(&g.commitment).unwrap();
    json!({"schema": "l5-layer-b2/vk/v1", "review": REVIEW,
        "what": "B's verifying key for its child: the preprocessed commitment of B's control (seeded key generation, L0' v2's method), the digests the seed is derived from, B's verifier-key digest; a verifier recomputes the key and compares every field",
        "preprocessed": {"commitment_postcard_hex": hex(&enc), "commitment_keccak256": hex(&keccak256(&[&enc])), "cap": cap_u32(&g.commitment),
            "cap_height": g.commitment.height(), "matrix_to_instance": g.matrix_to_instance,
            "instances": g.instances.iter().map(|m| m.as_ref().map(|m| json!({"matrix_index": m.matrix_index, "width": m.width, "degree_bits": m.degree_bits}))).collect::<Vec<_>>(),
            "salt_seed": hex(&key.salt_seed), "salt_seed_derivation": "Keccak-256(label, B's AIR digest, B's program digest)",
            "salt_seed_label": String::from_utf8_lossy(B_SALT_SEED_LABEL)},
        "air_digest": hex(&key.air_digest), "air_digest_derivation": "Keccak-256(label, kernel.rs, schedule.rs, compiler.rs)",
        "program_digest": hex(&key.program_digest),
        "program_digest_derivation": "Keccak-256(label, height, main width, preprocessed width, statement size, k0, every preprocessed column's name and values, the public-value binding map)",
        "b2_vk_digest": hex(vk), "domain": String::from_utf8_lossy(B_DOMAIN),
        "rows": s.n, "log_n": s.log_n, "main_width": kernel::WIDTH, "preprocessed_width": s.air.pre.len(), "periodic_columns": 0,
        "public_values": s.num_public, "child_vk_digest": hex(&s.child.child_vk), "compiled_program_sha256": hex(&s.child.program_sha256),
        "lookups": common.lookups[0].iter().map(|l| json!({"kind": format!("{:?}", l.kind), "column": l.column, "tuples": l.elements.len(), "count_weight": l.count_weight})).collect::<Vec<_>>(),
        "fri": b2_params()})
}

/// The recomputed key against a pinned vk.json, field by field.
pub fn check_b2_vk(recomputed: &Value, pinned: &Value) -> Value {
    let fields = ["preprocessed", "air_digest", "program_digest", "b2_vk_digest", "domain", "rows", "log_n", "main_width",
        "preprocessed_width", "periodic_columns", "public_values", "child_vk_digest", "compiled_program_sha256", "lookups", "fri"];
    let checks: Vec<(&str, bool)> = fields.iter().map(|f| (*f, recomputed[*f] == pinned[*f])).collect();
    let all = checks.iter().all(|(_, ok)| *ok);
    json!({"all_equal": all, "fields": checks.iter().map(|(f, ok)| json!({"field": f, "equal": ok})).collect::<Vec<_>>(),
        "commitment_keccak256": recomputed["preprocessed"]["commitment_keccak256"]})
}

/// B's proof configuration: its challenger observes B's domain, B's verifier-key digest and every public value before
/// the first commitment (B1's `b1_config`); the random number generators are the operating system's.
pub fn b2_config(vk: &[u8; 32], pv: &[F]) -> Config {
    let mut c = Challenger::new(default_koalabear_poseidon2_16());
    for bytes in [B_DOMAIN, &vk[..]] {
        c.observe(F::from_usize(bytes.len()));
        for &b in bytes {
            c.observe(F::from_u8(b));
        }
    }
    c.observe(F::from_usize(pv.len()));
    for &v in pv {
        c.observe(v);
    }
    p3_uni_stark::StarkConfig::new(b2_pcs([os_rng(), os_rng(), os_rng()]), c)
}

/// B's proof of a (possibly edited) trace with the prover data of B's key.
pub fn prove_kernel(cfg: &Config, s: &Schedule, data: &KData, trace: &RowMajorMatrix<F>, pv: &[F]) -> KProof {
    let airs = [s.air.clone()];
    let traces = [trace];
    let instances = p3_batch_stark_c3::StarkInstance::new_multiple(&airs, &traces, &[pv.to_vec()]);
    p3_batch_stark_c3::prove_batch(cfg, &instances, data).expect("B's prover")
}

/// B's verifier: the proof against the verifier key (its digest) and the key's common data (the pinned preprocessed
/// commitment and the packed lookups).
pub fn verify_kernel(s: &Schedule, vk: &[u8; 32], common: &KCommon, proof: &KProof, pv: &[F]) -> (bool, Option<String>, f64) {
    let t = Instant::now();
    let cfg = b2_config(vk, pv);
    let r = p3_batch_stark_c3::verify_batch(&cfg, std::slice::from_ref(&s.air), proof, &[pv.to_vec()], common);
    (r.is_ok(), r.err().map(|e| format!("{e:?}")), ms(t))
}

/// The breakdown's expectations from B's schedule and key.
pub fn kshape(s: &Schedule, common: &KCommon) -> breakdown::KShape {
    let lookups: &[p3_lookup::Lookup<F>] = &common.lookups[0];
    let layout = AirLayout::from_air(&s.air);
    let gadget = LogUpGadget::new();
    let log_chunks = p3_batch_stark_c3::symbolic::get_log_num_quotient_chunks::<F, EF, _, _>(&s.air, layout, s.n, lookups, 1, &gadget);
    let lde = s.log_n + 1 + K_LOG_BLOWUP;
    let arities = fold_schedule(&[lde], K_LOG_BLOWUP + K_LOG_FINAL_POLY_LEN, K_MAX_LOG_ARITY);
    breakdown::KShape { log_n: s.log_n, width: kernel::WIDTH, pre_width: s.air.pre.len(), perm_width: 8 * (lookups.len() + 1), chunks: 1usize << (log_chunks + 1), fri_log_arities: arities }
}

// ---------- the native replay ----------

fn ef_flat(out: &mut Vec<F>, values: impl Iterator<Item = EF>) {
    for v in values {
        out.extend_from_slice(v.as_basis_coefficients_slice());
    }
}
fn cap_flat(out: &mut Vec<F>, cap: &Cap) {
    for d in cap.roots() {
        out.extend_from_slice(d);
    }
}

type Claims = Vec<p3_commit::CommitmentWithOpeningPoints<EF, Cap, p3_field::coset::TwoAdicMultiplicativeCoset<F>>>;

/// The child proof's claimed values per (input round, matrix, point) as the PCS absorbs them: the C3n verifier's own
/// `commitments_with_opening_points` (verifier/mod.rs l. 185-446) with the hiding PCS's random-codeword values
/// appended (hiding_pcs.rs l. 357-425).
fn claims_of(cfg: &Config, proof: &ChildProof, common: &CommonData<Config>, next: &[NextRowColumns], zeta: EF, lqd: &[usize]) -> Claims {
    let pre_w: Vec<usize> = (0..lqd.len()).map(|i| pre_width(common, i)).collect();
    let (rounds, _, _) = p3_batch_stark_c3n::verifier::commitments_with_opening_points(cfg, next, zeta, &proof.commitments, &proof.opened_values, common, &proof.degree_bits, &pre_w, lqd)
        .expect("commitments_with_opening_points");
    let rcw = &proof.opening_proof.0;
    rounds
        .into_iter()
        .enumerate()
        .map(|(r, mut round)| {
            for (m, mat) in round.matrices.iter_mut().enumerate() {
                for (p, pt) in mat.points.iter_mut().enumerate() {
                    pt.values.extend(rcw[r][m][p].iter().copied());
                }
            }
            round
        })
        .collect()
}

/// The child proof's witness stream in the schedule's order (the events' witness segments).
fn witness_stream(s: &Schedule, proof: &ChildProof, claims: &Claims) -> Vec<F> {
    let mut wit = vec![];
    let fri = &proof.opening_proof.1;
    let input_trees: Vec<usize> = (0..s.trees.len()).filter(|&t| matches!(s.trees[t].kind, schedule::TreeKind::Input(_))).collect();
    for (name, first, len) in &s.wit_segments {
        let before = wit.len();
        assert_eq!(before, *first, "{name}: witness position");
        if name == "batch.main_commitment" {
            cap_flat(&mut wit, &proof.commitments.main);
        } else if name == "batch.permutation_commitment" {
            cap_flat(&mut wit, proof.commitments.permutation.as_ref().unwrap());
        } else if name == "batch.quotient_random_commitment" {
            cap_flat(&mut wit, &proof.commitments.quotient_chunks);
        } else if let Some(t) = name.strip_prefix("batch.lookup_terminal.table") {
            let t: usize = t.parse().unwrap();
            ef_flat(&mut wit, std::iter::once(proof.lookup_terminals[t].as_ref().unwrap().0));
        } else if let Some(rest) = name.strip_prefix("pcs.claims.") {
            let parts: Vec<&str> = rest.split('.').collect();
            let ti = s.trees.iter().position(|t| t.name == parts[0]).unwrap();
            let round = input_trees.iter().position(|&x| x == ti).unwrap();
            let m: usize = parts[1][1..].parse().unwrap();
            let pt_name = parts[2..].join(".");
            let p = s.trees[ti].mats[m].points.iter().position(|&pp| schedule::pt_name(pp) == pt_name).unwrap();
            ef_flat(&mut wit, claims[round].matrices[m].points[p].values.iter().copied());
        } else if let Some(r) = name.strip_prefix("fri.round").and_then(|x| x.strip_suffix(".commitment")) {
            let r: usize = r.parse().unwrap();
            cap_flat(&mut wit, &fri.commit_phase_commits[r]);
        } else if name == "fri.final_poly" {
            ef_flat(&mut wit, fri.final_poly.iter().copied());
        } else {
            panic!("unknown witness segment {name}");
        }
        assert_eq!(wit.len() - before, *len, "{name}: witness length");
    }
    assert_eq!(wit.len(), s.wit_len);
    wit
}

/// A recording builder over EF8 values: every base and extension constraint's value at one point, in fold order.
pub struct PointBuilder<'a> {
    pub main: RowWindow<'a, EF>,
    pub pre: RowWindow<'a, EF>,
    pub perm: RowWindow<'a, EF>,
    pub public: &'a [F],
    pub challenges: &'a [EF],
    pub perm_values: &'a [EF],
    pub sels: [EF; 3],
    pub values: Vec<EF>,
}
impl<'a> p3_air::AirBuilder for PointBuilder<'a> {
    type F = F;
    type Expr = EF;
    type Var = EF;
    type PreprocessedWindow = RowWindow<'a, EF>;
    type MainWindow = RowWindow<'a, EF>;
    type PublicVar = F;
    type PeriodicVar = EF;
    fn main(&self) -> Self::MainWindow {
        self.main
    }
    fn preprocessed(&self) -> &Self::PreprocessedWindow {
        &self.pre
    }
    fn is_first_row(&self) -> EF {
        self.sels[0]
    }
    fn is_last_row(&self) -> EF {
        self.sels[1]
    }
    fn is_transition(&self) -> EF {
        self.sels[2]
    }
    fn assert_zero<I: Into<EF>>(&mut self, x: I) {
        self.values.push(x.into());
    }
    fn public_values(&self) -> &[F] {
        self.public
    }
    fn periodic_values(&self) -> &[EF] {
        &[]
    }
}
impl<'a> p3_air::ExtensionBuilder for PointBuilder<'a> {
    type EF = EF;
    type ExprEF = EF;
    type VarEF = EF;
    fn assert_zero_ext<I: Into<EF>>(&mut self, x: I) {
        self.values.push(x.into());
    }
}
impl<'a> p3_air::PermutationAirBuilder for PointBuilder<'a> {
    type MP = RowWindow<'a, EF>;
    type RandomVar = EF;
    type PermutationVar = EF;
    fn permutation(&self) -> Self::MP {
        self.perm
    }
    fn permutation_randomness(&self) -> &[EF] {
        self.challenges
    }
    fn permutation_values(&self) -> &[EF] {
        self.perm_values
    }
}
impl<'a> p3_lookup::InteractionBuilder for PointBuilder<'a> {
    fn push_interaction<E: Into<EF>>(&mut self, _bus: &str, fields: impl IntoIterator<Item = E>, _count: impl Into<p3_lookup::Count<EF>>) {
        fields.into_iter().for_each(drop);
    }
    fn push_local_interaction(&mut self, tuples: impl IntoIterator<Item = (Vec<EF>, p3_lookup::Count<EF>)>) {
        tuples.into_iter().for_each(drop);
    }
}

/// The lookup challenges as the batch transcript lays them out per table (transcript.rs l. 489-578).
fn lookup_challenges(spec: &ChildSpec, la: EF, lb: EF) -> Vec<Vec<EF>> {
    let gamma = lb.exp_u64(spec.max_message_width as u64);
    let prefix: Vec<EF> = (0..spec.num_buses).map(|b| la + gamma * F::from_usize(b + 1)).collect();
    spec.tables.iter().map(|t| t.lookup_bus.iter().flat_map(|&b| [prefix[b], lb]).collect()).collect()
}

/// The native verifier's values of every table's identity and of the terminal check, with C3n's and p3-commit's
/// functions: `selectors_at_point` and `vanishing_poly_at_point` over the table's domain, every constraint by the
/// AIR's own eval and the LogUp gadget (`eval_air_and_lookups`, protocol.rs l. 113-130), the accumulator of
/// `VerifierConstraintFolderWithLookups` (folder.rs l. 106-239, data.rs l. 93-115), the chunk domains and factors,
/// `recompose_quotient_from_chunks`, folded * inv_vanishing = quotient (data.rs l. 117-120) and `verify_terminal_sum`.
pub fn native_g1(spec: &ChildSpec, airs: &[ChildAir], common: &CommonData<Config>, next: &[NextRowColumns], ov: &p3_batch_stark_c3n::BatchOpenedValues<EF>,
    terminals: &[Option<p3_lookup::LookupTerminal<EF>>], public: &[Vec<F>], alpha: EF, zeta: EF, la: EF, lb: EF) -> NativeG1 {
    let gadget = LogUpGadget::new();
    let pcs = child_pcs([os_rng(), os_rng(), os_rng()]);
    let chal = lookup_challenges(spec, la, lb);
    let mut tables = vec![];
    for (i, air) in airs.iter().enumerate() {
        let tb = &spec.tables[i];
        let inst = &ov.instances[i];
        let bo = &inst.base_opened_values;
        let zero = |_c: usize| EF::ZERO;
        let tn = next[i].main_split().expand_next(bo.trace_next.as_deref().unwrap_or(&[]), zero);
        let pre_local: Vec<EF> = bo.preprocessed.as_ref().map(|p| p.local.clone()).unwrap_or_default();
        let pre_next = next[i].preprocessed_split().expand_next(bo.preprocessed.as_ref().and_then(|p| p.next.as_deref()).unwrap_or(&[]), zero);
        let recompose = |flat: &[EF]| -> Vec<EF> { flat.chunks_exact(8).map(|c| <EF as ExtensionField<F>>::from_ext_basis_coefficients(c).unwrap()).collect() };
        let perm_local = recompose(&inst.permutation_local);
        let perm_next_full = next[i].permutation_split(8).expand_next(&inst.permutation_next, zero);
        let perm_next = recompose(&perm_next_full);
        let terminal = terminals[i].as_ref().map(|t| t.0);
        let tv: Vec<EF> = terminal.into_iter().collect();
        let init = <HPcs as Pcs<EF, Challenger>>::natural_domain_for_degree(&pcs, 1usize << tb.log_trace);
        let ext = <HPcs as Pcs<EF, Challenger>>::natural_domain_for_degree(&pcs, 1usize << (tb.log_trace + 1));
        let sels = init.selectors_at_point(zeta);
        let z_h = init.vanishing_poly_at_point(zeta);
        let lk: &[p3_lookup::Lookup<F>] = &common.lookups[i];
        let mut pb = PointBuilder {
            main: RowWindow::from_two_rows(&bo.trace_local, &tn),
            pre: RowWindow::from_two_rows(&pre_local, &pre_next),
            perm: RowWindow::from_two_rows(&perm_local, &perm_next),
            public: &public[i],
            challenges: &chal[i],
            perm_values: &tv,
            sels: [sels.is_first_row, sels.is_last_row, sels.is_transition],
            values: vec![],
        };
        gadget.eval_air_and_lookups(air, &mut pb, lk);
        let main = VerticalPair::new(RowMajorMatrixView::new_row(&bo.trace_local), RowMajorMatrixView::new_row(&tn));
        let preprocessed = VerticalPair::new(RowMajorMatrixView::new_row(&pre_local), RowMajorMatrixView::new_row(&pre_next));
        let inner = p3_uni_stark::VerifierConstraintFolder::<Config> {
            main,
            preprocessed,
            preprocessed_window: RowWindow::from_two_rows(&pre_local, &pre_next),
            periodic_values: &[],
            public_values: &public[i],
            is_first_row: sels.is_first_row,
            is_last_row: sels.is_last_row,
            is_transition: sels.is_transition,
            alpha,
            accumulator: EF::ZERO,
        };
        let mut folder = p3_batch_stark_c3n::folder::VerifierConstraintFolderWithLookups::<Config> {
            inner,
            permutation: VerticalPair::new(RowMajorMatrixView::new_row(&perm_local), RowMajorMatrixView::new_row(&perm_next)),
            permutation_challenges: &chal[i],
            permutation_values: &tv,
        };
        gadget.eval_air_and_lookups(air, &mut folder, lk);
        let folded = folder.inner.accumulator;
        let qdom = ext.try_create_disjoint_domain(1usize << (tb.log_trace + 1 + tb.log_qd)).expect("quotient domain");
        let domains = qdom.split_domains(tb.chunks);
        let zps: Vec<EF> = (0..domains.len())
            .map(|k| {
                domains.iter().enumerate().filter(|(j, _)| *j != k).map(|(_, o)| o.vanishing_poly_at_point(zeta) * o.vanishing_poly_at_point(domains[k].first_point()).inverse()).product::<EF>()
            })
            .collect();
        let chunk_vanishing: Vec<EF> = domains.iter().map(|d| d.vanishing_poly_at_point(zeta)).collect();
        let chunk_values: Vec<EF> = bo.quotient_chunks.iter().map(|ch| <EF as ExtensionField<F>>::from_ext_basis_coefficients(ch).unwrap()).collect();
        let quotient = p3_uni_stark::recompose_quotient_from_chunks::<Config>(&domains, &bo.quotient_chunks, zeta);
        let identity_holds = folded * sels.inv_vanishing == quotient;
        tables.push(NativeTable {
            trace_local: bo.trace_local.clone(),
            trace_next: tn.clone(),
            pre_local: pre_local.clone(),
            perm_local: perm_local.clone(),
            perm_next: perm_next.clone(),
            perm_local_flat: inst.permutation_local.clone(),
            perm_next_flat: perm_next_full.clone(),
            chunks: bo.quotient_chunks.clone(),
            public: public[i].clone(),
            challenges: chal[i].clone(),
            terminal,
            sels: [sels.is_first_row, sels.is_last_row, sels.is_transition, sels.inv_vanishing],
            z_h,
            constraints: pb.values.clone(),
            folded,
            chunk_vanishing,
            zps,
            chunk_values,
            quotient,
            identity_holds,
            verify_constraints: if identity_holds { "Ok".into() } else { "OodEvaluationMismatch".into() },
        });
    }
    let terminal_sum_zero = gadget.verify_terminal_sum(terminals).is_ok();
    NativeG1 { alpha, zeta, lookup_alpha: la, lookup_beta: lb, tables, terminal_sum_zero }
}

/// The key's common data for the recording configuration (the same values; the configuration type differs).
fn recast_common(c: &CommonData<Config>) -> CommonData<replay::RecConfig> {
    let pre = c.preprocessed.as_ref().map(|g| p3_batch_stark_c3n::common::GlobalPreprocessed::<replay::RecConfig> {
        commitment: g.commitment.clone(),
        instances: g.instances.clone(),
        matrix_to_instance: g.matrix_to_instance.clone(),
    });
    CommonData::new(pre, c.lookups.clone())
}

/// Run the child's native verifier (the C3n verifier with recording wrappers) and collect what the trace generator
/// needs: the duplexings, the multi-openings with their caps and restored paths, the witness stream, p3-fri's own
/// reduced openings per height and the native values of every identity. `expect` is the native verdict the child
/// must get: "accepted", or the error it must be rejected with (`OodEvaluationMismatch`, `TerminalSumNonZero`).
pub fn replay_child(def: &ChildDef, s: &Schedule, bytes: &[u8], pv: &[F], expect: &str) -> (ChildData, Value) {
    let (proof, rest) = postcard::take_from_bytes::<replay::RecProof>(bytes).expect("decode child proof");
    assert!(rest.is_empty(), "trailing bytes");
    let decoded: ChildProof = postcard::from_bytes(bytes).unwrap();
    assert_eq!(decoded.degree_bits, def.degrees(), "the proof's degree bits differ from the pinned shape");
    let prefix = def.prefix_elements(pv);
    let (cfg, rec) = replay::rec_config((LOG_BLOWUP, LOG_FINAL_POLY_LEN, MAX_LOG_ARITY, QUERIES), RANDOM_CODEWORDS, &prefix, None);
    let public = def.tables_public(pv);
    let rec_common = recast_common(&def.data.common);
    let t = Instant::now();
    let verdict = p3_batch_stark_c3n::verify_batch(&cfg, &def.airs, &proof, &public, &rec_common);
    let native_ms = ms(t);
    let native_verdict = format!("{verdict:?}");
    match expect {
        "accepted" => assert!(verdict.is_ok(), "native verifier rejected the child: {verdict:?}"),
        e => assert!(native_verdict.contains(e), "the child must be rejected with {e}: {verdict:?}"),
    }
    let perm_log = rec.perms.lock().unwrap().clone();
    let calls = rec.mmcs.lock().unwrap().clone();
    assert_eq!(pv.len(), s.num_public);
    // The challenges as the native transcript squeezed them (lanes 7..0 of the recorded duplexings' outputs).
    let out_ef = |row: usize| -> EF { to_ef(&core::array::from_fn(|k| perm_log[row].1[7 - k])) };
    let (alpha, zeta, pcs_alpha, la, lb) = (out_ef(s.alpha_row), out_ef(s.zeta_row), out_ef(s.pcs_alpha_row), out_ef(s.lookup_alpha_row), out_ef(s.lookup_beta_row));
    let next = next_row_columns_for_batch(def.airs.iter(), &def.data.common);
    let lqd: Vec<usize> = s.child.tables.iter().map(|t| t.log_qd).collect();
    let claims = claims_of(&child_config(&prefix), &decoded, &def.data.common, &next, zeta, &lqd);
    let wit = witness_stream(s, &decoded, &claims);
    // Every tree's multi-opening, found by its cap.
    let mut tree_caps: Vec<Vec<[F; 8]>> = vec![];
    for t in &s.trees {
        let cap: Vec<[F; 8]> = match t.kind {
            schedule::TreeKind::Input(0) => decoded.commitments.main.roots().to_vec(),
            schedule::TreeKind::Input(1) => decoded.commitments.quotient_chunks.roots().to_vec(),
            schedule::TreeKind::Input(2) => def.pre_cap(),
            schedule::TreeKind::Input(3) => decoded.commitments.permutation.as_ref().unwrap().roots().to_vec(),
            schedule::TreeKind::Fri(r) => decoded.opening_proof.1.commit_phase_commits[r].roots().to_vec(),
            schedule::TreeKind::Input(_) => unreachable!(),
        };
        tree_caps.push(cap);
    }
    let (mut leaves, mut sibs, mut idx, mut summary) = (vec![], vec![], vec![], vec![]);
    for (ti, cap) in tree_caps.iter().enumerate() {
        let t = &s.trees[ti];
        let found: Vec<&replay::MmcsCall> = calls.iter().filter(|c| &c.cap == cap).collect();
        assert_eq!(found.len(), 1, "tree {}: expected one native multi-opening", t.name);
        let call = found[0];
        assert!(call.accepted, "tree {}: the native multi-opening was rejected", t.name);
        let dims_want: Vec<(usize, usize)> = t.mats.iter().map(|m| (m.width, 1usize << m.log_height)).collect();
        assert_eq!(call.dims, dims_want, "tree {}: the native dimensions differ from the schedule's", t.name);
        sibs.push(replay::restore(call, SALT_ELEMS));
        leaves.push(
            (0..call.indices.len())
                .map(|q| {
                    t.groups
                        .iter()
                        .map(|g| g.mats.iter().flat_map(|&m| call.rows[q][m].iter().chain(call.salts[q][m].iter()).copied()).collect::<Vec<F>>())
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>(),
        );
        idx.push(call.indices.clone());
        summary.push(json!({"tree": t.name, "dims": call.dims, "queries": call.indices.len(),
            "distinct_indices": call.indices.iter().collect::<std::collections::BTreeSet<_>>().len(),
            "pruned_sibling_digests": call.pruned.sibling_hashes.len(), "walked_levels": t.mc, "cap_entries": cap.len()}));
    }
    assert_eq!(calls.len(), s.trees.len(), "unexpected extra multi-openings");
    // p3-fri's own reduced openings per height (open_inputs, verifier.rs l. 1093-1418).
    let perm = default_koalabear_poseidon2_16();
    let mmcs = Mmcs::new(Hash::new(perm.clone()), Compress::new(perm), CAP_HEIGHT, os_rng());
    let global_idx: Vec<usize> = idx[s.canon()].clone();
    let t = Instant::now();
    let ro = p3_fri::verifier::open_inputs::<F, EF, Mmcs, ChMmcs>(&child_fri_params(os_rng()), s.child.index_bits, &global_idx,
        &decoded.opening_proof.1.input_openings, pcs_alpha, &mmcs, &claims).expect("p3-fri open_inputs on the child proof");
    let open_inputs_ms = ms(t);
    let native_ro: Vec<BTreeMap<usize, EF>> = ro.into_iter().map(|v| v.into_iter().collect()).collect();
    // The native values of every table's identity and of the terminal check.
    let t = Instant::now();
    let native = native_g1(&s.child, &def.airs, &def.data.common, &next, &decoded.opened_values, &decoded.lookup_terminals, &public, alpha, zeta, la, lb);
    let identity_ms = ms(t);
    let init = [F::ZERO; 16];
    let pre_cap = def.pre_cap();
    let report = json!({"child_proof_sha256": sha256_hex(bytes), "child_proof_bytes": bytes.len(),
        "native_verifier": "p3_batch_stark_c3n::verify_batch with recording wrappers (RecPerm, RecMmcs), unchanged otherwise, with the pinned key",
        "native_verdict_of_the_replay": native_verdict, "expected": expect,
        "native_verify_ms": native_ms, "native_duplexings_recorded": perm_log.len(),
        "preprocessed_cap_is_the_pinned_one": pre_cap == s.child.pre_cap,
        "native_multi_openings": summary, "child_vk_digest": hex(&s.child.child_vk),
        "native_reduced_openings": {"function": "p3_fri::verifier::open_inputs (verifier.rs l. 1093-1418) on the child proof, per height",
            "queries": native_ro.len(), "heights": native_ro[0].keys().collect::<Vec<_>>(), "ms": open_inputs_ms},
        "native_identities": {"tables": native.tables.iter().map(|t| json!({"identity_holds": t.identity_holds, "constraints": t.constraints.len()})).collect::<Vec<_>>(),
            "terminal_sum_zero": native.terminal_sum_zero, "ms": identity_ms}});
    (ChildData { pv: pv.to_vec(), wit, pre_cap, leaves, sibs, idx, caps: tree_caps, perm_log, init, native_ro, native }, report)
}

// ---------- the constraint check's report ----------

pub fn check_report(s: &Schedule, trace: &RowMajorMatrix<F>, pv: &[F]) -> (usize, Value, Vec<String>, BTreeMap<String, std::collections::BTreeSet<String>>) {
    let (constraints, fails, unbalanced, live) = kernel::check(&s.air, trace, pv);
    let row_instr: std::collections::HashMap<usize, usize> =
        s.instr_row.iter().enumerate().filter(|(i, _)| s.program[*i].op != kernel::Op::Load).map(|(i, &r)| (r, i)).collect();
    let mut groups: BTreeMap<String, (usize, Vec<usize>, std::collections::BTreeSet<String>)> = Default::default();
    let mut roles: BTreeMap<String, std::collections::BTreeSet<String>> = Default::default();
    for f in &fails {
        let e = groups.entry(f.group.to_string()).or_default();
        e.0 += 1;
        if e.1.len() < 6 && !e.1.contains(&f.row) {
            e.1.push(f.row);
        }
        if f.group.starts_with("alu.") {
            if let Some(&i) = row_instr.get(&f.row) {
                let ins = &s.program[i];
                if e.2.len() < 12 {
                    e.2.insert(format!("{} (query {:?}, round {:?})", ins.role, ins.query, ins.round));
                }
                roles.entry(f.group.to_string()).or_default().insert(ins.role.to_string());
            }
        }
    }
    let mut names: Vec<String> = groups.keys().cloned().collect();
    if !unbalanced.is_empty() {
        names.push("bus.balance".into());
    }
    let bus: Vec<Value> = unbalanced
        .iter()
        .take(12)
        .map(|u| json!({"address": u.address, "value": s.value_at(u.address).map(|v| format!("{v:?}")), "net_count": u.net,
            "coordinate0": u.values.first(), "rows": u.rows.iter().take(4).map(|(r, slot, c)| json!([r, slot, c])).collect::<Vec<_>>()}))
        .collect();
    let first = fails.iter().min_by_key(|f| (f.row, f.constraint)).map(|f| json!({"row": f.row, "constraint": f.constraint, "group": f.group}));
    // Which identity (per table) and whether the global terminal check fail: their EQ rows.
    let base = s.k3b_range.0 + s.k3b_unpacks();
    let eq_rows: std::collections::BTreeSet<usize> = fails.iter().filter(|f| f.group == "alu.eq").map(|f| f.row).collect();
    let identities: Vec<Value> = s.child.program.tables.iter().enumerate().map(|(t, o)| {
        let row = s.instr_row[base + o.identity];
        json!({"table": s.child.tables[t].name, "row": row, "fails": eq_rows.contains(&row)})
    }).collect();
    let terminal_row = s.instr_row[base + s.child.program.terminal_check];
    let doc = json!({"constraints_per_row": constraints, "rows": s.n, "constraint_evaluations": constraints * s.n,
        "failing_constraint_evaluations": fails.len(), "first_failure": first,
        "identity_checks": identities, "terminal_check": {"row": terminal_row, "fails": eq_rows.contains(&terminal_row)},
        "groups": groups.iter().map(|(g, (n, rows, r))| json!({"group": g, "failing_evaluations": n, "first_rows": rows, "alu_roles": r})).collect::<Vec<_>>(),
        "bus": {"messages_with_nonzero_count": live, "unbalanced_tuples": unbalanced.len(), "first_unbalanced": bus},
        "violated": names});
    (constraints, doc, names, roles)
}

fn pv_json(pv: &[F]) -> Value {
    json!(pv.iter().map(|v| v.as_canonical_u32()).collect::<Vec<_>>())
}

// ---------- modes ----------

/// L0' v2's key recomputed and checked against vk.json; its recorded proof decoded strictly and verified natively.
fn l0p2_native_mode(in_dir: &Path, out: &Path) {
    fs::create_dir(out).expect("fresh output directory required");
    let t = Instant::now();
    let def = l0p2_def(in_dir);
    let def_ms = ms(t);
    let bytes = fs::read(in_dir.join("l0p2.postcard")).unwrap();
    let metrics = read_json(&in_dir.join("metrics.json"));
    assert_eq!(metrics["proof_sha256"], json!(sha256_hex(&bytes)), "the proof is L0' v2's recorded one");
    assert_eq!(metrics["params"]["pi_bytes"], json!(hex(&def.statement.iter().map(|v| v.as_canonical_u32() as u8).collect::<Vec<_>>())), "the statement is L0' v2's");
    let t = Instant::now();
    let (proof, rest) = postcard::take_from_bytes::<ChildProof>(&bytes).expect("strict decoding");
    assert!(rest.is_empty(), "trailing bytes");
    let decode_ms = ms(t);
    assert_eq!(proof.degree_bits, def.degrees());
    let t = Instant::now();
    let cfg = child_config(&def.prefix_elements(&def.statement));
    let r = p3_batch_stark_c3n::verify_batch(&cfg, &def.airs, &proof, &def.tables_public(&def.statement), &def.data.common);
    let verify_ms = ms(t);
    let doc = json!({"schema": SCHEMA, "review": REVIEW, "tier": TIER,
        "what": "L0' v2's key recomputed in the B1 binary (the pinned outer-verifier graph) and compared with L0' v2's vk.json; L0' v2's recorded proof decoded strictly and verified by the C3n verifier compiled in this graph",
        "child": def.name, "child_vk_digest_b1": hex(&def.child_vk), "definition": def.record,
        "proof_bytes": bytes.len(), "proof_sha256": sha256_hex(&bytes), "native_accepted": r.is_ok(), "native_error": r.as_ref().err().map(|e| format!("{e:?}")),
        "timings_ms": {"build_key_and_check": def_ms, "decode": decode_ms, "verify": verify_ms}, "peak_rss_kib": peak_rss_kib()});
    save(&out.join("l0p2-native.json"), &serde_json::to_vec_pretty(&doc).unwrap());
    event(json!({"phase": "l0p2_native_done", "accepted": r.is_ok(), "vk_check": doc["definition"]["vk_check_against_vk_json"]["all_equal"], "verify_ms": verify_ms}));
    assert!(r.is_ok(), "L0' v2's proof must verify natively: {r:?}");
}

fn read_pi(path: &Path) -> Vec<u8> {
    let text = fs::read_to_string(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    let t = text.trim();
    assert_eq!(t.len(), 2 * 198, "PI file must hold 198 bytes in hex");
    unhex(t)
}
/// The g1b children's statement: the pinned relation crate's PI198 fixture.
fn g1b_pi(in_dir: &Path) -> Vec<u8> {
    read_pi(&in_dir.join("../relation/fixtures/pi198.hex"))
}

/// The compiled program file and the differential test against the native verifier's functions at random points.
fn compile_mode(kind: Kind, in_dir: &Path, out: &Path, points: usize) {
    fs::create_dir(out).expect("fresh output directory required");
    let def = child_def(kind, in_dir, &g1b_pi(in_dir));
    let t = Instant::now();
    let spec = child_spec(&def);
    let compile_ms = ms(t);
    let p = &spec.program;
    let bytes = p.file_bytes(&hex(&spec.child_vk));
    assert_eq!(sha256_hex(&bytes), hex(&spec.program_sha256));
    save(&out.join(format!("program-{}.json", kind.name())), &bytes);
    let mut rng = StdRng::seed_from_u64(0x6231_d1ff);
    let rand_ef = |rng: &mut StdRng| EF::from_basis_coefficients_fn(|_| rng.random::<F>());
    let (_, unfactored, _) = compile_child(&def, Options { factor_min: 0 }, None);
    // A program compiled without one LogUp constraint: the fraction pin of the first lookup of the last table with lookups.
    let drop_t = (0..spec.tables.len()).rev().find(|&t| spec.tables[t].perm_width > 0).unwrap();
    let (_, dropped, _) = compile_child(&def, Options::default(), Some((drop_t, 0)));
    let next = next_row_columns_for_batch(def.airs.iter(), &def.data.common);
    let (mut agree, mut agree_identity, mut unfactored_agree, mut dropped_differs) = (0, 0, 0, 0);
    let t = Instant::now();
    for _ in 0..points {
        // Random opened values of every table (only the columns the derived sets open at zeta * g), random challenges.
        let mut ov_inst = vec![];
        let mut terminals = vec![];
        let mut public = vec![];
        for (i, tb) in spec.tables.iter().enumerate() {
            let tl: Vec<EF> = (0..tb.width).map(|_| rand_ef(&mut rng)).collect();
            let tn: Vec<EF> = next[i].main.iter().map(|_| rand_ef(&mut rng)).collect();
            let pre = (tb.pre_width > 0).then(|| p3_uni_stark::PreprocessedOpenedValues { local: (0..tb.pre_width).map(|_| rand_ef(&mut rng)).collect(), next: None });
            let pl: Vec<EF> = (0..8 * tb.perm_width).map(|_| rand_ef(&mut rng)).collect();
            let pn: Vec<EF> = next[i].permutation.iter().flat_map(|_| (0..8).map(|_| rand_ef(&mut rng)).collect::<Vec<_>>()).collect();
            let chunks: Vec<Vec<EF>> = (0..tb.chunks).map(|_| (0..8).map(|_| rand_ef(&mut rng)).collect()).collect();
            ov_inst.push((tl, tn, pre, pl, pn, chunks));
            terminals.push((tb.perm_width > 0).then(|| p3_lookup::LookupTerminal(rand_ef(&mut rng))));
            public.push((0..tb.public.len()).map(|_| rng.random::<F>()).collect::<Vec<F>>());
        }
        let (alpha, zeta, la, lb) = (rand_ef(&mut rng), rand_ef(&mut rng), rand_ef(&mut rng), rand_ef(&mut rng));
        let build_ov = |chunk_fix: &dyn Fn(usize, &mut Vec<Vec<EF>>)| p3_batch_stark_c3n::BatchOpenedValues {
            instances: ov_inst
                .iter()
                .enumerate()
                .map(|(t, (tl, tn, pre, pl, pn, ch))| {
                    let mut ch = ch.clone();
                    chunk_fix(t, &mut ch);
                    p3_batch_stark_c3n::proof::OpenedValuesWithLookups {
                        base_opened_values: p3_uni_stark::OpenedValues {
                            trace_local: tl.clone(),
                            trace_next: (!tn.is_empty()).then(|| tn.clone()),
                            preprocessed: pre.clone(),
                            quotient_chunks: ch,
                            random: None,
                        },
                        permutation_local: pl.clone(),
                        permutation_next: pn.clone(),
                    }
                })
                .collect(),
        };
        let ov = build_ov(&|_, _| {});
        let nk = native_g1(&spec, &def.airs, &def.data.common, &next, &ov, &terminals, &public, alpha, zeta, la, lb);
        let input = |i: Input| -> EF {
            match i {
                Input::TraceLocal(t, k) => nk.tables[t].trace_local[k],
                Input::TraceNext(t, k) => nk.tables[t].trace_next[k],
                Input::PreLocal(t, k) => nk.tables[t].pre_local[k],
                Input::PreNext(..) => unreachable!(),
                Input::PermLocal(t, j, k) => nk.tables[t].perm_local_flat[8 * j + k],
                Input::PermNext(t, j, k) => nk.tables[t].perm_next_flat[8 * j + k],
                Input::Public(t, k) => EF::from(nk.tables[t].public[k]),
                Input::Alpha => alpha,
                Input::Zeta => zeta,
                Input::LookupAlpha => la,
                Input::LookupBeta => lb,
                Input::Terminal(t) => nk.tables[t].terminal.unwrap(),
                Input::Chunk(t, c, k) => nk.tables[t].chunks[c][k],
            }
        };
        let (v, eqs) = p.eval(&input);
        let eq_of = |i: usize| eqs.iter().find(|e| e.0 == i).unwrap().1;
        let (vu, _) = unfactored.eval(&input);
        for (t, o) in p.tables.iter().enumerate() {
            let got = |id: usize| v[id].expect("value");
            let nt = &nk.tables[t];
            assert_eq!([got(o.is_first_row), got(o.is_last_row), got(o.is_transition), got(o.inv_vanishing)], nt.sels, "table {t}: selectors");
            // Every constraint value, base and LogUp, against the AIR's own evaluation at the point.
            for (k, cv) in o.constraints.iter().enumerate() {
                let val = match cv.expect("every constraint compiled") {
                    compiler::CVal::Plain(id) => got(id),
                    compiler::CVal::Factored(sl, id) => {
                        let sel = match sl {
                            compiler::Sel::First => nt.sels[0],
                            compiler::Sel::Last => nt.sels[1],
                            compiler::Sel::Transition => nt.sels[2],
                        };
                        sel * got(id)
                    }
                };
                assert_eq!(val, nt.constraints[k], "table {t} constraint {k}");
            }
            assert_eq!(got(o.folded), nt.folded, "table {t}: folded");
            assert_eq!(got(o.quotient), nt.quotient, "table {t}: quotient");
            assert_eq!(eq_of(o.identity), nt.identity_holds, "table {t}: identity verdict");
            assert_eq!(vu[unfactored.tables[t].folded].unwrap(), nt.folded, "table {t}: the unfactored program's fold");
        }
        assert_eq!(eq_of(p.terminal_check), nk.terminal_sum_zero, "terminal-sum verdict");
        let (vd, _) = dropped.eval(&input);
        if vd[dropped.tables[drop_t].folded].unwrap() != nk.tables[drop_t].folded {
            dropped_differs += 1;
        }
        agree += 1;
        unfactored_agree += 1;
        // The same point made consistent: every table's chunk 0 coordinate 0 chosen so that its identity holds.
        let fixes: Vec<EF> = nk
            .tables
            .iter()
            .map(|nt| {
                let target = nt.folded * nt.sels[3];
                let rest: EF = (1..nt.chunk_values.len()).map(|c| nt.zps[c] * nt.chunk_values[c]).sum();
                let q0 = (target - rest) * nt.zps[0].inverse();
                let x = EF::from_basis_coefficients_fn(|k| if k == 1 { F::ONE } else { F::ZERO });
                let others: EF = (1..8).map(|k| x.exp_u64(k as u64) * nt.chunks[0][k]).sum();
                q0 - others
            })
            .collect();
        let ov2 = build_ov(&|t, ch| ch[0][0] = fixes[t]);
        let nk2 = native_g1(&spec, &def.airs, &def.data.common, &next, &ov2, &terminals, &public, alpha, zeta, la, lb);
        assert!(nk2.tables.iter().all(|t| t.identity_holds), "the adjusted point satisfies every identity natively");
        let input2 = |i: Input| -> EF {
            match i {
                Input::Chunk(t, c, k) => nk2.tables[t].chunks[c][k],
                other => input(other),
            }
        };
        let (_, eqs2) = p.eval(&input2);
        assert!(p.tables.iter().all(|o| eqs2.iter().find(|e| e.0 == o.identity).unwrap().1), "the program accepts the adjusted point");
        agree_identity += 1;
    }
    let diff_ms = ms(t);
    // zeta in a table's trace domain: the native vanishing value is zero and the program's inverse of Z_H has no value.
    let mut in_domain = vec![];
    for (t, tb) in spec.tables.iter().enumerate() {
        for e in [0u64, 3] {
            let w = <F as p3_field::TwoAdicField>::two_adic_generator(tb.log_trace).exp_u64(e);
            let zeta = EF::from(w);
            let init = p3_field::coset::TwoAdicMultiplicativeCoset::new(F::ONE, tb.log_trace).unwrap();
            let zero = init.vanishing_poly_at_point(zeta).is_zero();
            let input = |i: Input| -> EF {
                match i {
                    Input::Zeta => zeta,
                    _ => EF::from_basis_coefficients_fn(|k| F::from_u32(1 + k as u32 + 17 * t as u32)),
                }
            };
            let (v, _) = p.eval(&input);
            let inv = v[p.tables[t].inv_vanishing];
            assert!(zero && inv.is_none(), "zeta = w_t^{e} in H_t: Z_H = 0 natively and no inverse in the program");
            in_domain.push(json!({"table": t, "zeta": format!("w_table{t}^{e}"), "native_vanishing_is_zero": zero, "program_inverse_of_z_h": Value::Null}));
        }
    }
    let gz = gzip(&bytes);
    save(&out.join(format!("program-{}.json.gz", kind.name())), &gz);
    let (_, _, _, bus_names) = bus_layout(&def.data.common);
    let doc = json!({"schema": SCHEMA, "review": REVIEW, "tier": TIER, "child": def.name,
        "compiled_program_sha256": hex(&spec.program_sha256), "compiled_program_bytes": bytes.len(), "compiled_program_gzip_bytes": gz.len(),
        "compile_ms": compile_ms, "buses": bus_names, "max_message_width": spec.max_message_width,
        "stats": p.stats, "unfactored_program": unfactored.stats,
        "differential": {"points": points, "seed": "0x6231d1ff",
            "per_table_selectors_constraints_folded_quotient_identity_and_the_terminal_verdict_equal_native": agree,
            "consistent_points_accepted_by_both": agree_identity, "unfactored_program_folds_equal_native": unfactored_agree,
            "dropped_lookup_constraint": {"table": spec.tables[drop_t].name, "extension_constraint": 0, "instructions": dropped.instrs.len(),
                "folds_differing_from_native": dropped_differs},
            "native_functions": "selectors_at_point (p3-commit), the AIR's eval through the LogUp gadget (PointBuilder) for every constraint, VerifierConstraintFolderWithLookups (p3_batch_stark_c3n folder.rs, p3-lookup), recompose_quotient_from_chunks (p3-uni-stark), verify_terminal_sum (p3-lookup)",
            "ms": diff_ms},
        "zeta_in_h": in_domain, "peak_rss_kib": peak_rss_kib()});
    save(&out.join("differential.json"), &serde_json::to_vec_pretty(&doc).unwrap());
    event(json!({"phase": "compile_done", "child": kind.name(), "instructions": p.instrs.len(), "values": p.n_values, "live_values_max": p.stats["live_values_max"],
        "sha256": hex(&spec.program_sha256), "differential_points": agree, "consistent": agree_identity, "dropped_differs": dropped_differs,
        "compile_ms": compile_ms}));
}

/// B's schedule for a child: the shape, the interface map, the compiled program's file, B's key (the seeded
/// preprocessed commitment, pinned in vk.json) and verifier-key digest, and the program listing (gzipped).
fn schedule_mode(kind: Kind, in_dir: &Path, out: &Path) {
    fs::create_dir(out).expect("fresh output directory required");
    let def = child_def(kind, in_dir, &g1b_pi(in_dir));
    let t = Instant::now();
    let spec = child_spec(&def);
    let compile_ms = ms(t);
    let t = Instant::now();
    let s = Schedule::build(&spec);
    let build_ms = ms(t);
    let rss_before_keygen = peak_rss_kib();
    let (data, key) = b2_keygen(&s);
    let rss_after_keygen = peak_rss_kib();
    let vk = b2_vk_digest(&s, &key);
    save(&out.join(format!("program-{}.json", kind.name())), &spec.program.file_bytes(&hex(&spec.child_vk)));
    save(&out.join("interface.json"), &serde_json::to_vec_pretty(&s.interface()).unwrap());
    let listing = serde_json::to_vec(&s.program_json()).unwrap();
    save(&out.join("program-listing.json.gz"), &gzip(&listing));
    let vk_doc = b2_vk_json(&s, &data.common, &key, &vk);
    save(&out.join("vk.json"), &serde_json::to_vec_pretty(&vk_doc).unwrap());
    let shape = shape_doc(&s, &def, &vk, &data.common);
    drop(data);
    // Determinism of the key: a second key generation from the same seed gives the same commitment.
    let (_, key2) = b2_keygen(&s);
    let deterministic = key2.commitment.roots() == key.commitment.roots();
    let pre_sha = {
        let mut h = Sha256::new();
        for col in &s.air.pre {
            for v in col {
                h.update(v.as_canonical_u32().to_le_bytes());
            }
        }
        hex(&h.finalize())
    };
    let doc = json!({"schema": SCHEMA, "review": REVIEW, "tier": TIER, "shape": shape,
        "key": {"b2_vk_digest": hex(&vk), "air_digest": hex(&key.air_digest), "program_digest": hex(&key.program_digest),
            "salt_seed": hex(&key.salt_seed), "commitment_keccak256": vk_doc["preprocessed"]["commitment_keccak256"],
            "commitment_cap": vk_doc["preprocessed"]["cap"], "keygen_ms": key.keygen_ms, "second_keygen_same_commitment": deterministic,
            "peak_rss_kib_before_keygen": rss_before_keygen, "peak_rss_kib_after_keygen": rss_after_keygen,
            "preprocessed_columns_sha256_u32le_column_major": pre_sha},
        "listing_uncompressed_bytes": listing.len(), "listing_uncompressed_sha256": sha256_hex(&listing),
        "timings_ms": {"key_and_compile": compile_ms, "schedule": build_ms, "b_keygen": key.keygen_ms}, "peak_rss_kib": peak_rss_kib()});
    save(&out.join("schedule.json"), &serde_json::to_vec_pretty(&doc).unwrap());
    event(json!({"phase": "schedule_done", "child": kind.name(), "n": s.n, "used_rows": used_rows(&s), "margin_rows": s.n - used_rows(&s),
        "k1_rows": s.used_rows, "main_width": kernel::WIDTH, "preprocessed": s.air.pre.len(), "periodic": 0, "alu": s.program.len(),
        "transcript_rows": s.t_rows, "per_query": s.block_rows, "b2_vk_digest": hex(&vk), "commitment_keccak256": vk_doc["preprocessed"]["commitment_keccak256"],
        "keygen_ms": key.keygen_ms, "deterministic": deterministic}));
    assert!(deterministic, "the seeded key generation is deterministic");
}

/// The rows B uses: K1's (transcript and query blocks) or the last row holding an instruction or a reserved slot.
pub fn used_rows(s: &Schedule) -> usize {
    let last_instr = s.instr_row.iter().copied().max().unwrap_or(0);
    s.used_rows.max(last_instr + 1)
}

/// B's exact shape: rows, columns (main, preprocessed, periodic), constraints, bus traffic, the program's parts.
fn shape_doc(s: &Schedule, def: &ChildDef, vk: &[u8; 32], common: &KCommon) -> Value {
    let lookups: &[p3_lookup::Lookup<F>] = &common.lookups[0];
    let layout = AirLayout::from_air(&s.air);
    let gadget = LogUpGadget::new();
    let (base, ext) = p3_batch_stark_c3::symbolic::get_symbolic_constraints::<F, EF, _, _>(&s.air, layout, lookups, &gadget);
    let log_chunks = p3_batch_stark_c3::symbolic::get_log_num_quotient_chunks::<F, EF, _, _>(&s.air, layout, s.n, lookups, 1, &gadget);
    let degree = p3_batch_stark_c3::symbolic::get_max_constraint_degree::<F, EF, _, _>(&s.air, layout, s.n, lookups, &gadget);
    let (base0, _) = p3_batch_stark_c3::symbolic::get_symbolic_constraints::<F, EF, _, _>(&s.air, layout, &[], &gadget);
    let tags = kernel::constraint_tags(&s.air, s.num_public);
    assert_eq!(tags.len(), base0.len(), "the tag list and the symbolic constraints differ in length");
    let mut by_group: BTreeMap<&str, (usize, usize)> = Default::default();
    for (tag, c) in tags.iter().zip(&base0) {
        let e = by_group.entry(tag).or_default();
        e.0 += 1;
        e.1 = e.1.max(c.degree_multiple());
    }
    let mut k_hist = [0usize; 9];
    for r in &s.trows {
        k_hist[r.k] += 1;
    }
    let aux = lookups.len() + 1;
    let reads: usize = s.reads.values().map(|&v| v as usize).sum();
    let weight: u64 = common.lookups[0].total_count_weight();
    let bound = p3_lookup::check_multiplicity_height_bound(&common.lookups, &[s.n]);
    let counts = s.program_counts();
    let used = used_rows(s);
    let reserved: std::collections::BTreeSet<usize> = s.cap_reads.iter().map(|(r, _)| *r).chain(
        s.program.iter().zip(&s.instr_row).filter(|(i, _)| i.op == kernel::Op::Load).map(|(_, &r)| r)).collect();
    let reserved_below = reserved.iter().filter(|&&r| r < used).count();
    let non_load = s.program.iter().filter(|i| i.op != kernel::Op::Load).count();
    let public_selectors = s.air.pre_names.iter().filter(|n| n.starts_with("public_row")).count();
    json!({"child": {"name": def.name, "kind": def.kind.name(),
            "tables": s.child.tables.iter().map(|t| json!({"name": t.name, "log_trace": t.log_trace, "width": t.width,
                "preprocessed_width": t.pre_width, "public_values": t.public.len(), "next_main": t.next_main.len(), "next_preprocessed": t.next_pre.len(),
                "next_permutation_ef8": t.next_perm, "permutation_width_ef8": t.perm_width, "lookup_buses": t.lookup_bus,
                "log_quotient_degree": t.log_qd, "chunks": t.chunks})).collect::<Vec<_>>(),
            "index_bits": s.child.index_bits, "fri_log_arities": s.child.fri_log_arities, "log_final_poly_len": s.child.log_final_poly_len,
            "queries": s.child.num_queries, "child_vk_digest": hex(&s.child.child_vk), "cap_height": CAP_HEIGHT, "buses": s.child.num_buses,
            "max_message_width": s.child.max_message_width,
            "seed_elements": {"batch": s.child.seeds[0].len(), "pcs": s.child.seeds[1].len(), "fri": s.child.seeds[2].len()},
            "prefix": s.child.prefix.iter().map(|p| p.name().to_string()).collect::<Vec<_>>()},
        "compiled_program": {"sha256": hex(&s.child.program_sha256), "instructions": s.child.program.instrs.len(), "stats": s.child.program.stats},
        "rows": {"n": s.n, "log_n": s.log_n, "used": used, "margin_to_n": s.n - used, "share_of_n": used as f64 / s.n as f64,
            "k1_rows": s.used_rows, "transcript": s.t_rows, "per_query": s.block_rows, "query_blocks": s.q * s.block_rows,
            "per_query_per_tree": s.trees.iter().map(|t| json!({"tree": t.name, "rows": t.block_len, "groups": t.groups.iter().map(|g| g.lh_rows).collect::<Vec<_>>(),
                "compressions": t.mc, "injections": t.nodes.iter().filter(|(_, n)| matches!(n, schedule::Node::Inj(_))).count(), "cap_rows": t.cap_rows,
                "index_bits_on_leaf_rows": t.consume_lh, "index_bits_below": t.skip, "start": format!("{:?}", t.start)})).collect::<Vec<_>>(),
            "alu_instructions": s.program.len(), "alu_instructions_without_loads": non_load,
            "reserved_rows": {"cap_reads": s.cap_reads.len(), "loads": s.q, "distinct_rows": reserved.len(), "below_the_last_instruction": reserved_below},
            "rows_used_rule": "non-LOAD instructions on non-reserved rows, from row 0: the last instruction's row + 1 = non-LOAD instructions + reserved rows below it",
            "last_instruction_row": s.instr_row.iter().max(), "transcript_rows_by_absorbed_count": k_hist},
        "columns": {"main_width": kernel::WIDTH, "poseidon2": kernel::P2W, "bit_acc": 2, "hi_bits": kernel::HI_BITS, "hi_products": kernel::TP_N,
            "xq": 1, "base_lane_x": 1, "base_value_v": 1, "alu": 32, "ra_address_aa": 1, "w2_multiplicity_mw": 1, "w2_value": 8,
            "deep_accumulator": 8, "batching_challenge_powers": 32,
            "preprocessed": s.air.pre.len(), "preprocessed_control": s.air.pre.len() - public_selectors, "preprocessed_public_row_selectors": public_selectors,
            "preprocessed_bus_control": kernel::NCTRL, "periodic": 0, "public_values": s.num_public,
            "permutation_columns_ef8": aux, "permutation_columns_base": 8 * aux},
        "bus": {"name": kernel::BUS, "interaction_slots_per_row": kernel::SLOTS.len(), "slots": kernel::SLOTS,
            "lookups_after_packing": lookups.iter().map(|l| json!({"kind": format!("{:?}", l.kind), "column": l.column,
                "tuples": l.elements.len(), "tuple_width": l.elements.first().map(Vec::len), "count_weight": l.count_weight, "fraction_pin_degree": gadget.constraint_degree(l)})).collect::<Vec<_>>(),
            "addresses_written": s.writer.len(), "reads_scheduled": reads, "cap_reads_dynamic": s.cap_reads.len(),
            "injection_reads_ri": s.inj_reads.len(), "w2_writes": s.w2port.len(),
            "largest_scheduled_multiplicity": s.reads.values().max(),
            "multiplicity_height_bound": {"total_count_weight": weight, "base_trace_height": s.n, "weighted_sum": weight * s.n as u64,
                "check_multiplicity_height_bound": format!("{bound:?}")}},
        "deep": {"claims": s.n_claims(), "claim_runs": s.claim_runs.len(), "chains": s.chains.len(), "joined_matrices": s.chains.iter().map(|c| c.matrices.len() - 1).sum::<usize>(),
            "height_point_pairs": s.hz.len(), "chain_value_rows_per_query": s.chains.iter().map(|c| c.value_rows.len()).sum::<usize>(),
            "pass_rows_per_query": s.chains.iter().map(|c| c.pass_rows.len()).sum::<usize>(),
            "opened_values_per_query": s.chains.iter().map(|c| c.value_rows.iter().map(|(_, l)| l.len()).sum::<usize>()).sum::<usize>(),
            "rollins": s.rollins.iter().map(|(r, h)| json!({"after_round": r, "log_height": h, "arity": 1usize << s.child.fri_log_arities[*r]})).collect::<Vec<_>>()},
        "alu": counts,
        "constraints": {"base": base.len(), "extension": ext.len(), "max_degree_with_lookups": degree, "quotient_chunks_with_zk": 1usize << (log_chunks + 1),
            "by_group": by_group.iter().map(|(g, (n, d))| json!({"group": g, "constraints": n, "max_degree": d})).collect::<Vec<_>>(),
            "public_binding_terms": s.air.pub_terms.iter().map(|t| t.len()).sum::<usize>()},
        "b2_vk_digest": hex(vk), "b_proof_parameters": b2_params()})
}

/// B's honest trace on a child proof: B's key recomputed and checked against the pinned vk.json, the replay, the trace,
/// every native cross-check, the constraint and bus check on every row, the LogUp check (p3-lookup's permutation trace
/// with the preprocessed trace, its constraints, its terminal); the trace's hash.
fn trace_mode(kind: Kind, in_dir: &Path, proof_path: &Path, vk_path: &Path, out: &Path, save_path: Option<&Path>) {
    fs::create_dir(out).expect("fresh output directory required");
    tracegen::ef_selftest();
    let t0 = Instant::now();
    let pi = g1b_pi(in_dir);
    let def = child_def(kind, in_dir, &pi);
    let spec = child_spec(&def);
    let s = Schedule::build(&spec);
    let schedule_ms = ms(t0);
    let (data, key) = b2_keygen(&s);
    let vk = b2_vk_digest(&s, &key);
    let vk_check = check_b2_vk(&b2_vk_json(&s, &data.common, &key, &vk), &read_json(vk_path));
    assert_eq!(vk_check["all_equal"], json!(true), "B's recomputed key differs from the pinned vk.json: {vk_check}");
    let lookups = data.common.lookups[0].clone();
    let shape = shape_doc(&s, &def, &vk, &data.common);
    drop(data);
    let bytes = fs::read(proof_path).unwrap();
    let t = Instant::now();
    let (cd, replay_report) = replay_child(&def, &s, &bytes, &def.statement, "accepted");
    let replay_ms = ms(t);
    let t = Instant::now();
    let (kt, _xs, honest_report) = tracegen::honest(&s, &cd);
    let trace = kt.finalize();
    let tracegen_ms = ms(t);
    let t = Instant::now();
    let (constraints, check, names, _) = check_report(&s, &trace, &cd.pv);
    let check_ms = ms(t);
    let t = Instant::now();
    let lcheck = lcheck::check(&s.air, &trace, &cd.pv, &lookups, 0x6232_10c0);
    let lcheck_ms = ms(t);
    drop(kt);
    let t = Instant::now();
    let mut tb = Vec::with_capacity(trace.values.len() * 4);
    for v in &trace.values {
        tb.extend_from_slice(&v.as_canonical_u32().to_le_bytes());
    }
    let trace_sha = sha256_hex(&tb);
    if let Some(p) = save_path {
        save(&p.with_extension("trace.u32le"), &tb);
    }
    let hash_ms = ms(t);
    let ok = names.is_empty() && lcheck["all_zero"] == json!(true) && lcheck["terminal_is_zero"] == json!(true);
    let doc = json!({"schema": SCHEMA, "review": REVIEW, "tier": TIER, "n": 1, "child": def.name,
        "result": if ok { "the honest trace satisfies every constraint of B (base constraints on every row, the bus balanced, the LogUp constraints and terminal)" } else { "VIOLATED" },
        "b2_vk_digest": hex(&vk), "key_recomputed_against_vk_json": vk_check, "compiled_program_sha256": hex(&s.child.program_sha256), "statement": pv_json(&cd.pv),
        "statement_sha256": sha256_hex(&cd.pv.iter().flat_map(|v| v.as_canonical_u32().to_le_bytes()).collect::<Vec<u8>>()),
        "replay": replay_report, "honest_generation": honest_report,
        "constraint_check": {"constraints_per_row": constraints, "check": check},
        "logup_check": lcheck,
        "trace": {"rows": trace.height(), "width": trace.width(), "bytes_u32le": tb.len(), "sha256_u32le_row_major": trace_sha,
            "stored": save_path.map(|p| p.with_extension("trace.u32le").display().to_string())},
        "shape": shape,
        "timings_ms": {"key_compile_schedule": schedule_ms, "b_keygen": key.keygen_ms, "replay_open_inputs_identities": replay_ms,
            "trace_generation_and_native_checks": tracegen_ms, "constraint_and_bus_check": check_ms, "logup_check": lcheck_ms, "hash_and_save": hash_ms},
        "peak_rss_kib": peak_rss_kib()});
    save(&out.join("trace-report.json"), &serde_json::to_vec_pretty(&doc).unwrap());
    event(json!({"phase": "trace_done", "child": kind.name(), "ok": ok, "violated": names, "logup_all_zero": lcheck["all_zero"],
        "terminal_zero": lcheck["terminal_is_zero"], "n": s.n, "used_rows": used_rows(&s), "trace_sha256": trace_sha, "b2_vk_digest": hex(&vk),
        "peak_rss_kib": peak_rss_kib()}));
    if !ok {
        std::process::exit(3);
    }
}

/// The kinds of g1b child the child mode proves.
#[derive(Clone, Copy, Debug)]
enum G1bKind {
    Honest,
    Cell(usize, usize, usize),
    Unbalanced(usize),
}

fn g1b_child_mode(pi_path: &Path, out: &Path, kind: G1bKind) {
    fs::create_dir(out).expect("fresh output directory required");
    let pi = read_pi(pi_path);
    let def = g1b_def(&pi);
    let fault = match kind {
        G1bKind::Cell(t, r, c) => Some(Fault::Cell(t, r, c)),
        G1bKind::Unbalanced(k) => Some(Fault::Unbalanced(k)),
        G1bKind::Honest => None,
    };
    let t = Instant::now();
    let traces = child::traces(&pi, fault, 0);
    let trace_ms = ms(t);
    let g1: Vec<G1Air> = child::airs();
    let public = def.tables_public(&def.statement);
    let prefix = def.prefix_elements(&def.statement);
    let t = Instant::now();
    let cfg = child_config(&prefix);
    let trefs = [&traces[0], &traces[1], &traces[2]];
    let instances = StarkInstance::new_multiple(&g1, &trefs, &public);
    let proof = p3_batch_stark_c3n::prove_batch(&cfg, &instances, &g1b_keygen(&g1)).expect("child prover");
    let prove_ms = ms(t);
    let bytes = postcard::to_allocvec(&proof).unwrap();
    save(&out.join("proof.postcard"), &bytes);
    let decoded: ChildProof = postcard::from_bytes(&bytes).expect("decode");
    let t = Instant::now();
    let verdict = p3_batch_stark_c3n::verify_batch(&child_config(&prefix), &def.airs, &decoded, &public, &def.data.common);
    let verify_ms = ms(t);
    let native = match &verdict {
        Ok(()) => "accepted".to_string(),
        Err(e) => format!("rejected: {e:?}"),
    };
    let expect = match kind {
        G1bKind::Honest => {
            assert!(verdict.is_ok(), "the child must verify natively: {verdict:?}");
            "accepted"
        }
        G1bKind::Cell(t, _, _) => {
            let s = format!("{verdict:?}");
            assert!(s.contains("OodEvaluationMismatch") && s.contains(&format!("index: Some({t})")), "table {t}'s identity only: {verdict:?}");
            "OodEvaluationMismatch"
        }
        G1bKind::Unbalanced(_) => {
            assert!(format!("{verdict:?}").contains("TerminalSumNonZero"), "the terminal sum only: {verdict:?}");
            "TerminalSumNonZero"
        }
    };
    let run = json!({"schema": SCHEMA, "review": REVIEW, "tier": TIER, "child": def.name, "kind": format!("{kind:?}"),
        "pi_hex": hex(&pi), "statement": pv_json(&def.statement), "vk_digest": hex(&def.child_vk), "definition": def.record,
        "prover": "p3_batch_stark_c3n::prove_batch (L0' v2's C3n copy of p3-batch-stark 0.9.0-rc.1)",
        "native_verifier": "p3_batch_stark_c3n::verify_batch with the pinned key", "native_verdict": native, "native_expected": expect,
        "proof_bytes": bytes.len(), "proof_sha256": sha256_hex(&bytes),
        "fri": {"log_blowup": LOG_BLOWUP, "log_final_poly_len": LOG_FINAL_POLY_LEN, "max_log_arity": MAX_LOG_ARITY, "queries": QUERIES,
            "pow_bits": 0, "random_codewords": RANDOM_CODEWORDS, "salt_elements": SALT_ELEMS, "digest_elements": DIGEST_ELEMS, "cap_height": CAP_HEIGHT},
        "degree_bits": def.degrees(), "timings_ms": {"trace": trace_ms, "prove": prove_ms, "verify": verify_ms}, "peak_rss_kib": peak_rss_kib()});
    save(&out.join("run.json"), &serde_json::to_vec_pretty(&run).unwrap());
    event(json!({"phase": "child_done", "kind": format!("{kind:?}"), "native_verdict": native, "proof_bytes": bytes.len(), "prove_ms": prove_ms, "verify_ms": verify_ms}));
}

/// B2: a natively invalid L0' v2 child: L0' v2's research statement and key (recomputed and checked against vk.json),
/// its four traces with one Keccak-table cell plus one (L0' v2's malicious-prover fault `keccak_a_prime_bit`, recorded
/// there as `OodEvaluationMismatch` at the Keccak table), proven with the unchanged C3n prover; the native verifier
/// with the pinned key must reject it at the Keccak table's identity.
fn l0p2_child_mode(in_dir: &Path, out: &Path, cell: (usize, usize)) {
    fs::create_dir(out).expect("fresh output directory required");
    let t = Instant::now();
    let b = l0p2::build();
    let data = ProverData::from_airs_and_degrees(&keygen_config(&l0p2::keygen_seed(&b)), &b.airs, &l0p2::degrees()).expect("L0' v2 key generation");
    let next = next_row_columns_for_batch(b.airs.iter(), &data.common);
    let vk_check = l0p2::check_vk(&b, &data.common, &next, &read_json(&in_dir.join("vk.json")));
    assert_eq!(vk_check["all_equal"], json!(true), "the recomputed L0' v2 key differs from vk.json: {vk_check}");
    let child_vk = l0p2::vk_digest(&b, &pre_cap_of(&data.common), &next);
    let keygen_ms = ms(t);
    let t = Instant::now();
    let fault = l0p2::Fault::Keccak(cell.0, cell.1);
    let traces = l0p2::traces(&b, Some(fault));
    let trace_ms = ms(t);
    let prefix = schedule::prefix_elements(&l0p2::prefix(&b), &[]);
    let cfg = child_config(&prefix);
    let trefs = [&traces[0], &traces[1], &traces[2], &traces[3]];
    let instances = StarkInstance::new_multiple(&b.airs, &trefs, &b.public);
    let rss_before = peak_rss_kib();
    let t = Instant::now();
    let proof = p3_batch_stark_c3n::prove_batch(&cfg, &instances, &data).expect("L0' v2 prover");
    let prove_ms = ms(t);
    let rss_after = peak_rss_kib();
    let bytes = postcard::to_allocvec(&proof).unwrap();
    save(&out.join("proof.postcard"), &bytes);
    drop(proof);
    drop(instances);
    drop(traces);
    let decoded: ChildProof = postcard::from_bytes(&bytes).expect("decode");
    let t = Instant::now();
    let verdict = p3_batch_stark_c3n::verify_batch(&child_config(&prefix), &b.airs, &decoded, &b.public, &data.common);
    let verify_ms = ms(t);
    let native = match &verdict {
        Ok(()) => "accepted".to_string(),
        Err(e) => format!("rejected: {e:?}"),
    };
    let ok = native.contains("OodEvaluationMismatch") && native.contains("index: Some(2)");
    let run = json!({"schema": SCHEMA, "review": REVIEW, "tier": TIER,
        "child": "L0' v2's research statement, its pinned key, its four traces with one Keccak-table cell plus one (L0' v2's fault keccak_a_prime_bit: row 5, column A_PRIME + 7)",
        "kind": format!("{fault:?}"), "fault": {"table": "Keccak", "row": cell.0, "column": cell.1, "change": "plus one"},
        "vk_digest": hex(&child_vk), "key_recomputed_against_vk_json": vk_check,
        "prover": "p3_batch_stark_c3n::prove_batch (L0' v2's C3n copy, unchanged)",
        "native_verifier": "p3_batch_stark_c3n::verify_batch with the pinned key", "native_verdict": native,
        "native_expected": "OodEvaluationMismatch", "native_expected_table": 2, "as_expected": ok,
        "proof_bytes": bytes.len(), "proof_sha256": sha256_hex(&bytes), "degree_bits": l0p2::degrees(),
        "timings_ms": {"build_and_keygen": keygen_ms, "trace": trace_ms, "prove": prove_ms, "verify": verify_ms},
        "peak_rss_kib_before_prove": rss_before, "peak_rss_kib_after_prove": rss_after, "rayon_threads": std::env::var("RAYON_NUM_THREADS").ok()});
    save(&out.join("run.json"), &serde_json::to_vec_pretty(&run).unwrap());
    event(json!({"phase": "l0p2_child_done", "native_verdict": native, "as_expected": ok, "proof_bytes": bytes.len(), "prove_ms": prove_ms, "peak_rss_kib": rss_after}));
    if !ok {
        std::process::exit(3);
    }
}

/// The child proof a run uses: a child's directory (its run.json and proof: a g1b child, or the natively invalid L0' v2
/// child), or L0' v2's recorded proof.
fn child_proof(kind: Kind, in_dir: &Path, child_dir: Option<&Path>, def: &ChildDef) -> (Value, Vec<u8>) {
    match child_dir {
        Some(dir) => {
            let run = read_json(&dir.join("run.json"));
            assert_eq!(run["vk_digest"].as_str().unwrap(), hex(&def.child_vk), "the child's verifier-key digest is the pinned one");
            let bytes = fs::read(dir.join("proof.postcard")).unwrap();
            assert_eq!(run["proof_sha256"].as_str().unwrap(), sha256_hex(&bytes));
            (run, bytes)
        }
        None => {
            assert_eq!(kind, Kind::L0p2, "a g1b child needs --child-dir");
            let bytes = fs::read(in_dir.join("l0p2.postcard")).unwrap();
            (json!({"kind": "L0' v2's recorded proof", "native_verdict": "accepted", "native_expected": "accepted", "proof_sha256": sha256_hex(&bytes)}), bytes)
        }
    }
}

/// A trace-level negative: on a g1b child or at full scale on L0' v2: the honest trace (its native checks), the
/// variant's edit, the constraint and bus check on every row; the targeted group must be violated (and, where stated,
/// nothing else). B's verifier-key digest from the pinned key (its AIR and program digests recomputed and compared).
fn negative_mode(kind: Kind, variant: &str, in_dir: &Path, child_dir: Option<&Path>, vk_path: &Path, out: &Path) {
    fs::create_dir(out).expect("fresh output directory required");
    let exp = variants::expected(variant);
    let pi = g1b_pi(in_dir);
    let def = child_def(kind, in_dir, &pi);
    let spec = child_spec(&def);
    let s = Schedule::build(&spec);
    let pinned = read_json(vk_path);
    let key = pinned_key(&s, &pinned);
    let vk = b2_vk_digest(&s, &key);
    assert_eq!(pinned["b2_vk_digest"], json!(hex(&vk)), "B's verifier-key digest from the pinned key");
    let (run, bytes) = child_proof(kind, in_dir, child_dir, &def);
    let t = Instant::now();
    let (cd, replay_report) = replay_child(&def, &s, &bytes, &def.statement, run["native_expected"].as_str().unwrap());
    let (mut kt, xs, honest_report) = tracegen::honest(&s, &cd);
    let honest_trace = kt.finalize();
    let (constraints, honest_check, honest_names, honest_roles) = check_report(&s, &honest_trace, &cd.pv);
    if exp.child_level {
        assert!(variants::exact_met(&exp, &honest_names, &honest_roles), "the variant child's trace: {honest_check}");
    } else {
        assert_eq!(honest_names, exp.honest, "the honest generation from the variant's child: {honest_check}");
    }
    // The positive control also gets the LogUp check on the honest trace (B's key's packed lookups).
    let lcheck = (variant == "P").then(|| {
        let (data, _) = b2_keygen(&s);
        let lookups = data.common.lookups[0].clone();
        drop(data);
        lcheck::check(&s.air, &honest_trace, &cd.pv, &lookups, 0x6232_10c1)
    });
    let mut pv = cd.pv.clone();
    let edit = if exp.child_level || variant == "P" { json!({"edit": "none: the honest generation from the child"}) } else { variants::apply(variant, &mut kt, &s, &cd, &xs, &mut pv) };
    let trace = if variant == "P" || exp.child_level { honest_trace } else { kt.finalize() };
    let (_, this_check, names, roles) = check_report(&s, &trace, &pv);
    let targeted = variants::target_met(&exp, &names, &roles);
    let rejected = !names.is_empty();
    let as_expected = rejected == (exp.expect == "reject") && targeted && lcheck.as_ref().is_none_or(|l| l["all_zero"] == json!(true) && l["terminal_is_zero"] == json!(true));
    let doc = json!({"schema": SCHEMA, "review": REVIEW, "tier": TIER, "variant": variant, "child": def.name, "child_kind": kind.name(),
        "expected": exp.expect, "targeted_constraint_group": exp.target, "expected_exact_violations": exp.exact, "expected_alu_roles": exp.roles,
        "edit": edit, "child_run": {"kind": run["kind"], "native_verdict": run["native_verdict"], "proof_sha256": run["proof_sha256"]},
        "constraint_check": {"constraints_per_row": constraints, "rows": s.n,
            "honest_generation_violations": honest_names, "this_trace": this_check, "targeted_group_violated": targeted},
        "logup_check_of_the_honest_trace": lcheck,
        "verdict": if rejected { "REJECTED by constraints" } else { "every constraint holds" }, "as_expected": as_expected,
        "b2_vk_digest": hex(&vk), "replay": replay_report, "honest_generation": honest_report,
        "ms": ms(t), "peak_rss_kib": peak_rss_kib()});
    save(&out.join("negative.json"), &serde_json::to_vec_pretty(&doc).unwrap());
    event(json!({"phase": "negative_done", "child": kind.name(), "variant": variant, "verdict": doc["verdict"], "violated": names, "roles": roles,
        "targeted": targeted, "as_expected": as_expected}));
    if !as_expected {
        std::process::exit(3);
    }
}

/// A public-value binding term to rebind: the first term (lane, term) with another public value of a different value
/// (the first such index), so that the rebinding changes what the honest trace must hold; None when every public
/// value is equal (no rebinding is visible).
fn rebind_target(s: &Schedule, pv: &[F]) -> Option<(usize, usize, usize)> {
    for l in 0..8 {
        for (t, &(_, j)) in s.air.pub_terms[l].iter().enumerate() {
            if let Some(j2) = (0..pv.len()).find(|&k| pv[k] != pv[j]) {
                return Some((l, t, j2));
            }
        }
    }
    None
}

/// A changed verifier's schedule at the honest table height (a control must not move the height).
fn rebuilt(spec: &ChildSpec, log_n: usize) -> Schedule {
    Schedule::build_with(spec, true, log_n).unwrap_or_else(|need| panic!("the changed verifier's schedule needs {need} rows"))
}

/// Trace-level controls on B for L0' v2: the honest trace (made under the honest verifier) checked under a changed
/// verifier: the schedule (an opcode, a cap read's base address, a W2 address), the child's pinned preprocessed cap,
/// the compiled program (one LogUp constraint dropped), the next-row sets (an extra column), the child's prefix (a
/// descriptor entry), the public-value binding map. Each changed verifier's key is generated again (its own
/// preprocessed commitment) and has another B verifier-key digest, and the honest trace violates its constraints.
fn controls_mode(in_dir: &Path, vk_path: &Path, out: &Path) {
    fs::create_dir(out).expect("fresh output directory required");
    let def = l0p2_def(in_dir);
    let spec = child_spec(&def);
    let s = Schedule::build(&spec);
    let pinned = read_json(vk_path);
    let key = pinned_key(&s, &pinned);
    let vk = b2_vk_digest(&s, &key);
    assert_eq!(pinned["b2_vk_digest"], json!(hex(&vk)));
    let bytes = fs::read(in_dir.join("l0p2.postcard")).unwrap();
    let (cd, _) = replay_child(&def, &s, &bytes, &def.statement, "accepted");
    let (kt, _, _) = tracegen::honest(&s, &cd);
    let trace = kt.finalize();
    drop(kt);
    let (_, _, honest_names, _) = check_report(&s, &trace, &cd.pv);
    assert!(honest_names.is_empty(), "the honest trace satisfies the honest verifier");
    let mut rows = vec![];
    let mut record = |case: &str, what: &str, s2: &Schedule| {
        let (_, k2) = b2_keygen(s2);
        let vk2 = b2_vk_digest(s2, &k2);
        let (_, doc, names, _) = check_report(s2, &trace, &cd.pv);
        let commitment_differs = k2.commitment.roots() != key.commitment.roots();
        let row = json!({"case": case, "what": what, "b2_vk_digest": hex(&vk2), "digest_differs": vk2 != vk, "rows": s2.n,
            "preprocessed_commitment_differs": commitment_differs, "keygen_ms": k2.keygen_ms,
            "violated": names, "failing_evaluations": doc["failing_constraint_evaluations"], "unbalanced_tuples": doc["bus"]["unbalanced_tuples"],
            "as_expected": vk2 != vk && !names.is_empty()});
        event(json!({"phase": "control", "control": row}));
        rows.push(row);
    };
    // The schedule: one fold butterfly (query 5, round 1) computed as a product.
    let target = s.program.iter().position(|i| i.role == "fri.fold" && i.query == Some(5) && i.round == Some(1)).unwrap();
    let mut bad = rebuilt(&spec, s.log_n);
    let (bf, mu) = (bad.air.pidx.op[2], bad.air.pidx.op[0]);
    let row = s.instr_row[target];
    bad.air.pre[bf][row] = F::ZERO;
    bad.air.pre[mu][row] = F::ONE;
    record("schedule_opcode", "a verifier whose schedule computes one fold butterfly (query 5, round 1) as a product", &bad);
    drop(bad);
    // The schedule: a cap read's base address + 1 (query 5, quotient tree).
    let mut bad2 = rebuilt(&spec, s.log_n);
    let qt = bad2.trees.iter().position(|t| t.kind == schedule::TreeKind::Input(1)).unwrap();
    let cr = bad2.cap_read_row(5, qt);
    let ca = bad2.air.pidx.ctrl[kernel::ADDR_A];
    bad2.air.pre[ca][cr] += F::ONE;
    record("schedule_cap_base", "a verifier whose cap read (query 5, quotient tree) starts one address later", &bad2);
    drop(bad2);
    // B2: the W2 slot's schedule: claim 40's write address + 1.
    let mut bad3 = rebuilt(&spec, s.log_n);
    let crow = bad3.claim_pos[variants::VCLAIM].row;
    let cw = bad3.air.pidx.ctrl[kernel::ADDR_W];
    bad3.air.pre[cw][crow] += F::ONE;
    record("schedule_w2_address", "a verifier whose W2 slot writes claim 40 one address later", &bad3);
    drop(bad3);
    // The pinned (child's) preprocessed cap.
    let mut wrong_pre = spec.clone();
    wrong_pre.pre_cap[3][2] += F::ONE;
    record("pinned_child_preprocessed_cap", "a verifier pinning another child preprocessed cap (entry 3, element 2 plus one)", &rebuilt(&wrong_pre, s.log_n));
    // The compiled program: the fraction pin of the SHA-512 table's first lookup dropped.
    let (_, dropped, _) = compile_child(&def, Options::default(), Some((3, 0)));
    record("program_dropped_logup_constraint", "a verifier whose program is compiled without the SHA-512 table's first LogUp fraction pin", &rebuilt(&spec_with_program(&spec, dropped), s.log_n));
    // The next-row sets: the Keccak table's column 24 (export, unread at the next row) opened at zeta * g as well.
    let mut extra = spec.clone();
    let mut nm = extra.tables[2].next_main.clone();
    assert!(!nm.contains(&24));
    nm.push(24);
    nm.sort();
    extra.tables[2].next_main = nm;
    record("next_row_set_extra_column", "a verifier whose schedule opens the Keccak table's column 24 at zeta * g as well", &rebuilt(&extra, s.log_n));
    // The child's prefix: the descriptor's entry 6 (the query count) plus one (L0' v2's WrongDescriptor control).
    let mut wrong_desc = spec.clone();
    for item in wrong_desc.prefix.iter_mut() {
        if let PrefixItem::Fields(name, f) = item {
            if name == "descriptor" {
                f[1 + 6] += F::ONE;
            }
        }
    }
    record("child_prefix_descriptor", "a verifier absorbing L0' v2's descriptor with entry 6 (the query count) plus one", &rebuilt(&wrong_desc, s.log_n));
    // B2: the public-value binding map: one binding term (the first whose public value differs from the next) names the next public value.
    let mut bad4 = rebuilt(&spec, s.log_n);
    let (lane, ti, j2) = rebind_target(&bad4, &cd.pv).expect("L0' v2's statement has two different public values");
    bad4.air.pub_terms[lane][ti].1 = j2;
    record("public_binding_map", &format!("a verifier whose transcript.public binds one absorbed lane (lane {lane}, term {ti}) to public value {j2}, whose value differs"), &bad4);
    drop(bad4);
    let all = rows.iter().all(|r| r["as_expected"].as_bool().unwrap());
    let doc = json!({"schema": SCHEMA, "review": REVIEW, "tier": TIER, "child": def.name, "b2_vk_digest_honest": hex(&vk),
        "what": "the honest trace of B for L0' v2 (it satisfies every constraint of the honest verifier) checked under changed verifiers; each changed verifier's key is generated again (its own seeded preprocessed commitment) and has another B verifier-key digest; no proof is made",
        "all_as_expected": all, "controls": rows, "peak_rss_kib": peak_rss_kib()});
    save(&out.join("controls.json"), &serde_json::to_vec_pretty(&doc).unwrap());
    if !all {
        std::process::exit(3);
    }
}

fn mem_available_kib() -> Option<u64> {
    let m = fs::read_to_string("/proc/meminfo").ok()?;
    m.lines().find(|l| l.starts_with("MemAvailable:"))?.split_whitespace().nth(1)?.parse().ok()
}

fn pv_from_json(v: &Value) -> Vec<F> {
    v.as_array().unwrap().iter().map(|x| F::from_u32(x.as_u64().unwrap() as u32)).collect()
}

fn decode_strict(bytes: &[u8]) -> KProof {
    let (proof, rest) = postcard::take_from_bytes::<KProof>(bytes).expect("decode B's proof");
    assert!(rest.is_empty(), "trailing bytes");
    proof
}

/// B2: B's proof of its trace for a child (honest, or edited by a variant before the unmodified prover commits; a
/// child-level variant is the honest generation from a natively invalid child). B's key is recomputed (seeded) and
/// checked against the pinned vk.json; the proof is verified in this process; its exact byte breakdown is recorded.
fn prove_mode(kind: Kind, variant: &str, in_dir: &Path, child_dir: Option<&Path>, vk_path: &Path, out: &Path) {
    fs::create_dir(out).expect("fresh output directory required");
    tracegen::ef_selftest();
    let exp = variants::expected(variant);
    let t0 = Instant::now();
    let pi = g1b_pi(in_dir);
    let def = child_def(kind, in_dir, &pi);
    let spec = child_spec(&def);
    let s = Schedule::build(&spec);
    let schedule_ms = ms(t0);
    let (run, bytes) = child_proof(kind, in_dir, child_dir, &def);
    let t = Instant::now();
    let (cd, replay_report) = replay_child(&def, &s, &bytes, &def.statement, run["native_expected"].as_str().unwrap());
    let replay_ms = ms(t);
    let t = Instant::now();
    let (mut kt, xs, honest_report) = tracegen::honest(&s, &cd);
    let honest_trace = kt.finalize();
    let (constraints, honest_check, honest_names, honest_roles) = check_report(&s, &honest_trace, &cd.pv);
    if exp.child_level {
        assert!(variants::exact_met(&exp, &honest_names, &honest_roles), "the variant child's trace: {honest_check}");
    } else {
        assert_eq!(honest_names, exp.honest, "the honest generation from the child: {honest_check}");
    }
    let tracegen_ms = ms(t);
    let mut pv = cd.pv.clone();
    let t = Instant::now();
    let edit = if exp.child_level || variant == "P" { json!({"edit": "none: the honest generation from the child"}) } else { variants::apply(variant, &mut kt, &s, &cd, &xs, &mut pv) };
    let trace = if variant == "P" || exp.child_level {
        honest_trace
    } else {
        drop(honest_trace);
        kt.finalize()
    };
    drop(kt);
    drop(cd);
    let (_, this_check, names, roles) = check_report(&s, &trace, &pv);
    let targeted = variants::target_met(&exp, &names, &roles);
    let variant_ms = ms(t);
    let trace_sha = {
        let mut h = Sha256::new();
        for v in &trace.values {
            h.update(v.as_canonical_u32().to_le_bytes());
        }
        hex(&h.finalize())
    };
    // B's key: generated again from the seed (the prover data: the preprocessed LDE and tree) and checked against the
    // pinned vk.json field by field.
    let rss_before_keygen = peak_rss_kib();
    let (data, key) = b2_keygen(&s);
    let vk = b2_vk_digest(&s, &key);
    let vk_check = check_b2_vk(&b2_vk_json(&s, &data.common, &key, &vk), &read_json(vk_path));
    assert_eq!(vk_check["all_equal"], json!(true), "B's recomputed key differs from the pinned vk.json: {vk_check}");
    let rss_after_keygen = peak_rss_kib();
    let cfg = b2_config(&vk, &pv);
    let mem_before = mem_available_kib();
    let t = Instant::now();
    let proof = prove_kernel(&cfg, &s, &data, &trace, &pv);
    let prove_ms = ms(t);
    let rss_after = peak_rss_kib();
    let encoded = postcard::to_allocvec(&proof).unwrap();
    drop(proof);
    save(&out.join("proof.postcard"), &encoded);
    let decoded = decode_strict(&encoded);
    let (accepted, error, verify_ms) = verify_kernel(&s, &vk, &data.common, &decoded, &pv);
    let (bd, bd_errors) = breakdown::report(&encoded, &decoded, &kshape(&s, &data.common));
    save(&out.join("breakdown.json"), &serde_json::to_vec_pretty(&bd).unwrap());
    let statement = json!({"schema": SCHEMA, "variant": variant, "child_kind": kind.name(), "public_values": pv_json(&pv),
        "public_values_sha256": sha256_hex(&pv.iter().flat_map(|v| v.as_canonical_u32().to_le_bytes()).collect::<Vec<u8>>()),
        "b2_vk_digest": hex(&vk), "child_vk_digest": hex(&s.child.child_vk), "compiled_program_sha256": hex(&s.child.program_sha256),
        "b2_preprocessed_commitment_keccak256": vk_check["commitment_keccak256"]});
    save(&out.join("statement.json"), &serde_json::to_vec_pretty(&statement).unwrap());
    let terminal_zero = decoded.lookup_terminals.iter().flatten().all(|x| x.0 == EF::ZERO);
    let expect = exp.expect;
    let as_expected = accepted == (expect == "accept") && targeted && bd_errors.is_empty();
    let report = json!({"schema": SCHEMA, "review": REVIEW, "tier": TIER, "n": 1, "variant": variant, "child_kind": kind.name(),
        "expected": expect, "targeted_constraint_group": exp.target, "expected_exact_violations": exp.exact, "expected_alu_roles": exp.roles,
        "edit": edit, "child_run": {"kind": run["kind"], "native_verdict": run["native_verdict"], "proof_sha256": run["proof_sha256"]},
        "native_row_check": {"constraints_per_row": constraints, "rows": s.n,
            "honest_generation_violations": honest_names, "honest_generation_check": if honest_names.is_empty() { Value::Null } else { honest_check },
            "this_trace": this_check, "targeted_group_violated": targeted},
        "proved_trace_sha256_u32le_row_major": trace_sha,
        "lookup_terminal_is_zero": terminal_zero,
        "in_process": {"accepted": accepted, "error": error, "as_expected": accepted == (expect == "accept")},
        "as_expected": as_expected,
        "proof_bytes": encoded.len(), "proof_sha256": sha256_hex(&encoded), "b2_vk_digest": hex(&vk), "key_recomputed_against_vk_json": vk_check,
        "breakdown_summary": bd["summary"], "breakdown_all_checks_passed": bd["all_checks_passed"], "breakdown_errors": bd_errors,
        "compiled_program_sha256": hex(&s.child.program_sha256),
        "replay": replay_report, "honest_generation": honest_report,
        "timings_ms": {"schedule_and_compile": schedule_ms, "child_replay_open_inputs_and_identities": replay_ms, "trace_generation_and_check": tracegen_ms,
            "variant_and_check": variant_ms, "b_keygen": key.keygen_ms, "prove": prove_ms, "verify_in_process": verify_ms},
        "mem_available_kib_before_prove": mem_before, "peak_rss_kib_before_keygen": rss_before_keygen, "peak_rss_kib_after_keygen": rss_after_keygen,
        "peak_rss_kib_after_prove": rss_after, "rayon_threads": std::env::var("RAYON_NUM_THREADS").ok(), "b2_proof_parameters": b2_params()});
    save(&out.join("report.json"), &serde_json::to_vec_pretty(&report).unwrap());
    event(json!({"phase": "prove_done", "variant": variant, "accepted_in_process": accepted, "error": report["in_process"]["error"],
        "violated": names, "roles": roles, "lookup_terminal_is_zero": terminal_zero, "proof_bytes": encoded.len(), "prove_ms": prove_ms,
        "peak_rss_kib": rss_after, "as_expected": as_expected}));
    if !as_expected {
        std::process::exit(3);
    }
}

/// B2: a fresh process verifies a proof of B: it rebuilds the child's specification and B's schedule, generates B's
/// key again from the seed (the preprocessed commitment) and compares it with the pinned vk.json field by field,
/// computes B's verifier-key digest, decodes the proof strictly and runs p3_batch_stark_c3's verifier.
fn verify_mode(kind: Kind, in_dir: &Path, vk_path: &Path, dir: &Path, out: &Path) {
    assert!(!out.exists(), "refusing to overwrite {}", out.display());
    let t = Instant::now();
    let def = child_def(kind, in_dir, &g1b_pi(in_dir));
    let spec = child_spec(&def);
    let s = Schedule::build(&spec);
    let schedule_ms = ms(t);
    let (data, key) = b2_keygen(&s);
    let vk = b2_vk_digest(&s, &key);
    let vk_check = check_b2_vk(&b2_vk_json(&s, &data.common, &key, &vk), &read_json(vk_path));
    let KData { common, prover_only } = data;
    drop(prover_only);
    let st = read_json(&dir.join("statement.json"));
    let pv = pv_from_json(&st["public_values"]);
    let bytes = fs::read(dir.join("proof.postcard")).unwrap();
    let t = Instant::now();
    let proof = decode_strict(&bytes);
    let decode_ms = ms(t);
    let (accepted, error, verify_ms) = verify_kernel(&s, &vk, &common, &proof, &pv);
    let key_ok = vk_check["all_equal"] == json!(true);
    let statement_ok = st["b2_vk_digest"].as_str() == Some(hex(&vk).as_str()) && st["child_vk_digest"].as_str() == Some(hex(&s.child.child_vk).as_str())
        && pv.len() == s.num_public;
    let statement_is_the_childs = pv == def.statement;
    let doc = json!({"schema": SCHEMA, "review": REVIEW, "phase": "fresh_process_verify", "variant": st["variant"], "child_kind": kind.name(),
        "key_recomputed_against_vk_json": vk_check, "statement_names_this_verifier_and_child": statement_ok,
        "statement_is_the_childs_public_input": statement_is_the_childs,
        "stark_verifier_accepted": accepted, "stark_verifier_error": error,
        "verdict": if accepted && key_ok && statement_ok { "ACCEPTED" } else { "REJECTED" },
        "proof_bytes": bytes.len(), "proof_sha256": sha256_hex(&bytes), "b2_vk_digest": hex(&vk),
        "timings_ms": {"key_compile_schedule": schedule_ms, "b_keygen": key.keygen_ms, "decode": decode_ms, "verify": verify_ms},
        "peak_rss_kib": peak_rss_kib(), "rayon_threads": std::env::var("RAYON_NUM_THREADS").ok()});
    save(out, &serde_json::to_vec_pretty(&doc).unwrap());
    event(doc);
}

/// B2: verify-only controls on the accepted positive control's proof: the statement, B's verifier-key digest, the
/// pinned preprocessed commitment, a changed schedule, a changed public-value binding map and a changed compiled
/// program (each changed verifier with its own key generated again from its own seed).
fn proof_controls_mode(kind: Kind, in_dir: &Path, vk_path: &Path, dir: &Path, out: &Path) {
    assert!(!out.exists(), "refusing to overwrite {}", out.display());
    let def = child_def(kind, in_dir, &g1b_pi(in_dir));
    let spec = child_spec(&def);
    let s = Schedule::build(&spec);
    let (data, key) = b2_keygen(&s);
    let vk = b2_vk_digest(&s, &key);
    let vk_check = check_b2_vk(&b2_vk_json(&s, &data.common, &key, &vk), &read_json(vk_path));
    assert_eq!(vk_check["all_equal"], json!(true));
    let KData { common, prover_only } = data;
    drop(prover_only);
    let st = read_json(&dir.join("statement.json"));
    assert_eq!(st["variant"], "P", "controls run on the accepted positive-control proof");
    let pv = pv_from_json(&st["public_values"]);
    let bytes = fs::read(dir.join("proof.postcard")).unwrap();
    let proof = decode_strict(&bytes);
    let mut rows = vec![];
    let mut record = |case: &str, what: &str, expect_accept: bool, r: (bool, Option<String>, f64)| {
        let row = json!({"case": case, "what": what, "expected": if expect_accept {"accept"} else {"reject"},
            "accepted": r.0, "error": r.1, "verify_ms": r.2, "as_expected": r.0 == expect_accept});
        event(json!({"phase": "control", "control": row}));
        rows.push(row);
    };
    record("honest", "the positive-control proof and statement under the honest key", true, verify_kernel(&s, &vk, &common, &proof, &pv));
    let mut p2 = pv.clone();
    p2[3] = F::from_u8((pv[3].as_canonical_u32() as u8) ^ 1);
    record("statement_public_value_3_flipped", "the honest proof; the statement's public value 3 (PI_bytes byte 3) with bit 0 flipped", false, verify_kernel(&s, &vk, &common, &proof, &p2));
    let mut wrong_vk = vk;
    wrong_vk[0] ^= 1;
    record("b2_vk_digest_bit_flipped", "the honest proof against B's verifier-key digest with one bit flipped (the transcript's prefix)", false, verify_kernel(&s, &wrong_vk, &common, &proof, &pv));
    // Another pinned preprocessed commitment in the verifier's common data.
    let other_common = |cap: Cap| -> KCommon {
        let g = common.preprocessed.as_ref().unwrap();
        KCommon::new(Some(p3_batch_stark_c3::common::GlobalPreprocessed { commitment: cap, instances: g.instances.clone(), matrix_to_instance: g.matrix_to_instance.clone() }), common.lookups.clone())
    };
    let mut roots = key.commitment.roots().to_vec();
    roots[0][0] += F::ONE;
    let cm2 = other_common(Cap::new(roots.clone()));
    record("pinned_preprocessed_commitment_changed_honest_vk", "a verifier pinning another preprocessed commitment (root element 0 plus one), the honest B verifier-key digest", false, verify_kernel(&s, &vk, &cm2, &proof, &pv));
    let key2 = BKey { commitment: Cap::new(roots), ..key.clone() };
    let vk2 = b2_vk_digest(&s, &key2);
    record("pinned_preprocessed_commitment_changed_vk_recomputed", "the same changed commitment with its own B verifier-key digest", false, verify_kernel(&s, &vk2, &cm2, &proof, &pv));
    drop(cm2);
    // A changed schedule (one fold butterfly as a product), its own key and digest.
    let target = s.program.iter().position(|i| i.role == "fri.fold" && i.query == Some(5) && i.round == Some(1)).unwrap();
    let mut bad = rebuilt(&spec, s.log_n);
    let (bf, mu) = (bad.air.pidx.op[2], bad.air.pidx.op[0]);
    let row = s.instr_row[target];
    bad.air.pre[bf][row] = F::ZERO;
    bad.air.pre[mu][row] = F::ONE;
    let (bd, bk) = b2_keygen(&bad);
    let bvk = b2_vk_digest(&bad, &bk);
    record("schedule_opcode_changed_own_key", "a verifier whose schedule computes one fold butterfly (query 5, round 1) as a product: its own preprocessed commitment and B verifier-key digest", false, verify_kernel(&bad, &bvk, &bd.common, &proof, &pv));
    record("schedule_opcode_changed_honest_key", "the same changed schedule's AIR under the honest key (the verifier reads B's control only through the pinned commitment, so this is the honest verifier)", true, verify_kernel(&bad, &vk, &common, &proof, &pv));
    drop(bd);
    drop(bad);
    // A changed public-value binding map (an AIR change: transcript.public), its own key and digest.
    match rebind_target(&s, &pv) {
        Some((lane, ti, j2)) => {
            let mut bad2 = rebuilt(&spec, s.log_n);
            bad2.air.pub_terms[lane][ti].1 = j2;
            let (bd2, bk2) = b2_keygen(&bad2);
            let bvk2 = b2_vk_digest(&bad2, &bk2);
            record("public_binding_map_changed_own_key", &format!("a verifier whose transcript.public binds one absorbed lane (lane {lane}, term {ti}) to public value {j2}, whose value differs: its own key and digest"), false, verify_kernel(&bad2, &bvk2, &bd2.common, &proof, &pv));
            record("public_binding_map_changed_honest_key", "the same changed AIR under the honest key and digest", false, verify_kernel(&bad2, &vk, &common, &proof, &pv));
        }
        None => event(json!({"phase": "control_skipped", "case": "public_binding_map", "why": "every public value of the statement is equal"})),
    }
    // A program compiled without the SHA-512 table's first LogUp fraction pin (L0' v2) or without the last lookup
    // table's first fraction pin (g1b): its own schedule, key and digest.
    let drop_t = (0..spec.tables.len()).rev().find(|&t| spec.tables[t].perm_width > 0).unwrap();
    let (_, dropped, _) = compile_child(&def, Options::default(), Some((drop_t, 0)));
    let sd = rebuilt(&spec_with_program(&spec, dropped), s.log_n);
    let (bd3, bk3) = b2_keygen(&sd);
    let bvk3 = b2_vk_digest(&sd, &bk3);
    record("program_dropped_logup_constraint_own_key", "a verifier whose compiled program omits one LogUp fraction pin of the child: its own schedule, key and digest", false, verify_kernel(&sd, &bvk3, &bd3.common, &proof, &pv));
    drop(bd3);
    let all = rows.iter().all(|r| r["as_expected"].as_bool().unwrap());
    let doc = json!({"schema": SCHEMA, "review": REVIEW, "tier": TIER, "proof_sha256": sha256_hex(&bytes), "b2_vk_digest": hex(&vk),
        "all_as_expected": all, "controls": rows, "peak_rss_kib": peak_rss_kib()});
    save(out, &serde_json::to_vec_pretty(&doc).unwrap());
    if !all {
        std::process::exit(3);
    }
}

fn arg(args: &[String], name: &str) -> Option<String> {
    args.iter().position(|a| a == name).map(|i| args[i + 1].clone())
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mode = args.get(1).map(String::as_str).unwrap_or("");
    let path = |n: &str| PathBuf::from(arg(&args, n).unwrap_or_else(|| panic!("{n} required")));
    let kind = || Kind::parse(&arg(&args, "--child").expect("--child"));
    let child_dir = arg(&args, "--child-dir").map(PathBuf::from);
    match mode {
        "l0p2-native" => l0p2_native_mode(&path("--in"), &path("--out")),
        "compile" => compile_mode(kind(), &path("--in"), &path("--out"), arg(&args, "--points").map(|p| p.parse().unwrap()).unwrap_or(16)),
        "schedule" => schedule_mode(kind(), &path("--in"), &path("--out")),
        "trace" => trace_mode(kind(), &path("--in"), &path("--proof"), &path("--vk"), &path("--out"), arg(&args, "--save").map(PathBuf::from).as_deref()),
        "g1b-child" => {
            let kind = if let Some(c) = arg(&args, "--cell") {
                let v: Vec<usize> = c.split(',').map(|x| x.parse().unwrap()).collect();
                G1bKind::Cell(v[0], v[1], v[2])
            } else if let Some(k) = arg(&args, "--unbalanced") {
                G1bKind::Unbalanced(k.parse().unwrap())
            } else {
                G1bKind::Honest
            };
            g1b_child_mode(&path("--pi"), &path("--out"), kind);
        }
        "l0p2-child" => {
            let v: Vec<usize> = arg(&args, "--keccak-cell").expect("--keccak-cell ROW,COL").split(',').map(|x| x.parse().unwrap()).collect();
            l0p2_child_mode(&path("--in"), &path("--out"), (v[0], v[1]));
        }
        "negative" => negative_mode(
            arg(&args, "--child").map(|c| Kind::parse(&c)).unwrap_or(Kind::G1b),
            &arg(&args, "--variant").expect("--variant"),
            &path("--in"),
            child_dir.as_deref(),
            &path("--vk"),
            &path("--out"),
        ),
        "controls" => controls_mode(&path("--in"), &path("--vk"), &path("--out")),
        "prove" => prove_mode(kind(), &arg(&args, "--variant").expect("--variant"), &path("--in"), child_dir.as_deref(), &path("--vk"), &path("--out")),
        "verify" => verify_mode(kind(), &path("--in"), &path("--vk"), &path("--dir"), &path("--out")),
        "proof-controls" => proof_controls_mode(kind(), &path("--in"), &path("--vk"), &path("--dir"), &path("--out")),
        "children" => {
            for (d, a) in variants::CHILDREN {
                println!("{d} {a}");
            }
        }
        "variants" => println!("{}", if arg(&args, "--child").as_deref() == Some("l0p2") { variants::ALL_L0P2.join(" ") } else { variants::ALL.join(" ") }),
        "prove-variants" => println!("{}", variants::PROVE_L0P2.join(" ")),
        "variant-child" => println!("{}", variants::child_dir(&arg(&args, "--variant").expect("--variant"))),
        "keccak-a-prime-cell" => println!("5,{}", keccak::A_PRIME + 7),
        // ---- F1: F verifying B (fmodes.rs) ----
        "f-compile" => fmodes::f_compile_mode(&path("--in"), &path("--b-vk"), &path("--out"), arg(&args, "--points").map(|p| p.parse().unwrap()).unwrap_or(16)),
        "f-schedule" => fmodes::f_schedule_mode(&path("--in"), &path("--b-vk"), &path("--out")),
        "f-trace" => fmodes::f_trace_mode(&path("--in"), &path("--b-vk"), &path("--b-dir"), &path("--out"), arg(&args, "--save").map(PathBuf::from).as_deref(),
            arg(&args, "--f1-trace").map(PathBuf::from).as_deref()),
        // ---- F2: changes (a) and (d), F's proof ----
        "f-degree" => fprove::f_degree_mode(&path("--in"), &path("--b-vk"), &path("--out")),
        "f-salts" => fprove::f_salts_mode(&path("--out"), arg(&args, "--log-height").map(|p| p.parse().unwrap()).unwrap_or(22)),
        "f-prove" => fprove::f_prove_mode(&arg(&args, "--variant").expect("--variant"), &path("--in"), &path("--b-vk"), &path("--b-dir"), child_dir.as_deref(),
            &path("--f-vk"), &path("--out")),
        "f-verify" => fprove::f_verify_mode(&path("--in"), &path("--b-vk"), &path("--f-vk"), &path("--dir"), &path("--out")),
        "f-proof-controls" => fprove::f_proof_controls_mode(&path("--in"), &path("--b-vk"), &path("--f-vk"), &path("--dir"), &path("--out")),
        "f-negative" => fmodes::f_negative_mode(&arg(&args, "--variant").expect("--variant"), &path("--in"), &path("--b-vk"), &path("--b-dir"), child_dir.as_deref(), &path("--out")),
        "f-controls" => fmodes::f_controls_mode(&path("--in"), &path("--b-vk"), &path("--b-dir"), &path("--out")),
        "f-variants" => println!("{}", fvariants::ALL.join(" ")),
        "f-child-variants" => println!("{}", fvariants::CHILD_LEVEL.join(" ")),
        // ---- pipeline (code/pq-proof-pipeline-20261101) ----
        "b-prove-statement" | "f-export-key" => pipeline::cli(&args),
        _ => panic!("unknown mode {mode:?}"),
    }
}
