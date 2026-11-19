//! `TrustedParams` (the pinned constants) and F's verifier key, built once from the embedded material and checked
//! against them.
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::OnceLock;
use std::time::Instant;

use p3_batch_stark_c3np::NextRowColumns;
use p3_challenger::{CanObserve, DuplexChallenger};
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_fri::{FriParameters, HidingFriPcs};
use p3_koala_bear::{KoalaBear as F, Poseidon2KoalaBear, default_koalabear_poseidon2_16};
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use rand::SeedableRng;
use rand::rngs::StdRng;
use serde_json::Value;
use sha2::{Digest as _, Sha256};

use crate::error::VerifyError;
use crate::fkernel::KernelAir;
use crate::material::{self, DigestSources};

// F's configuration types, exactly as F2's binary defines them (code/l5-layer-f2-20261031/f2/main.rs).
pub type EF = BinomialExtensionField<F, 8>;
pub type Perm = Poseidon2KoalaBear<16>;
pub type Hash = PaddingFreeSponge<Perm, 16, 8, 8>;
pub type Compress = TruncatedPermutation<Perm, 2, 8, 16>;
pub type FMmcs = p3_merkle_tree_ps::MerkleTreeHidingMmcs<<F as Field>::Packing, <F as Field>::Packing, Hash, Compress, StdRng, 2, 8, 8>;
pub type FChMmcs = ExtensionMmcs<F, EF, FMmcs>;
pub type FHPcs = HidingFriPcs<F, Radix2DitParallel<F>, FMmcs, FChMmcs, StdRng>;
pub type Challenger = DuplexChallenger<F, Perm, 16, 8>;
pub type FConfig = p3_uni_stark::StarkConfig<FHPcs, EF, Challenger>;
pub type FProof = p3_batch_stark_c3np::BatchProof<FConfig>;
pub type FCommon = p3_batch_stark_c3np::CommonData<FConfig>;

/// F's FRI and PCS parameters (code/l5-layer-f2-20261031/f2/fmodes.rs, `f_pcs` and the `F_*` constants).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FriPcsParams {
    /// F's trace has 2^log_n rows (2^14); its proof's degree bits are log_n + 1 (the zero-knowledge extension).
    pub log_n: usize,
    pub log_blowup: usize,
    pub log_final_poly_len: usize,
    pub max_log_arity: usize,
    pub num_queries: usize,
    pub batch_pow_bits: usize,
    pub commit_pow_bits: usize,
    pub query_pow_bits: usize,
    /// Merkle cap height of both MMCS (0: one root).
    pub cap_height: usize,
    /// `HidingFriPcs` random codewords per committed matrix.
    pub random_codewords: usize,
    /// Salt elements per Merkle leaf.
    pub salt_elems: usize,
    /// KoalaBear elements per digest.
    pub digest_elems: usize,
    /// The challenge field's degree over KoalaBear.
    pub extension_degree: usize,
}

/// Everything the verifier trusts, fixed in this crate. The fields are private and `TRUSTED_PARAMS` is the only
/// value: the submitter of a proof chooses nothing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrustedParams {
    f_vk_digest: [u8; 32],
    b_vk_digest: [u8; 32],
    l0p2_vk_digest: [u8; 32],
    f_domain: &'static str,
    fri: FriPcsParams,
    max_proof_bytes: usize,
    public_values: usize,
    periodic_columns: usize,
    periodic_sha256: [u8; 32],
    key_material_sha256: [u8; 32],
    periodic_rle_sha256: [u8; 32],
}

const fn nibble(c: u8) -> u8 {
    match c {
        b'0'..=b'9' => c - b'0',
        b'a'..=b'f' => c - b'a' + 10,
        _ => panic!("lower-case hex expected"),
    }
}
const fn h32(s: &str) -> [u8; 32] {
    let b = s.as_bytes();
    assert!(b.len() == 64, "32 bytes of hex expected");
    let mut out = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        out[i] = (nibble(b[2 * i]) << 4) | nibble(b[2 * i + 1]);
        i += 1;
    }
    out
}

/// The pinned parameters: F's verifier-key digest and the identity digests it covers (B's, which covers L0' v2's), F's
/// FRI and PCS parameters, `MAX_PROOF_BYTES`, and the SHA-256 of the embedded key material.
pub const TRUSTED_PARAMS: TrustedParams = TrustedParams {
    f_vk_digest: h32("ed2fcf813b942404729da7827c4743020dae8d89ebbc206e5bee7718503df3f2"),
    b_vk_digest: h32("415bf19b5b55f7acd0b793c2ea45aef7923e3e640fdce2e81fc9fb350fdcf490"),
    l0p2_vk_digest: h32("6537a5af9b10f1599a151c024c549cad3740b95f9bc026b658b927a81ca20372"),
    f_domain: "PQ-MIGRATE-RESEARCH-L5-F2-v1",
    fri: FriPcsParams {
        log_n: 14,
        log_blowup: 9,
        log_final_poly_len: 8,
        max_log_arity: 4,
        num_queries: 29,
        batch_pow_bits: 0,
        commit_pow_bits: 0,
        query_pow_bits: 0,
        cap_height: 0,
        random_codewords: 8,
        salt_elems: 8,
        digest_elems: 8,
        extension_degree: 8,
    },
    max_proof_bytes: 196_608,
    public_values: 198,
    periodic_columns: 162,
    periodic_sha256: h32("c4ea648516734e6f42ef26886c82e46d9baa52e4ca0161566cc0ce6e31f4c228"),
    key_material_sha256: h32("079b3554a854a729cb7d8c6e48682dada7e4ef0fde46fea8de82ca45d9109156"),
    periodic_rle_sha256: h32("971c157a28b9f796e853bab275b71b431b90be6c4911b2fce220c6aed39b8d08"),
};

impl TrustedParams {
    /// F's verifier-key digest (absorbed by F's transcript before the first commitment).
    pub const fn f_vk_digest(&self) -> &[u8; 32] {
        &self.f_vk_digest
    }
    /// B's verifier-key digest, covered by F's.
    pub const fn b_vk_digest(&self) -> &[u8; 32] {
        &self.b_vk_digest
    }
    /// L0' v2's identity digest as B pins it, covered by B's.
    pub const fn l0p2_vk_digest(&self) -> &[u8; 32] {
        &self.l0p2_vk_digest
    }
    /// F's transcript domain separator.
    pub const fn f_domain(&self) -> &'static str {
        self.f_domain
    }
    pub const fn fri(&self) -> &FriPcsParams {
        &self.fri
    }
    /// The largest proof accepted for decoding: `MAX_PROOF_BYTES` = 196,608 (spec l. 72).
    pub const fn max_proof_bytes(&self) -> usize {
        self.max_proof_bytes
    }
    /// The statement's length in field elements (one per PI byte).
    pub const fn public_values(&self) -> usize {
        self.public_values
    }
    /// SHA-256 of F's 162 periodic columns, u32 little-endian, column-major (F2's `periodic_columns_sha256`).
    pub const fn periodic_sha256(&self) -> &[u8; 32] {
        &self.periodic_sha256
    }
    /// SHA-256 of the embedded `key/f-key-material.json`.
    pub const fn key_material_sha256(&self) -> &[u8; 32] {
        &self.key_material_sha256
    }
    /// SHA-256 of the embedded `key/f-periodic.rle`.
    pub const fn periodic_rle_sha256(&self) -> &[u8; 32] {
        &self.periodic_rle_sha256
    }
}

const MATERIAL_JSON: &[u8] = include_bytes!("../key/f-key-material.json");
const PERIODIC_RLE: &[u8] = include_bytes!("../key/f-periodic.rle");

/// The sources that the digests cover. `fkernel.rs` is the module this crate compiles and evaluates (F's AIR); the
/// others are digest input only (byte-identical copies of code/l5-layer-f2-20261031/f2/).
pub fn sources() -> DigestSources<'static> {
    DigestSources {
        fkernel: include_bytes!("fkernel.rs"),
        fschedule: include_bytes!("../key/sources/fschedule.rs"),
        compiler: include_bytes!("../key/sources/compiler.rs"),
        fchild: include_bytes!("../key/sources/fchild.rs"),
        fmodes: include_bytes!("../key/sources/fmodes.rs"),
        kernel: include_bytes!("../key/sources/kernel.rs"),
        schedule: include_bytes!("../key/sources/schedule.rs"),
    }
}

/// F's verifier key: F's AIR (with its 162 periodic columns), F's key data (the packed lookups), and the next-row sets
/// (derived from the AIR, and opened by the break-even rule).
pub struct VerifierKey {
    pub air: KernelAir,
    pub common: FCommon,
    /// The derived sets (checked and digest-bound; the verifier opens `opened`).
    #[allow(dead_code)]
    pub derived: NextRowColumns,
    pub opened: NextRowColumns,
    pub build_ms: f64,
}

/// A PCS with F's parameters. Verification draws no randomness; the generators get a fixed seed so that the verifier
/// never reads operating-system entropy (the record's verifier passed operating-system generators that it never drew).
fn pcs(p: &FriPcsParams) -> FHPcs {
    let perm = default_koalabear_poseidon2_16();
    let rng = || StdRng::from_seed([0u8; 32]);
    let fri = FriParameters {
        log_blowup: p.log_blowup,
        log_final_poly_len: p.log_final_poly_len,
        max_log_arity: p.max_log_arity,
        num_queries: p.num_queries,
        batch_proof_of_work_bits: p.batch_pow_bits,
        commit_proof_of_work_bits: p.commit_pow_bits,
        query_proof_of_work_bits: p.query_pow_bits,
        mmcs: FChMmcs::new(FMmcs::new(Hash::new(perm.clone()), Compress::new(perm.clone()), p.cap_height, rng())),
    };
    FHPcs::new(Radix2DitParallel::default(), FMmcs::new(Hash::new(perm.clone()), Compress::new(perm), p.cap_height, rng()), fri, p.random_codewords, rng())
}

/// F's challenger before the first commitment (fmodes.rs `f_challenger`): F's domain, F's verifier-key digest and the
/// public values, each sequence preceded by its length.
fn challenger(domain: &str, vk: &[u8; 32], pv: &[F]) -> Challenger {
    let mut c = Challenger::new(default_koalabear_poseidon2_16());
    for bytes in [domain.as_bytes(), &vk[..]] {
        c.observe(F::from_usize(bytes.len()));
        for &b in bytes {
            c.observe(F::from_u8(b));
        }
    }
    c.observe(F::from_usize(pv.len()));
    for &v in pv {
        c.observe(v);
    }
    c
}

/// F's verifying configuration for one statement (a fresh transcript per verification).
pub fn config(params: &TrustedParams, pv: &[F]) -> FConfig {
    p3_uni_stark::StarkConfig::new(pcs(&params.fri), challenger(params.f_domain, &params.f_vk_digest, pv))
}

fn fault(msg: impl Into<String>) -> VerifyError {
    VerifyError::VerifierKey(msg.into())
}

fn build(params: &TrustedParams) -> Result<VerifierKey, VerifyError> {
    let t = Instant::now();
    let sha = |b: &[u8]| -> [u8; 32] { Sha256::digest(b).into() };
    if sha(MATERIAL_JSON) != params.key_material_sha256 {
        return Err(fault("the embedded f-key-material.json is not the pinned one"));
    }
    if sha(PERIODIC_RLE) != params.periodic_rle_sha256 {
        return Err(fault("the embedded f-periodic.rle is not the pinned one"));
    }
    let m: Value = serde_json::from_slice(MATERIAL_JSON).map_err(|e| fault(format!("key material: {e}")))?;
    let mf = |e: material::MaterialError| fault(format!("key material: {e}"));
    let f = material::get(&m, "f").map_err(mf)?;
    let p = &params.fri;
    let [log_blowup, log_final, arity, queries, cw, salt, digest, cap] = material::f_params(f).map_err(mf)?;
    if [log_blowup, log_final, arity, queries, cw, salt, digest, cap]
        != [p.log_blowup, p.log_final_poly_len, p.max_log_arity, p.num_queries, p.random_codewords, p.salt_elems, p.digest_elems, p.cap_height]
    {
        return Err(fault("the material's FRI and PCS parameters are not the pinned ones"));
    }
    if material::text(f, "domain").map_err(mf)? != params.f_domain {
        return Err(fault("the material's domain is not the pinned one"));
    }
    let fa = material::get(f, "air").map_err(mf)?;
    let per = material::get(fa, "periodic").map_err(mf)?;
    let (ncols, nrows) = (material::num(per, "columns").map_err(mf)?, material::num(per, "rows").map_err(mf)?);
    if ncols != params.periodic_columns || nrows != 1 << p.log_n {
        return Err(fault("the material's periodic shape is not the pinned one"));
    }
    let cols = material::decode_periodic(PERIODIC_RLE, ncols, nrows).map_err(mf)?;
    if material::periodic_sha256(&cols) != params.periodic_sha256 {
        return Err(fault("the periodic columns' SHA-256 is not the pinned one"));
    }
    let air = material::air_from_material(fa, cols).map_err(mf)?;
    if air.log_n != p.log_n || air.num_public != params.public_values {
        return Err(fault("F's AIR shape is not the pinned one"));
    }
    // F's key data: p3_batch_stark_c3np's own key generation (F has no preprocessed trace: the packed lookups only).
    let keygen_cfg = p3_uni_stark::StarkConfig::new(pcs(p), challenger(params.f_domain, &[0u8; 32], &[]));
    let data = p3_batch_stark_c3np::ProverData::from_airs_and_degrees(&keygen_cfg, std::slice::from_ref(&air), &[p.log_n + 1])
        .map_err(|e| fault(format!("F's key generation: {e:?}")))?;
    let common = data.common;
    let lookups: Vec<(String, usize, usize, u64)> = common.lookups[0]
        .iter()
        .map(|l| (format!("{:?}", l.kind), l.column, l.elements.len(), u64::from(l.count_weight)))
        .collect();
    let pinned_lookups: Vec<(String, usize, usize, u64)> = material::get(f, "lookups")
        .map_err(mf)?
        .as_array()
        .ok_or_else(|| fault("lookups is not an array"))?
        .iter()
        .map(|l| -> Result<_, VerifyError> {
            Ok((material::text(l, "kind").map_err(mf)?.to_string(), material::num(l, "column").map_err(mf)?,
                material::num(l, "tuples").map_err(mf)?, material::num(l, "count_weight").map_err(mf)? as u64))
        })
        .collect::<Result<_, _>>()?;
    if lookups != pinned_lookups {
        return Err(fault("F's packed lookups differ from the material's"));
    }
    // The next-row sets: derived from the AIR (C3nP's symbolic analysis) and opened by the break-even rule; both must
    // be the material's (and both enter F's digest).
    let derived = p3_batch_stark_c3np::next_row_columns_for_batch(std::iter::once(&air), &common).remove(0);
    let opened = material::opened_from_derived(&derived, p.num_queries, p.random_codewords, p.salt_elems);
    let m_derived = material::next_rows_from_json(material::get(f, "next_row_derived").map_err(mf)?).map_err(mf)?;
    let m_opened = material::next_rows_from_json(material::get(f, "next_row_opened").map_err(mf)?).map_err(mf)?;
    if derived != m_derived || opened != m_opened {
        return Err(fault("F's next-row sets differ from the material's"));
    }
    if !derived.main.iter().all(|c| opened.main.contains(c)) || !derived.permutation.iter().all(|c| opened.permutation.contains(c)) {
        return Err(fault("an opened next-row set does not contain the derived one"));
    }
    // The digest chain: L0' v2's identity digest, B's (covering it), F's (covering B's), each recomputed.
    let (f_vk, b_vk, l_vk) = material::digest_chain(&m, &air, &derived, &opened, &sources()).map_err(mf)?;
    if (f_vk, b_vk, l_vk) != (params.f_vk_digest, params.b_vk_digest, params.l0p2_vk_digest) {
        return Err(fault("the recomputed digests are not the pinned ones"));
    }
    Ok(VerifierKey { air, common, derived, opened, build_ms: t.elapsed().as_secs_f64() * 1e3 })
}

static KEY: OnceLock<Result<VerifierKey, VerifyError>> = OnceLock::new();

/// F's verifier key, built once per process (about 0.1 s) and shared; `params` must be `TRUSTED_PARAMS`.
pub fn verifier_key(params: &TrustedParams) -> Result<&'static VerifierKey, VerifyError> {
    if *params != TRUSTED_PARAMS {
        return Err(fault("the parameters are not the pinned TRUSTED_PARAMS"));
    }
    KEY.get_or_init(|| {
        catch_unwind(AssertUnwindSafe(|| build(&TRUSTED_PARAMS))).unwrap_or_else(|p| {
            let msg = p.downcast_ref::<String>().cloned().or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string()));
            Err(VerifyError::Internal(format!("building the verifier key: {}", msg.unwrap_or_default())))
        })
    })
    .as_ref()
    .map_err(Clone::clone)
}
