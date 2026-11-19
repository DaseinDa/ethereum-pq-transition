//! L0' v2's configuration, key and statement in the B1 and B2 binaries (L5 layer B1, 2026-10-31; B2, 2026-11-01: the
//! research statement's four traces, with an optional one-cell fault, for the natively invalid child): a reproduction, from the
//! recorded sources, of what L0' v2's verifier pins (code/l5-leaf-l0p2-20261031/l0p2/main.rs, read only; line
//! numbers of that file): the domain separator, the AIR digest over L0' v2's AIR sources (l. 108-112), the descriptor
//! (l. 116-120), the program digest computed as S5 computes it (l. 126-138), the deterministic key generation with its
//! salt seed (l. 222-225, 348-352), the four prefix absorptions (l. 164-180), and the research statement's AIRs and
//! public values (`build`, l. 290-346: the default witness, every assertion kept). The AIR sources themselves are
//! L0' v2's files, byte-identical (src/b1/l0p2/, SHA-256 checked by apply_patch.py); the B1 binary recomputes the key
//! and compares every field of L0' v2's vk.json that pins the verifier (`check_vk`).
//! Research prototype; loop-internal self-review; not independently reviewed.
use std::sync::Arc;

use num_bigint::BigUint;
use p3_batch_stark_c3n::{CommonData, NextRowColumns};
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_keccak_air::NUM_KECCAK_COLS;
use p3_koala_bear::KoalaBear as F;
use p3_matrix::dense::RowMajorMatrix;
use serde_json::{Value, json};
use tiny_keccak::{Hasher, Keccak};

use crate::air::{Ag1Air, BytePairAir, FieldOpAir, KeccakTableAir, ShaAir};
use crate::program::{Ckd, HEIGHT, LIMBS, PAIR_HEIGHT, PUBLIC_BLOCKS, col};
use crate::{CAP_HEIGHT, Config, DIGEST_ELEMS, LOG_BLOWUP, LOG_FINAL_POLY_LEN, MAX_LOG_ARITY, QUERIES, RANDOM_CODEWORDS, hex, keccak256};
use crate::{instance, keccak, program, sha};

pub const DOMAIN: &[u8] = b"PQ-MIGRATE-RESEARCH-L5-LEAF-L0P-v2";
pub const AIR_LABEL: &[u8] = b"PQ-MIGRATE-L5-LEAF-L0P-AIR-v2";
pub const SALT_SEED_LABEL: &[u8] = b"PQ-MIGRATE-L5-LEAF-L0P-PREPROCESSED-SALT-SEED-v2";
/// The batch layout's tag in the descriptor: C3n.
const LAYOUT_C3N: usize = 4;
/// L0' v2's AIR digest covers these four sources, in this order (L0' v2 main.rs l. 87).
const AIR_SOURCES: [&[u8]; 4] = [include_bytes!("l0p2/air.rs"), include_bytes!("l0p2/program.rs"), include_bytes!("l0p2/keccak.rs"), include_bytes!("l0p2/sha.rs")];
/// S5's program digest (L0' v2 main.rs l. 89-90).
const S5_PROGRAM_DIGEST: &str = "b5c607936d9fbed32ed393b767e67dbd76d2a0ffe8454317bd17b16916aa9b0a";
pub const TABLES: [&str; 4] = ["FieldOp", "BytePair", "Keccak", "Sha"];
/// The B1 label of L0' v2's verifier-key digest (B1's own; L0' v2 has none of this form).
const VK_LABEL: &[u8] = b"PQ-MIGRATE-RESEARCH-L5-B1-CHILD-L0P2-VK-v1";

pub fn air_digest() -> [u8; 32] {
    let mut parts: Vec<&[u8]> = vec![AIR_LABEL];
    parts.extend(AIR_SOURCES);
    keccak256(&parts)
}

/// S5's 22 entries with L0''s values, L0''s additions and v2's (L0' v2 main.rs l. 116-120).
pub fn descriptor(canonical_bits: bool) -> Vec<usize> {
    vec![1, 8, 8, LOG_FINAL_POLY_LEN, RANDOM_CODEWORDS, LOG_BLOWUP, QUERIES, MAX_LOG_ARITY, 0, 0, 0, 0, HEIGHT, col::WIDTH, PAIR_HEIGHT,
         PUBLIC_BLOCKS * LIMBS, keccak::HEIGHT, NUM_KECCAK_COLS, keccak::PI_BYTES, sha::HEIGHT, sha::WIDTH, canonical_bits as usize,
         16, 8, DIGEST_ELEMS, CAP_HEIGHT, LAYOUT_C3N, program::per::NUM, program::pair_col::WIDTH - 1, sha::NUM_PERIODIC]
}

/// The extended degree bits of each table (L0' v2 main.rs l. 122-124).
pub fn degrees() -> Vec<usize> {
    [HEIGHT, PAIR_HEIGHT, keccak::HEIGHT, sha::HEIGHT].iter().map(|h| h.trailing_zeros() as usize + 1).collect()
}

/// Keccak-256 of the program, as S5 computes it (L0' v2 main.rs l. 126-138).
fn program_digest(airs: &[Ag1Air]) -> [u8; 32] {
    let mut h = Keccak::v256();
    for a in airs {
        let cols = match a {
            Ag1Air::FieldOp(x) => &x.program,
            Ag1Air::BytePair(x) => &x.program,
            Ag1Air::Sha(x) => &x.program,
            Ag1Air::Keccak(_) => continue,
        };
        for c in cols.iter() {
            for v in c {
                h.update(&v.to_le_bytes());
            }
        }
    }
    let mut out = [0; 32];
    h.finalize(&mut out);
    out
}

/// The key generation's salt seed (L0' v2 main.rs l. 225).
pub fn salt_seed(program: &[u8; 32]) -> [u8; 32] {
    keccak256(&[SALT_SEED_LABEL, &air_digest(), program])
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

/// The research statement's AIRs and public values.
pub struct Built {
    pub airs: Vec<Ag1Air>,
    /// The tables' public values: the Keccak table's 198 (PI_bytes), none elsewhere.
    pub public: Vec<Vec<F>>,
    pub pi: [u8; keccak::PI_BYTES],
    pub digest: [u8; 32],
    pub canonical_bits: bool,
    pub address: [u8; 20],
    /// B2: what L0' v2's `traces` needs (main.rs l. 243-256): the program, the Keccak message, the SHA-512
    /// compressions and the SHA-512 table's program.
    pub prog: program::Program,
    pub message: [u8; 64],
    pub comps: Vec<sha::Compression>,
    pub sha_program: Arc<Vec<Vec<u64>>>,
}

/// One changed cell of an honest trace (L0' v2 main.rs l. 261, its malicious-prover faults).
#[derive(Clone, Copy, Debug)]
pub enum Fault {
    FieldOp(usize, usize),
    Keccak(usize, usize),
    Sha(usize, usize),
}

/// The four traces of the research statement with an optional fault (L0' v2 main.rs l. 398-411, `traces`).
pub fn traces(b: &Built, fault: Option<Fault>) -> [RowMajorMatrix<F>; 4] {
    let field_fault = match fault { Some(Fault::FieldOp(r, c)) => Some((r, c)), _ => None };
    let keccak_fault = match fault { Some(Fault::Keccak(r, c)) => Some((r, c)), _ => None };
    let sha_fault = match fault { Some(Fault::Sha(r, c)) => Some((r, c)), _ => None };
    let (t, mult) = program::traces(&b.prog, field_fault);
    let main = RowMajorMatrix::new(t.into_iter().map(F::from_u64).collect(), col::WIDTH);
    let pair = RowMajorMatrix::new(mult.into_iter().map(F::from_u64).collect(), program::pair_col::WIDTH);
    let kec = keccak::trace::<F>(&b.message, keccak_fault);
    let sha = sha::trace::<F>(&b.comps, &b.sha_program, sha_fault);
    [main, pair, kec, sha]
}

/// L0' v2's `build()` (main.rs l. 290-298) with its default witness (`build_with`, l. 300-346, `Witness::default()`,
/// not lenient): the SHA-512 derivation, the program, the message and address, the four AIRs, PI_bytes with nonce 0.
/// Every assertion of the original is kept.
pub fn build() -> Built {
    let seed = instance::seed();
    let path = instance::PATH;
    let (comps, il) = sha::derive(&seed, &path);
    assert!(sha::fits_shape(&path), "the research path fits the shape");
    assert_eq!(il, instance::derive_with(&seed, &path).il.to_vec(), "SHA-table I_L values differ from the hmac crate");
    let il: [BigUint; 6] = il.try_into().unwrap();
    let mut prog = program::build(&Ckd { il, force_key: None }, None, false);
    prog.index_first = std::array::from_fn(|s| if s == 0 { 0 } else { (path[s - 1] >> 24) as u64 });
    let message = message_of(&prog.pubkey);
    let address = keccak::address(&message);
    let sha_program = Arc::new(sha::periodic());
    let canonical_bits = true;
    let airs = vec![
        Ag1Air::FieldOp(FieldOpAir { program: Arc::new(program::periodic(&prog)), p_limbs: program::p_limbs(), n_limbs: program::n_limbs(), canonical_bits }),
        Ag1Air::BytePair(BytePairAir { program: Arc::new(program::pair_periodic()) }),
        Ag1Air::Keccak(KeccakTableAir),
        Ag1Air::Sha(ShaAir { program: sha_program.clone() }),
    ];
    let pi = keccak::pi_bytes(&address, 0);
    let public = vec![vec![], vec![], pi.iter().map(|&v| F::from_u8(v)).collect(), vec![]];
    let digest = program_digest(&airs);
    // build()'s assertions (main.rs l. 291-297).
    let d = instance::derive();
    let ckd = Ckd { il: d.il.clone(), force_key: None };
    assert_eq!(program::derive_keys(&ckd), d.keys.to_vec(), "key arithmetic differs from the reference derivation");
    assert_eq!(hex(&address), instance::EXPECTED_ADDRESS_HEX, "address differs from the research fixture");
    assert_eq!(hex(&digest), S5_PROGRAM_DIGEST, "the program differs from S5's");
    Built { airs, public, pi, digest, canonical_bits, address, prog, message, comps, sha_program }
}

/// The four prefix absorptions (L0' v2 main.rs l. 164-180, `Binding::Expected`).
pub fn prefix(b: &Built) -> Vec<crate::schedule::PrefixItem> {
    use crate::schedule::PrefixItem;
    let d = descriptor(b.canonical_bits);
    let mut fields = vec![F::from_usize(d.len())];
    fields.extend(d.iter().map(|&v| F::from_usize(v)));
    vec![
        PrefixItem::Bytes("domain_separator".into(), DOMAIN.to_vec()),
        PrefixItem::Bytes("air_digest".into(), air_digest().to_vec()),
        PrefixItem::Fields("descriptor".into(), fields),
        PrefixItem::Bytes("program_digest".into(), b.digest.to_vec()),
    ]
}

/// L0' v2's verifier-key digest for B (B1's identity of the child; not absorbed by the child's transcript): label,
/// domain, AIR digest, descriptor, program digest, degree bits, every preprocessed cap entry, the derived next-row
/// sets.
pub fn vk_digest(b: &Built, pre_cap: &[[F; 8]], next: &[NextRowColumns]) -> [u8; 32] {
    let mut h = Keccak::v256();
    h.update(VK_LABEL);
    for part in [DOMAIN, &air_digest()[..], &b.digest[..]] {
        h.update(&(part.len() as u64).to_le_bytes());
        h.update(part);
    }
    for v in descriptor(b.canonical_bits).into_iter().chain(degrees()) {
        h.update(&(v as u64).to_le_bytes());
    }
    for d in pre_cap {
        for v in d {
            h.update(&v.as_canonical_u32().to_le_bytes());
        }
    }
    for n in next {
        for set in [&n.main, &n.preprocessed, &n.permutation] {
            h.update(&(set.len() as u64).to_le_bytes());
            for &c in set.iter() {
                h.update(&(c as u64).to_le_bytes());
            }
        }
    }
    let mut out = [0u8; 32];
    h.finalize(&mut out);
    out
}

/// The recomputed key against L0' v2's vk.json: the preprocessed commitment (postcard bytes, Keccak-256, every cap
/// entry, the matrix map, the instances, the salt seed), the AIR digest, the program digest, the descriptor, the degree
/// bits and the derived next-row sets (L0' v2 main.rs l. 488-498 compares the same fields but the degree bits).
pub fn check_vk(b: &Built, common: &CommonData<Config>, next: &[NextRowColumns], pinned: &Value) -> Value {
    let g = common.preprocessed.as_ref().expect("C4a: a preprocessed commitment");
    let enc = postcard::to_allocvec(&g.commitment).unwrap();
    let cap: Vec<Vec<u32>> = g.commitment.roots().iter().map(|d| d.iter().map(|x| x.as_canonical_u32()).collect()).collect();
    let instances: Vec<Value> = g.instances.iter().zip(TABLES).map(|(m, t)| match m {
        Some(m) => json!({"table": t, "matrix_index": m.matrix_index, "width": m.width, "degree_bits": m.degree_bits}),
        None => Value::Null,
    }).collect();
    let next_rec: Value = json!(next.iter().zip(TABLES).map(|(r, t)| json!({"table": t,
        "main_width": r.main_width, "main_next_row_columns": r.main,
        "preprocessed_width": r.preprocessed_width, "preprocessed_next_row_columns": r.preprocessed,
        "permutation_ef8_width": r.permutation_width, "permutation_next_row_ef8_columns": r.permutation})).collect::<Vec<_>>());
    let pp = &pinned["preprocessed"];
    let checks = vec![
        ("preprocessed.commitment_postcard_hex", pp["commitment_postcard_hex"] == json!(hex(&enc))),
        ("preprocessed.commitment_keccak256", pp["commitment_keccak256"] == json!(hex(&keccak256(&[&enc])))),
        ("preprocessed.cap", pp["cap"] == json!(cap)),
        ("preprocessed.cap_height", pp["cap_height"] == json!(g.commitment.height())),
        ("preprocessed.matrix_to_instance", pp["matrix_to_instance"] == json!(g.matrix_to_instance)),
        ("preprocessed.instances", pp["instances"] == json!(instances)),
        ("preprocessed.salt_seed", pp["salt_seed"] == json!(hex(&salt_seed(&b.digest)))),
        ("air_digest", pinned["air_digest"] == json!(hex(&air_digest()))),
        ("program_digest", pinned["program_digest"] == json!(hex(&b.digest))),
        ("descriptor", pinned["descriptor"] == json!(descriptor(b.canonical_bits))),
        ("degree_bits", pinned["degree_bits"] == json!(degrees())),
        ("domain", pinned["domain"] == json!(String::from_utf8_lossy(DOMAIN))),
        ("public_values", pinned["public_values"] == json!(keccak::PI_BYTES)),
        ("next_row_columns", pinned["next_row_columns"] == next_rec),
    ];
    let all = checks.iter().all(|(_, ok)| *ok);
    json!({"all_equal": all, "fields": checks.iter().map(|(n, ok)| json!({"field": n, "equal": ok})).collect::<Vec<_>>(),
        "commitment_keccak256": hex(&keccak256(&[&enc]))})
}

/// The tables' widths, heights and public-value counts of the statement (for the record).
pub fn shape_record(b: &Built) -> Value {
    json!({"tables": TABLES, "degree_bits": degrees(), "address": hex(&b.address), "pi_bytes": hex(&b.pi),
        "program_digest": hex(&b.digest), "air_digest": hex(&air_digest()), "descriptor": descriptor(b.canonical_bits),
        "domain": String::from_utf8_lossy(DOMAIN), "public_values_per_table": b.public.iter().map(Vec::len).collect::<Vec<_>>()})
}

pub fn keygen_seed(b: &Built) -> [u8; 32] {
    salt_seed(&b.digest)
}
