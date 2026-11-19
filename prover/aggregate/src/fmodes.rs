//! F2's modes (L5 layer F2, 2026-11-01): F1's trace-level modes on F2's layout, and F's identity for F's proof.
//! What F2 changes against F1 (each with its control in the record):
//! - (c) **periodic bus control**: F's AIR (`fkernel.rs`) reads the 14 bus-control values that were pure main copies
//!   from their periodic columns (main width 271 -> 257); F's prover is p3_batch_stark_c3np (C3n with p3-lookup's
//!   permutation-trace generation given the periodic columns, `periodic_logup.rs`), and F's key, next-row sets and
//!   symbolic analysis are C3nP's;
//! - (b) **the break-even split rule**: of the next-row sets C3nP derives, a trace is split (its next-row subset
//!   committed apart) only where the split saves bytes by L0' v2's calibrated byte rule (`split_delta_bytes`); otherwise
//!   the trace is opened in full at zeta * g (a superset of the derived set). For F: the main trace split, the
//!   permutation trace not. The opened sets enter F's verifier-key digest and the batch transcript;
//! - (d) **salts from a seed**: F's PCS uses p3_merkle_tree_ps (the pinned p3-merkle-tree with each committed matrix's
//!   salts regenerated from a per-matrix 256-bit seed by ChaCha20 instead of stored; the proof is unchanged);
//! - (a) quotient degree 3 is not applied (`f-degree` records why: with zero knowledge the pinned prover commits
//!   2^(ceil(log2 d) + 1) chunks, 8 at degree 3 and at degree 4).
//! F's domain and verifier-key label are F2's own. F1's description follows; "F1" there is the step that built it.
//!
//! F1's modes (L5, 2026-11-01): the final layer F verifying B, at trace level. F's AIR is B1's periodic-control kernel
//! (`fkernel.rs`, byte-identical to code/l5-layer-b1-20261031/b1/kernel.rs: 271 main columns, 8 bus slots, periodic
//! control with the bus control copied into 16 main columns because p3-lookup reads no periodic column); F's schedule,
//! trace generator, LogUp check and negatives are B1's (`fschedule.rs`, `ftracegen.rs`, `flcheck.rs`, `fvariants.rs`, module
//! paths renamed), applied to B as the child (`fchild.rs`). F's own proof parameters are the budget's (2^14 rows, blowup
//! 2^9, 29 queries, FRI arities [16, 8], final polynomial 2^8, cap height 0, hiding with 8 random codewords and 8-element
//! salts, no grinding); they enter F's verifier-key digest and F's key generation (the packed lookups); F is not proven
//! by these modes.
//! - `f-compile`: B's AIR compiled with the kernel's compiler, and the differential test against C3's native functions;
//! - `f-schedule`: F's schedule for B: rows, columns, constraints, bus, DEEP, ALU, F's verifier-key digest, F's key
//!   (lookups), the next-row sets C3n would derive for F's AIR, the interface map and the program listing;
//! - `f-trace`: B's proof replayed natively, F's honest trace, every native cross-check, every constraint of F on every
//!   row, the bus counted exactly, p3-lookup's permutation trace with every constraint and the terminal;
//! - `f-negative`: one trace-level negative (the targeted group must be violated);
//! - `f-controls`: the honest trace under changed verifiers (each with its own F verifier-key digest).
//! Research measurement; loop-internal self-review; not independently reviewed.
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;
use std::time::Instant;

use p3_air::BaseAir;
use p3_air::symbolic::AirLayout;
use p3_challenger::CanObserve;
use p3_dft::Radix2DitParallel;
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_fri::FriParameters;
use p3_koala_bear::{KoalaBear as F, default_koalabear_poseidon2_16};
use p3_lookup::{LogUpGadget, LookupProtocol};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use rand::rngs::StdRng;
use serde_json::{Value, json};
use sha2::{Digest as _, Sha256};
use tiny_keccak::{Hasher, Keccak};

use crate::fchild::{self, BChild};
use crate::fschedule::{self, PrefixItem, Schedule};
use crate::{
    Challenger, Compress, DIGEST_ELEMS, EF, FChMmcs, FCommon, FConfig, FHPcs, FMmcs, Hash, RANDOM_CODEWORDS, REVIEW, SALT_ELEMS, TIER, event,
    flcheck, fkernel, ftracegen, fvariants, gzip, hex, ms, os_rng, peak_rss_kib, save, sha256_hex,
};
use p3_batch_stark_c3np::NextRowColumns;

// F's own proof parameters (the budget's, results/l5-budget-k1-20261031 and results/l5-c3b-20261031): 2^14 rows,
// blowup 2^9, 29 queries, FRI arities [16, 8], final polynomial 2^8, Merkle cap height 0; hiding with 8 random
// codewords and 8-element salts; no grinding.
pub const F_LOG_BLOWUP: usize = 9;
pub const F_LOG_FINAL_POLY_LEN: usize = 8;
pub const F_MAX_LOG_ARITY: usize = 4;
pub const F_QUERIES: usize = 29;
pub const F_CAP_HEIGHT: usize = 0;
pub const F_LOG_N_DESIGN: usize = 14;
pub const F_DOMAIN: &[u8] = b"PQ-MIGRATE-RESEARCH-L5-C-v1";
const F_VK_LABEL: &[u8] = b"PQ-MIGRATE-RESEARCH-L5-F2-VK-v1";
const FKERNEL_SOURCE: &[u8] = include_bytes!("fkernel.rs");
const FSCHEDULE_SOURCE: &[u8] = include_bytes!("fschedule.rs");
const COMPILER_SOURCE: &[u8] = include_bytes!("compiler.rs");
const FCHILD_SOURCE: &[u8] = include_bytes!("fchild.rs");
/// The source of F's next-row layout rule (`split_delta_bytes`, `f_next_rows`): this file's rule section, hashed into
/// F's verifier-key digest with the opened sets themselves.
const FMODES_SOURCE: &[u8] = include_bytes!("fmodes.rs");

/// F's PCS with given random number generators (the input MMCS's salt seeds, the FRI MMCS's salt seeds, the PCS's own
/// random codewords and masks). F2: both MMCS are p3_merkle_tree_ps's (salts regenerated from a per-matrix seed).
pub fn f_pcs(rngs: [StdRng; 3]) -> FHPcs {
    let [input_rng, fri_rng, pcs_rng] = rngs;
    let perm = default_koalabear_poseidon2_16();
    let fri = FriParameters {
        log_blowup: F_LOG_BLOWUP,
        log_final_poly_len: F_LOG_FINAL_POLY_LEN,
        max_log_arity: F_MAX_LOG_ARITY,
        num_queries: F_QUERIES,
        batch_proof_of_work_bits: 0,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 0,
        mmcs: FChMmcs::new(FMmcs::new(Hash::new(perm.clone()), Compress::new(perm.clone()), F_CAP_HEIGHT, fri_rng)),
    };
    FHPcs::new(Radix2DitParallel::default(), FMmcs::new(Hash::new(perm.clone()), Compress::new(perm), F_CAP_HEIGHT, input_rng), fri, RANDOM_CODEWORDS, pcs_rng)
}

/// F's challenger before the first commitment: F's domain, F's verifier-key digest and every public value (the 198
/// statement values), each sequence preceded by its length (B1's `b1_config`, F's parameters).
pub fn f_challenger(vk: &[u8; 32], pv: &[F]) -> Challenger {
    let mut c = Challenger::new(default_koalabear_poseidon2_16());
    for bytes in [F_DOMAIN, &vk[..]] {
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

/// F's proof configuration with fresh operating-system randomness (every proof attempt builds its own: §22.2).
pub fn f_config(vk: &[u8; 32], pv: &[F]) -> FConfig {
    p3_uni_stark::StarkConfig::new(f_pcs([os_rng(), os_rng(), os_rng()]), f_challenger(vk, pv))
}

pub fn f_params() -> Value {
    json!({"prover": "p3_batch_stark_c3np (L0' v2's C3n copy of p3-batch-stark with p3-lookup's permutation-trace generation given the AIR's periodic columns): one instance with periodic control columns, one named LogUp bus (global kind; its terminal must be zero); next-row sets C3nP derives, widened by the break-even split rule",
        "verifier": "p3_batch_stark_c3np::verify_batch_with_next_row_columns with F's opened next-row sets (a superset of the derived sets, checked) and zero for omitted entries (C3n's verify_batch is the same call with the derived sets)",
        "rows_design": 1usize << F_LOG_N_DESIGN, "log_blowup": F_LOG_BLOWUP, "log_final_poly_len": F_LOG_FINAL_POLY_LEN, "max_log_arity": F_MAX_LOG_ARITY,
        "num_queries": F_QUERIES, "pow_bits": 0, "random_codewords": RANDOM_CODEWORDS, "salt_elements": SALT_ELEMS,
        "digest_elements": DIGEST_ELEMS, "cap_height": F_CAP_HEIGHT, "extension_degree": 8,
        "mmcs": "p3_merkle_tree_ps::MerkleTreeHidingMmcs (the pinned hiding MMCS; each committed matrix's salts regenerated from a 256-bit seed drawn from the MMCS's generator, ChaCha20 with stream = row, instead of stored; openings and verification unchanged)",
        "hash": "Poseidon2KoalaBear<16>: PaddingFreeSponge<_,16,8,8> leaves, TruncatedPermutation<_,2,8,16> nodes, DuplexChallenger<_,_,16,8>"})
}

// ---------- (b) the break-even split rule ----------

/// The length of a postcard varint.
fn vlen(n: usize) -> i64 {
    let mut len = 1;
    let mut v = n >> 7;
    while v > 0 {
        len += 1;
        v >>= 7;
    }
    len
}

/// The worst-case byte change of opening a hiding trace's next-row subset by a split (C3n: two committed matrices of
/// the same height, the subset at zeta and zeta * g, the rest at zeta only) instead of opening the whole trace at both
/// points; negative when the split saves bytes. L0' v2's calibrated rule (code/l5-leaf-l0p2-20261031/f_effect.py
/// `trace_bytes`, `round_framing`; it reproduced four measured deltas of L0' v2 to the byte, and F1's budget re-checked
/// it against L0' v2's record): per query one more opened row's framing and one more salt; one more matrix-point of
/// random-codeword values; the out-of-domain values at zeta * g of `next` columns instead of `width` (extension
/// elements of 32 B; the main trace's `Option` tag is the same either way); the round's matrix count stays a one-byte
/// varint. `width` and `next` count base columns (a permutation trace's EF8 columns times 8).
pub fn split_delta_bytes(width: usize, next: usize) -> i64 {
    assert!(0 < next && next < width, "only a proper, non-empty next-row subset can be split");
    let (q, cw, salt, efb, fb) = (F_QUERIES as i64, RANDOM_CODEWORDS, SALT_ELEMS as i64, 32i64, 4i64);
    let ood = (vlen(next) + efb * next as i64) - (vlen(width) + efb * width as i64);
    let codewords = vlen(1) + vlen(cw) + efb * cw as i64;
    let rows = q * (vlen(next + cw) + vlen(width - next + cw) - vlen(width + cw) + fb * cw as i64);
    let salts = q * (vlen(SALT_ELEMS) + fb * salt);
    let framing = vlen(2) - vlen(1);
    ood + codewords + rows + salts + q * 2 * framing + framing
}

/// F's next-row sets: (the sets C3nP derives from F's AIR and key, the sets F opens). The break-even rule: a main or
/// permutation trace whose derived set is a proper subset is split only if `split_delta_bytes` is negative; otherwise
/// it is opened in full at zeta * g. The opened sets contain the derived ones (asserted), so every column a constraint
/// reads at the next row is opened there; they are F's verifier's, never the proof's.
pub fn f_next_rows(s: &Schedule, common: &FCommon) -> (NextRowColumns, NextRowColumns, Value) {
    let derived = p3_batch_stark_c3np::next_row_columns_for_batch(std::iter::once(&s.air), common).remove(0);
    let mut opened = derived.clone();
    let main_delta = derived.main_split().is_split().then(|| split_delta_bytes(derived.main_width, derived.main.len()));
    let pw = 8 * derived.permutation_width;
    let perm_delta = derived.permutation_split(8).is_split().then(|| split_delta_bytes(pw, 8 * derived.permutation.len()));
    if main_delta.is_some_and(|d| d >= 0) {
        opened.main = (0..derived.main_width).collect();
    }
    if perm_delta.is_some_and(|d| d >= 0) {
        opened.permutation = (0..derived.permutation_width).collect();
    }
    assert!(opened.is_well_formed(), "the opened sets are well formed");
    for (sub, sup) in [(&derived.main, &opened.main), (&derived.preprocessed, &opened.preprocessed), (&derived.permutation, &opened.permutation)] {
        assert!(sub.iter().all(|c| sup.contains(c)), "the opened next-row set contains the derived one");
    }
    let rule = json!({"rule": "split a trace's next-row subset only where it saves bytes (L0' v2's calibrated rule, split_delta_bytes); otherwise open the trace in full at zeta*g",
        "main": {"width": derived.main_width, "derived_next": derived.main.len(), "split_delta_bytes": main_delta, "split": opened.main_split().is_split(), "opened_next": opened.main.len()},
        "permutation_ef8": {"width": derived.permutation_width, "derived_next": derived.permutation.len(), "split_delta_bytes": perm_delta,
            "split": opened.permutation_split(8).is_split(), "opened_next": opened.permutation.len()},
        "preprocessed": {"width": derived.preprocessed_width, "derived_next": derived.preprocessed.len()}});
    (derived, opened, rule)
}

/// The next-row sets' bytes for F's verifier-key digest: each width and each column list, in a fixed order.
fn next_rows_digest_words(n: &NextRowColumns) -> Vec<u64> {
    let mut d = vec![n.main_width as u64, n.main.len() as u64];
    d.extend(n.main.iter().map(|&c| c as u64));
    d.extend([n.preprocessed_width as u64, n.preprocessed.len() as u64]);
    d.extend(n.preprocessed.iter().map(|&c| c as u64));
    d.extend([n.permutation_width as u64, n.permutation.len() as u64]);
    d.extend(n.permutation.iter().map(|&c| c as u64));
    d
}

/// F's verifier-key digest (B1's `b1_vk_digest`, F's parameters and sources): F's shape and parameters, the child's (B's)
/// shape, FRI tail and identity, every periodic column (`periodic_statement`: the transcript's constants, i.e. B's
/// prefix, the seeds, the degree bits and B's pinned preprocessed cap; opcodes, immediates, addresses, multiplicities,
/// lanes), F1: the first transcript row's absorbed count and the public-value binding map, the bus name, B's
/// verifier-key digest, B's prefix, the compiled program's SHA-256, and F's kernel, schedule, compiler and child sources.
/// F2 adds: the main trace's bus-control width, F's next-row sets as opened (after the break-even rule) and as derived,
/// and this file's source (the rule, F's domain and challenger).
pub fn f_vk_digest(s: &Schedule, next: &(NextRowColumns, NextRowColumns)) -> [u8; 32] {
    let mut h = Keccak::v256();
    h.update(F_VK_LABEL);
    let c = &s.child;
    let mut d: Vec<u64> = vec![fkernel::NCTRL_MAIN as u64];
    d.extend(next_rows_digest_words(&next.1));
    d.extend(next_rows_digest_words(&next.0));
    d.extend([s.n as u64, fkernel::WIDTH as u64, s.q as u64, s.num_public as u64, s.air.periodic.len() as u64,
        s.t_rows as u64, s.block_rows as u64, s.program.len() as u64, F_LOG_BLOWUP as u64, F_LOG_FINAL_POLY_LEN as u64,
        F_MAX_LOG_ARITY as u64, F_QUERIES as u64, RANDOM_CODEWORDS as u64, SALT_ELEMS as u64, DIGEST_ELEMS as u64, F_CAP_HEIGHT as u64,
        c.index_bits as u64, c.num_queries as u64, c.log_final_poly_len as u64, c.log_blowup as u64, crate::K_CAP_HEIGHT as u64]);
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
    h.update(&BaseAir::<F>::periodic_statement(&s.air));
    // F1: the AIR's two schedule-derived structures that are not periodic columns (B1's digest left them out; B2 added
    // them to B's program digest): the first transcript row's absorbed count (`transcript.iv`) and the public-value
    // binding map (`transcript.public`: per lane, each (periodic selector, public value)).
    h.update(&(s.air.k0 as u64).to_le_bytes());
    for lane in &s.air.pub_terms {
        h.update(&(lane.len() as u64).to_le_bytes());
        for &(sel, j) in lane {
            h.update(&(sel as u64).to_le_bytes());
            h.update(&(j as u64).to_le_bytes());
        }
    }
    h.update(fkernel::BUS.as_bytes());
    h.update(&c.child_vk);
    for v in fschedule::prefix_elements(&c.prefix, &vec![F::ZERO; c.num_public]) {
        h.update(&v.as_canonical_u32().to_le_bytes());
    }
    h.update(&c.program_sha256);
    h.update(FKERNEL_SOURCE);
    h.update(FSCHEDULE_SOURCE);
    h.update(COMPILER_SOURCE);
    h.update(FCHILD_SOURCE);
    h.update(FMODES_SOURCE);
    let mut out = [0u8; 32];
    h.finalize(&mut out);
    out
}

/// F's key data from p3_batch_stark_c3np's own key generation (F has no preprocessed trace: the packed lookups only;
/// the configuration's challenger and randomness take no part in it).
pub fn f_data(s: &Schedule) -> crate::FData {
    let cfg = p3_uni_stark::StarkConfig::new(f_pcs([os_rng(), os_rng(), os_rng()]), f_challenger(&[0u8; 32], &[]));
    p3_batch_stark_c3np::ProverData::from_airs_and_degrees(&cfg, std::slice::from_ref(&s.air), &[s.log_n + 1]).expect("F's key generation")
}
pub fn f_common(s: &Schedule) -> FCommon {
    f_data(s).common
}

/// F's next-row sets and F's verifier-key digest from F's schedule (the key's lookups decide the sets).
pub fn f_identity(s: &Schedule) -> (FCommon, (NextRowColumns, NextRowColumns), Value, [u8; 32]) {
    let common = f_common(s);
    let (derived, opened, rule) = f_next_rows(s, &common);
    let next = (derived, opened);
    let vk = f_vk_digest(s, &next);
    (common, next, rule, vk)
}

/// The next-row sets of F's AIR as C3nP derives them and as F opens them (the break-even rule), with column names.
pub fn f_next_row(next: &(NextRowColumns, NextRowColumns), rule: &Value) -> Value {
    let names = |cols: &[usize]| -> Vec<String> { cols.iter().map(|&c| fkernel_column_name(c)).collect() };
    let (n, o) = next;
    json!({"derived_by": "p3_batch_stark_c3np::next_row_columns_for_batch (next_row.rs: every Main/Preprocessed/Permutation variable at offset 1 of the symbolic constraints, the LogUp gadget's included)",
        "main_width": n.main_width, "main_next_row_columns": n.main, "main_next_row_column_names": names(&n.main),
        "preprocessed_width": n.preprocessed_width, "preprocessed_next_row_columns": n.preprocessed,
        "permutation_ef8_width": n.permutation_width, "permutation_next_row_ef8_columns": n.permutation,
        "opened_after_break_even_rule": {"main_next_row_columns": o.main.len(), "main_split": o.main_split().is_split(),
            "permutation_next_row_ef8_columns": o.permutation, "permutation_split": o.permutation_split(8).is_split()},
        "break_even_rule": rule})
}

/// The name of F's main column c (for the record).
pub fn fkernel_column_name(c: usize) -> String {
    use fkernel::*;
    match c {
        x if x < 16 => format!("poseidon2.input{x}"),
        x if x < OUT => format!("poseidon2.internal{x}"),
        x if x < P2W => format!("poseidon2.output{}", x - OUT),
        x if x == BIT => "BIT".into(),
        x if x == ACC => "ACC".into(),
        x if x >= HB && x < TP => format!("HB{}", x - HB),
        x if x >= TP && x < XQ => format!("TP{}", x - TP),
        x if x == XQ => "XQ".into(),
        x if x == X => "X".into(),
        x if x == V => "V".into(),
        x if x >= A && x < B => format!("A{}", x - A),
        x if x >= B && x < C => format!("B{}", x - B),
        x if x >= C && x < R => format!("C{}", x - C),
        x if x >= R && x < CTRL => format!("R{}", x - R),
        x if x >= CTRL && x < DL => format!("CTRL.{}", CTRL_MAIN_NAMES[x - CTRL]),
        x if x >= DL && x < PW => format!("DL{}", x - DL),
        x if x >= PW && x < WIDTH => format!("PW{}.{}", (x - PW) / 8 + 1, (x - PW) % 8),
        x => format!("column{x}"),
    }
}

/// F's rows: K1's (transcript and query blocks) or the last row holding an instruction or a reserved slot.
pub fn f_used_rows(s: &Schedule) -> usize {
    let last_instr = s.instr_row.iter().copied().max().unwrap_or(0);
    s.used_rows.max(last_instr + 1)
}

/// The reserved rows (no instruction): the write port's rows by kind, the LOAD rows, the injection and cap-read rows.
fn f_reserved_rows(s: &Schedule) -> Value {
    let count = |f: &dyn Fn(&fschedule::Val) -> bool| s.rport.iter().filter(|(_, v)| f(v)).count();
    let inj: usize = s.trees.iter().map(|t| t.nodes.iter().filter(|(_, n)| matches!(n, fschedule::Node::Inj(_))).count()).sum::<usize>() * s.q;
    let claims = count(&|v| matches!(v, fschedule::Val::Claim(_)));
    let caps = count(&|v| matches!(v, fschedule::Val::Cap(..)));
    let terms = count(&|v| matches!(v, fschedule::Val::Terminal(_)));
    let sd = count(&|v| matches!(v, fschedule::Val::SD(..)));
    let hi = count(&|v| matches!(v, fschedule::Val::Hi(_)));
    json!({"claims": claims, "cap_entries": caps, "lookup_terminals": terms, "deep_chain_sums": sd, "query_high_parts": hi,
        "cap_reads": s.cap_reads.len(), "injections": inj, "loads": s.q,
        "total_without_loads": claims + caps + terms + sd + hi + s.cap_reads.len() + inj})
}

/// F's exact shape: rows, columns (main, periodic), constraints by group with degrees, bus traffic, the program's parts,
/// the packed lookups, the next-row sets C3nP derives and those F opens.
pub fn f_shape_doc(s: &Schedule, bc: &BChild, cm: &FCommon, next: &(NextRowColumns, NextRowColumns), rule: &Value, vk: &[u8; 32]) -> Value {
    let lookups: &[p3_lookup::Lookup<F>] = &cm.lookups[0];
    let layout = AirLayout::from_air(&s.air);
    let gadget = LogUpGadget::new();
    let (base, ext) = p3_batch_stark_c3np::symbolic::get_symbolic_constraints::<F, EF, _, _>(&s.air, layout, lookups, &gadget);
    let log_chunks = p3_batch_stark_c3np::symbolic::get_log_num_quotient_chunks::<F, EF, _, _>(&s.air, layout, s.n, lookups, 1, &gadget);
    let degree = p3_batch_stark_c3np::symbolic::get_max_constraint_degree::<F, EF, _, _>(&s.air, layout, s.n, lookups, &gadget);
    let (base0, _) = p3_batch_stark_c3np::symbolic::get_symbolic_constraints::<F, EF, _, _>(&s.air, layout, &[], &gadget);
    let base_degree = base0.iter().map(|c| c.degree_multiple()).max().unwrap_or(0);
    let tags = fkernel::constraint_tags(&s.air, s.num_public);
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
    let weight: u64 = cm.lookups[0].total_count_weight();
    let bound = p3_lookup::check_multiplicity_height_bound(&cm.lookups, &[s.n]);
    let counts = s.program_counts();
    let reserved = f_reserved_rows(s);
    let public_selectors = s.air.periodic_names.iter().filter(|n| n.starts_with("public_row")).count();
    let used = f_used_rows(s);
    json!({"child": {"name": s.child.name, "b": bc.record,
            "tables": s.child.tables.iter().map(|t| json!({"name": t.name, "log_trace": t.log_trace, "width": t.width,
                "preprocessed_width": t.pre_width, "public_values": t.public.len(), "next_main": t.next_main.len(), "next_preprocessed": t.next_pre.len(),
                "next_permutation_ef8": t.next_perm, "permutation_width_ef8": t.perm_width, "lookup_buses": t.lookup_bus,
                "log_quotient_degree": t.log_qd, "chunks": t.chunks})).collect::<Vec<_>>(),
            "index_bits": s.child.index_bits, "fri_log_arities": s.child.fri_log_arities, "log_final_poly_len": s.child.log_final_poly_len,
            "queries": s.child.num_queries, "child_vk_digest": hex(&s.child.child_vk), "cap_height": crate::K_CAP_HEIGHT, "buses": s.child.num_buses,
            "max_message_width": s.child.max_message_width,
            "seed_elements": {"batch": s.child.seeds[0].len(), "pcs": s.child.seeds[1].len(), "fri": s.child.seeds[2].len()},
            "prefix": s.child.prefix.iter().map(|p| p.name().to_string()).collect::<Vec<_>>()},
        "compiled_program": {"sha256": hex(&s.child.program_sha256), "instructions": s.child.program.instrs.len(), "stats": s.child.program.stats},
        "rows": {"n": s.n, "log_n": s.log_n, "used": used, "margin_to_n": s.n - used, "share_of_n": used as f64 / s.n as f64,
            "k1_rows": s.used_rows, "transcript": s.t_rows, "per_query": s.block_rows, "query_blocks": s.q * s.block_rows,
            "per_query_per_tree": s.trees.iter().map(|t| json!({"tree": t.name, "rows": t.block_len, "groups": t.groups.iter().map(|g| g.lh_rows).collect::<Vec<_>>(),
                "compressions": t.mc, "injections": t.nodes.iter().filter(|(_, n)| matches!(n, fschedule::Node::Inj(_))).count(), "cap_rows": t.cap_rows,
                "index_bits_on_leaf_rows": t.consume_lh, "index_bits_below": t.skip, "start": format!("{:?}", t.start)})).collect::<Vec<_>>(),
            "alu_instructions": s.program.len(), "reserved_rows": reserved, "last_instruction_row": s.instr_row.iter().max(),
            "alu_and_reserved_rows": s.program.len() + reserved["total_without_loads"].as_u64().unwrap() as usize,
            "rows_used_rule": "max(K1's rows, the last ALU instruction's row + 1); the ALU's instructions fill every row that holds no reserved slot (the write port's claims, cap entries, terminals, DEEP chain sums and query high parts; the cap reads; the LOADs)",
            "transcript_rows_by_absorbed_count": k_hist},
        "columns": {"main_width": fkernel::WIDTH, "poseidon2": fkernel::P2W, "bit_acc": 2, "hi_bits": fkernel::HI_BITS, "hi_products": fkernel::TP_N,
            "xq": 1, "base_lane_x": 1, "base_value_v": 1, "alu": 32, "bus_control_main": fkernel::NCTRL_MAIN,
            "bus_control_main_names": fkernel::CTRL_MAIN_NAMES, "bus_control_read_from_periodic_columns": fkernel::NCTRL - fkernel::NCTRL_MAIN,
            "deep_accumulator": 8, "batching_challenge_powers": 32, "preprocessed": 0,
            "periodic": s.air.periodic.len(), "periodic_control": s.air.periodic.len() - public_selectors, "periodic_public_row_selectors": public_selectors,
            "public_values": s.num_public, "permutation_columns_ef8": aux, "permutation_columns_base": 8 * aux},
        "bus": {"name": fkernel::BUS, "interaction_slots_per_row": fkernel::SLOTS.len(), "slots": fkernel::SLOTS,
            "lookups_after_packing": lookups.iter().map(|l| json!({"kind": format!("{:?}", l.kind), "column": l.column,
                "tuples": l.elements.len(), "tuple_width": l.elements.first().map(Vec::len), "count_weight": l.count_weight, "fraction_pin_degree": gadget.constraint_degree(l)})).collect::<Vec<_>>(),
            "addresses_written": s.writer.len(), "reads_scheduled": reads, "cap_reads_dynamic": s.cap_reads.len(),
            "largest_scheduled_multiplicity": s.reads.values().max(),
            "multiplicity_height_bound": {"total_count_weight": weight, "base_trace_height": s.n, "weighted_sum": weight * s.n as u64,
                "check_multiplicity_height_bound": format!("{bound:?}")}},
        "deep": {"claims": s.n_claims(), "claim_runs": s.claim_runs.len(), "chains": s.chains.len(), "joined_matrices": s.chains.iter().map(|c| c.matrices.len() - 1).sum::<usize>(),
            "height_point_pairs": s.hz.len(), "chain_value_rows_per_query": s.chains.iter().map(|c| c.value_rows.len()).sum::<usize>(),
            "pass_rows_per_query": s.chains.iter().map(|c| c.pass_rows.len()).sum::<usize>(),
            "opened_values_per_query": s.chains.iter().map(|c| c.value_rows.iter().map(|(_, l)| l.len()).sum::<usize>()).sum::<usize>(),
            "rollins": s.rollins.iter().map(|(r, h)| json!({"after_round": r, "log_height": h})).collect::<Vec<_>>(),
            "r_port_writes": s.rport.len()},
        "alu": counts,
        "constraints": {"base": base.len(), "extension": ext.len(), "max_degree_with_lookups": degree, "max_degree_base_only": base_degree,
            "quotient_chunks_with_zk": 1usize << (log_chunks + 1),
            "by_group": by_group.iter().map(|(g, (n, d))| json!({"group": g, "constraints": n, "max_degree": d})).collect::<Vec<_>>(),
            "public_binding_terms": s.air.pub_terms.iter().map(|t| t.len()).sum::<usize>()},
        "next_row_sets_c3n": f_next_row(next, rule),
        "f_vk_digest": hex(vk), "f_proof_parameters": f_params()})
}

/// The constraint check's report on F (B1's `check_report` on F's AIR): every failing group with counts, first rows and
/// ALU roles, B's identity's and the terminal check's EQ rows, the bus.
pub fn fcheck_report(s: &Schedule, trace: &RowMajorMatrix<F>, pv: &[F]) -> (usize, Value, Vec<String>, BTreeMap<String, BTreeSet<String>>) {
    let (constraints, fails, unbalanced, live) = fkernel::check(&s.air, trace, pv);
    let row_instr: std::collections::HashMap<usize, usize> =
        s.instr_row.iter().enumerate().filter(|(i, _)| s.program[*i].op != fkernel::Op::Load).map(|(i, &r)| (r, i)).collect();
    let mut groups: BTreeMap<String, (usize, Vec<usize>, BTreeSet<String>)> = Default::default();
    let mut roles: BTreeMap<String, BTreeSet<String>> = Default::default();
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
    let base = s.k3b_range.0 + s.k3b_unpacks();
    let eq_rows: BTreeSet<usize> = fails.iter().filter(|f| f.group == "alu.eq").map(|f| f.row).collect();
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

/// SHA-256 of F's periodic columns (u32 little-endian, column-major).
pub fn periodic_sha256(s: &Schedule) -> String {
    let mut h = Sha256::new();
    for col in &s.air.periodic {
        for v in col {
            h.update(v.as_canonical_u32().to_le_bytes());
        }
    }
    hex(&h.finalize())
}

/// F's verifier key as a record (`f-vk.json`): F's verifier-key digest and everything a fresh verifier recomputes and
/// compares (`check_f_vk`): the shape, the periodic columns' hash, the next-row sets as opened and as derived, the
/// packed lookups, the child's identity, the proof parameters.
pub fn f_vk_json(s: &Schedule, cm: &FCommon, next: &(NextRowColumns, NextRowColumns), vk: &[u8; 32]) -> Value {
    json!({"schema": "l5-layer-f2/vk/v1", "review": REVIEW,
        "what": "F's verifier identity: F's verifier-key digest (F's shape and parameters, every periodic column, the next-row sets as opened and derived, B's identity and prefix, the compiled program's SHA-256, F's sources); F has no preprocessed trace",
        "f_vk_digest": hex(vk), "domain": String::from_utf8_lossy(F_DOMAIN), "rows": s.n, "log_n": s.log_n, "main_width": fkernel::WIDTH,
        "bus_control_main": fkernel::NCTRL_MAIN, "periodic_columns": s.air.periodic.len(), "periodic_columns_sha256": periodic_sha256(s),
        "public_values": s.num_public,
        "next_row_opened": {"main": next.1.main, "permutation_ef8": next.1.permutation, "preprocessed": next.1.preprocessed},
        "next_row_derived": {"main": next.0.main, "permutation_ef8": next.0.permutation, "preprocessed": next.0.preprocessed},
        "lookups": cm.lookups[0].iter().map(|l| json!({"kind": format!("{:?}", l.kind), "column": l.column, "tuples": l.elements.len(), "count_weight": l.count_weight})).collect::<Vec<_>>(),
        "child_vk_digest_b": hex(&s.child.child_vk), "compiled_program_sha256": hex(&s.child.program_sha256), "fri": f_params()})
}

/// A recomputed F key record against the pinned one, field by field.
pub fn check_f_vk(recomputed: &Value, pinned: &Value) -> Value {
    let fields = ["f_vk_digest", "domain", "rows", "log_n", "main_width", "bus_control_main", "periodic_columns", "periodic_columns_sha256",
        "public_values", "next_row_opened", "next_row_derived", "lookups", "child_vk_digest_b", "compiled_program_sha256", "fri"];
    let checks: Vec<(&str, bool)> = fields.iter().map(|f| (*f, recomputed[*f] == pinned[*f])).collect();
    json!({"all_equal": checks.iter().all(|(_, ok)| *ok), "fields": checks.iter().map(|(f, ok)| json!({"field": f, "equal": ok})).collect::<Vec<_>>()})
}

/// The process's current resident set (VmRSS), for the model's process base: what a proving process would hold besides
/// the prover once B's key data is dropped (the peak, VmHWM, includes B's key generation).
pub fn rss_now_kib() -> Option<u64> {
    let status = fs::read_to_string("/proc/self/status").ok()?;
    status.lines().find(|l| l.starts_with("VmRSS:"))?.split_whitespace().nth(1)?.parse().ok()
}

fn pv_json(pv: &[F]) -> Value {
    json!(pv.iter().map(|v| v.as_canonical_u32()).collect::<Vec<_>>())
}

/// B's proof a run uses: B's prove directory (statement.json, proof.postcard, report.json).
pub fn b_proof(dir: &Path, bc: &BChild) -> (Value, Vec<u8>, Vec<F>) {
    let st = crate::read_json(&dir.join("statement.json"));
    let report = crate::read_json(&dir.join("report.json"));
    assert_eq!(st["b2_vk_digest"].as_str().unwrap(), hex(&bc.vk), "B's proof names B's pinned verifier-key digest");
    let bytes = fs::read(dir.join("proof.postcard")).unwrap();
    assert_eq!(report["proof_sha256"].as_str().unwrap(), sha256_hex(&bytes), "B's proof file is the one its prove run recorded");
    let pv = crate::pv_from_json(&st["public_values"]);
    let expect = if report["in_process"]["accepted"] == json!(true) { "accepted" } else { "OodEvaluationMismatch" };
    (json!({"variant": st["variant"], "proof_sha256": sha256_hex(&bytes), "proof_bytes": bytes.len(),
        "b_in_process_verdict": report["in_process"], "native_expected": expect}), bytes, pv)
}

/// `f-compile`: B's AIR compiled with the kernel's compiler; the program file; the differential test.
pub fn f_compile_mode(in_dir: &Path, b_vk: &Path, out: &Path, points: usize) {
    fs::create_dir(out).expect("fresh output directory required");
    let t = Instant::now();
    let bc = fchild::b_child(in_dir, b_vk);
    let def_ms = ms(t);
    let t = Instant::now();
    let spec = fchild::b_spec(&bc);
    let compile_ms = ms(t);
    let p = &spec.program;
    let bytes = p.file_bytes(&hex(&spec.child_vk));
    assert_eq!(sha256_hex(&bytes), hex(&spec.program_sha256));
    save(&out.join("program-b.json"), &bytes);
    save(&out.join("program-b.json.gz"), &gzip(&bytes));
    let (base, ext) = fchild::b_symbolic(&bc);
    let ops = crate::compiler::executed_ops(&base, &ext);
    let diff = fchild::b_differential(&bc, &spec, points, 0x6631_d1ff);
    let doc = json!({"schema": crate::SCHEMA, "review": REVIEW, "tier": TIER, "child": spec.name, "b": bc.record,
        "compiled_program_sha256": hex(&spec.program_sha256), "compiled_program_bytes": bytes.len(),
        "b_constraints": {"base": base.len(), "logup": ext.len(), "executed_symbolic_operations": ops},
        "table": {"log_trace": spec.tables[0].log_trace, "width": spec.tables[0].width, "preprocessed_width": spec.tables[0].pre_width,
            "public_values": spec.tables[0].public.len(), "permutation_width_ef8": spec.tables[0].perm_width, "lookup_buses": spec.tables[0].lookup_bus,
            "log_quotient_degree": spec.tables[0].log_qd, "chunks": spec.tables[0].chunks},
        "buses": spec.num_buses, "max_message_width": spec.max_message_width,
        "stats": p.stats, "differential": diff,
        "timings_ms": {"l0p2_b_schedule_and_key": def_ms, "compile": compile_ms}, "peak_rss_kib": peak_rss_kib()});
    save(&out.join("differential.json"), &serde_json::to_vec_pretty(&doc).unwrap());
    event(json!({"phase": "f_compile_done", "instructions": p.instrs.len(), "values": p.n_values, "live_values_max": p.stats["live_values_max"],
        "sha256": hex(&spec.program_sha256), "differential_points": diff["selectors_constraints_folded_quotient_identity_and_terminal_verdict_equal_native"],
        "consistent": diff["consistent_points_accepted_by_both"], "dropped_differs": diff["dropped_lookup_constraint"]["folds_differing_from_native"],
        "base": base.len(), "logup": ext.len()}));
}

/// `f-schedule`: F's schedule for B (the smallest power-of-two table holding K1's rows and the ALU program with its
/// reserved rows), F's shape, F's verifier-key digest, the interface map and the program listing.
pub fn f_schedule_mode(in_dir: &Path, b_vk: &Path, out: &Path) {
    fs::create_dir(out).expect("fresh output directory required");
    let t = Instant::now();
    let bc = fchild::b_child(in_dir, b_vk);
    let spec = fchild::b_spec(&bc);
    let def_ms = ms(t);
    let t = Instant::now();
    let s = Schedule::build(&spec);
    let build_ms = ms(t);
    let t = Instant::now();
    let (cm, next, rule, vk) = f_identity(&s);
    let vk_ms = ms(t);
    save(&out.join("program-b.json"), &spec.program.file_bytes(&hex(&spec.child_vk)));
    save(&out.join("interface.json.gz"), &gzip(&serde_json::to_vec(&s.interface()).unwrap()));
    let listing = serde_json::to_vec(&s.program_json()).unwrap();
    save(&out.join("program-listing.json.gz"), &gzip(&listing));
    let shape = f_shape_doc(&s, &bc, &cm, &next, &rule, &vk);
    let doc = json!({"schema": crate::SCHEMA, "review": REVIEW, "tier": TIER, "shape": shape, "b_prefix": prefix_record(&s.child.prefix),
        "f_vk_digest": hex(&vk), "periodic_columns_sha256_u32le_column_major": periodic_sha256(&s),
        "listing_uncompressed_bytes": listing.len(), "listing_uncompressed_sha256": sha256_hex(&listing),
        "timings_ms": {"b_definition_and_compile": def_ms, "schedule": build_ms, "f_key_next_rows_and_vk_digest": vk_ms}, "peak_rss_kib": peak_rss_kib()});
    save(&out.join("f-schedule.json"), &serde_json::to_vec_pretty(&doc).unwrap());
    save(&out.join("f-vk.json"), &serde_json::to_vec_pretty(&f_vk_json(&s, &cm, &next, &vk)).unwrap());
    event(json!({"phase": "f_schedule_done", "n": s.n, "log_n": s.log_n, "used_rows": f_used_rows(&s), "margin_rows": s.n - f_used_rows(&s),
        "k1_rows": s.used_rows, "transcript_rows": s.t_rows, "per_query": s.block_rows, "alu": s.program.len(),
        "main_width": fkernel::WIDTH, "periodic": s.air.periodic.len(), "f_vk_digest": hex(&vk),
        "constraints": shape["constraints"]["base"], "max_degree": shape["constraints"]["max_degree_with_lookups"],
        "chunks": shape["constraints"]["quotient_chunks_with_zk"], "permutation_ef8": shape["columns"]["permutation_columns_ef8"],
        "next_row_main": shape["next_row_sets_c3n"]["main_next_row_columns"].as_array().map(Vec::len)}));
}

/// `f-trace`: B's proof replayed natively, F's honest trace, every native cross-check, every constraint of F on every
/// row, the bus, the LogUp check; the trace's hash (the trace stored outside the repository).
pub fn f_trace_mode(in_dir: &Path, b_vk: &Path, b_dir: &Path, out: &Path, save_path: Option<&Path>, f1_trace: Option<&Path>) {
    fs::create_dir(out).expect("fresh output directory required");
    ftracegen::ef_selftest();
    let t0 = Instant::now();
    let bc = fchild::b_child(in_dir, b_vk);
    let spec = fchild::b_spec(&bc);
    let s = Schedule::build(&spec);
    let schedule_ms = ms(t0);
    let t = Instant::now();
    let (cm, next, rule, vk) = f_identity(&s);
    let vk_ms = ms(t);
    let (brun, bytes, pv) = b_proof(b_dir, &bc);
    assert_eq!(brun["native_expected"], json!("accepted"), "the honest trace replays an accepted B proof");
    assert_eq!(pv, bc.statement, "B's statement is L0' v2's PI_bytes");
    let t = Instant::now();
    let (cd, replay_report) = fchild::replay_b(&bc, &s, &bytes, &pv, "accepted");
    let replay_ms = ms(t);
    let t = Instant::now();
    let (kt, _xs, honest_report) = ftracegen::honest(&s, &cd);
    let trace = kt.finalize();
    let tracegen_ms = ms(t);
    let t = Instant::now();
    let (constraints, check, names, _) = fcheck_report(&s, &trace, &cd.pv);
    let check_ms = ms(t);
    let t = Instant::now();
    let lcheck = flcheck::check(&s.air, &trace, &cd.pv, &cm.lookups[0], 0x6631_10c0);
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
    // (c)'s controls: F1's stored trace for the same B proof, and C3nP's periodic generation against p3-lookup's own
    // generation on the same lookups with every periodic column materialized as a main column.
    let t = Instant::now();
    let f1 = f1_trace.map(|p| f1_equivalence(&s, &trace, p));
    let materialized = periodic_generation_equivalence(&s, &trace, &cd.pv, &cm.lookups[0], 0x6632_0c0c);
    let equivalence_ms = ms(t);
    let equivalent = f1.as_ref().is_none_or(|v| v["equal"] == json!(true)) && materialized["equal"] == json!(true);
    let ok = names.is_empty() && lcheck["all_zero"] == json!(true) && lcheck["terminal_is_zero"] == json!(true) && equivalent;
    // The resident set with F's schedule, B's replay and F's trace held, B's key data dropped: the model's process base.
    let rss_with_trace = rss_now_kib();
    let shape = f_shape_doc(&s, &bc, &cm, &next, &rule, &vk);
    let doc = json!({"schema": crate::SCHEMA, "review": REVIEW, "tier": TIER, "n": 1, "child": s.child.name, "b_proof": brun,
        "result": if ok { "the honest trace satisfies every constraint of F (base constraints on every row, the bus balanced, the LogUp constraints and terminal)" } else { "VIOLATED" },
        "f_vk_digest": hex(&vk), "compiled_program_sha256": hex(&s.child.program_sha256), "statement": pv_json(&cd.pv),
        "statement_sha256": sha256_hex(&cd.pv.iter().flat_map(|v| v.as_canonical_u32().to_le_bytes()).collect::<Vec<u8>>()),
        "statement_is_l0p2_pi_bytes": cd.pv == bc.statement,
        "replay": replay_report, "honest_generation": honest_report,
        "constraint_check": {"constraints_per_row": constraints, "check": check},
        "logup_check": lcheck,
        "periodic_bus_control_controls": {"f1_stored_trace": f1, "c3np_generation_against_p3_lookup_materialized": materialized},
        "trace": {"rows": trace.height(), "width": trace.width(), "bytes_u32le": tb.len(), "sha256_u32le_row_major": trace_sha,
            "stored": save_path.map(|p| p.with_extension("trace.u32le").display().to_string())},
        "shape": shape,
        "timings_ms": {"b_definition_compile_schedule": schedule_ms, "f_key_next_rows_vk_digest": vk_ms, "replay_open_inputs_identity": replay_ms,
            "trace_generation_and_native_checks": tracegen_ms, "constraint_and_bus_check": check_ms, "logup_check": lcheck_ms, "hash_and_save": hash_ms,
            "equivalence_controls": equivalence_ms},
        "rss_kib_with_the_trace_held": rss_with_trace, "peak_rss_kib": peak_rss_kib()});
    save(&out.join("trace-report.json"), &serde_json::to_vec_pretty(&doc).unwrap());
    event(json!({"phase": "f_trace_done", "ok": ok, "violated": names, "logup_all_zero": lcheck["all_zero"],
        "terminal_zero": lcheck["terminal_is_zero"], "n": s.n, "used_rows": f_used_rows(&s), "trace_sha256": trace_sha, "f_vk_digest": hex(&vk),
        "f1_trace_equal_without_the_14_copies": f1.as_ref().map(|v| v["equal"].clone()), "c3np_generation_equal_to_p3_lookup_materialized": materialized["equal"],
        "peak_rss_kib": peak_rss_kib()}));
    if !ok {
        std::process::exit(3);
    }
}

/// F1's honest trace for the same B proof (stored by F1's record outside the repository; its SHA-256 recorded in F1's
/// results): F1's width 271 = F2's 257 + B1's 14 bus-control copies. The control: F2's trace equals F1's with those 14
/// columns removed, and each of them equals its periodic column on every row (what F1's `bus.control` pinned), so F2's
/// bus messages and counts equal F1's on every row.
pub const F1_TRACE_SHA256: &str = "acd843e90add69b12ce277fa64dc0a7fec3118074c1800290112c9dbd4077ed9";
pub const F1_WIDTH: usize = 271;

pub fn f1_equivalence(s: &Schedule, trace: &RowMajorMatrix<F>, path: &Path) -> Value {
    use fkernel::{ADDR_A, CTRL, DL, MULT_R, NCTRL, WIDTH};
    let bytes = fs::read(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    let sha = sha256_hex(&bytes);
    assert_eq!(sha, F1_TRACE_SHA256, "F1's stored trace is the one F1's record hashed");
    let n = trace.height();
    assert_eq!(bytes.len(), n * F1_WIDTH * 4, "F1's trace: 2^14 rows of 271 columns");
    let f1 = |r: usize, c: usize| u32::from_le_bytes(bytes[4 * (r * F1_WIDTH + c)..4 * (r * F1_WIDTH + c) + 4].try_into().unwrap());
    // F1's column of each F2 column.
    let map: Vec<usize> = (0..WIDTH)
        .map(|c| match c {
            c if c < CTRL => c,
            c if c == CTRL + fkernel::CM_ADDR_A => CTRL + ADDR_A,
            c if c == CTRL + fkernel::CM_MULT_R => CTRL + MULT_R,
            c => c - DL + CTRL + NCTRL,
        })
        .collect();
    let p = &s.air.pidx;
    let (mut differing_cells, mut first_diff) = (0usize, None);
    let (mut copy_mismatches, mut first_copy_mismatch) = (0usize, None);
    for r in 0..n {
        for (c, &c1) in map.iter().enumerate() {
            if trace.values[r * WIDTH + c].as_canonical_u32() != f1(r, c1) {
                differing_cells += 1;
                first_diff.get_or_insert((r, c, c1));
            }
        }
        for k in (0..NCTRL).filter(|&k| k != ADDR_A && k != MULT_R) {
            if s.air.periodic[p.ctrl[k]][r].as_canonical_u32() != f1(r, CTRL + k) {
                copy_mismatches += 1;
                first_copy_mismatch.get_or_insert((r, k));
            }
        }
    }
    json!({"what": "F2's honest trace against F1's stored honest trace for the same B proof: F2's 257 columns equal F1's columns at the mapped positions (B1's 14 bus-control copies removed), and each removed copy equals its periodic column on every row",
        "f1_trace_path": path.display().to_string(), "f1_trace_sha256": sha, "rows": n, "f1_width": F1_WIDTH, "f2_width": WIDTH,
        "removed_f1_columns": (0..NCTRL).filter(|&k| k != ADDR_A && k != MULT_R).map(|k| CTRL + k).collect::<Vec<_>>(),
        "cells_compared": n * WIDTH, "differing_cells": differing_cells, "first_difference_row_f2column_f1column": first_diff,
        "copy_cells_compared": n * (NCTRL - 2), "copies_differing_from_their_periodic_column": copy_mismatches, "first_copy_mismatch_row_k": first_copy_mismatch,
        "equal": differing_cells == 0 && copy_mismatches == 0})
}

/// A symbolic expression with every periodic leaf k replaced by the main column `width + k`.
fn materialize(e: &p3_air::symbolic::SymbolicExpression<F>, width: usize) -> p3_air::symbolic::SymbolicExpression<F> {
    use p3_air::symbolic::{BaseEntry, BaseLeaf, SymbolicExpr, SymbolicVariable};
    match e {
        SymbolicExpr::Leaf(BaseLeaf::Variable(v)) if matches!(v.entry, BaseEntry::Periodic) => {
            SymbolicVariable::<F>::new(BaseEntry::Main { offset: 0 }, width + v.index).into()
        }
        SymbolicExpr::Leaf(_) => e.clone(),
        SymbolicExpr::Add { x, y, .. } => materialize(x, width) + materialize(y, width),
        SymbolicExpr::Sub { x, y, .. } => materialize(x, width) - materialize(y, width),
        SymbolicExpr::Neg { x, .. } => -materialize(x, width),
        SymbolicExpr::Mul { x, y, .. } => materialize(x, width) * materialize(y, width),
    }
}

/// C3nP's `generate_permutation_periodic` on F's trace and lookups against p3-lookup's own `generate_permutation` on the
/// same lookups with every periodic leaf rewritten to a main column of an augmented trace (F's columns, then the
/// periodic columns' values): the two permutation traces and terminals must be equal, with the same challenges (random,
/// laid out as the batch transcript lays them out for one global bus, as `flcheck` does, so the honest terminal is zero).
pub fn periodic_generation_equivalence(s: &Schedule, trace: &RowMajorMatrix<F>, pv: &[F], lookups: &[p3_lookup::Lookup<F>], seed: u64) -> Value {
    use p3_field::BasedVectorSpace;
    use rand::{RngExt, SeedableRng};
    let gadget = LogUpGadget::new();
    let mut rng = StdRng::seed_from_u64(seed);
    let rand_ef = |rng: &mut StdRng| EF::from_basis_coefficients_fn(|_| rng.random::<F>());
    let (alpha, beta) = (rand_ef(&mut rng), rand_ef(&mut rng));
    let width = lookups.iter().map(|l| l.elements.first().map(Vec::len).unwrap_or(1)).max().unwrap_or(1);
    let ch = p3_lookup::Challenges::new(alpha, beta, width, 1);
    let challenges: Vec<EF> = lookups.iter().flat_map(|_| [ch.bus_prefix[0], beta]).collect();
    let (w, n, np) = (trace.width(), trace.height(), s.air.periodic.len());
    let reads_periodic = lookups.iter().any(|l| {
        let mut found = false;
        for e in l.elements.iter().flatten().chain(&l.multiplicities) {
            found |= format!("{e:?}").contains("Periodic");
        }
        found
    });
    let materialized: Vec<p3_lookup::Lookup<F>> = lookups
        .iter()
        .map(|l| {
            let mut m = l.clone();
            m.elements = l.elements.iter().map(|t| t.iter().map(|e| materialize(e, w)).collect()).collect();
            m.multiplicities = l.multiplicities.iter().map(|e| materialize(e, w)).collect();
            m.flags = l.flags.as_ref().map(|f| f.iter().map(|e| materialize(e, w)).collect());
            m
        })
        .collect();
    let mut aug = Vec::with_capacity(n * (w + np));
    for r in 0..n {
        aug.extend_from_slice(&trace.values[r * w..(r + 1) * w]);
        aug.extend(s.air.periodic.iter().map(|col| col[r % col.len()]));
    }
    let aug = RowMajorMatrix::new(aug, w + np);
    let t = Instant::now();
    let (a, ta) = p3_batch_stark_c3np::generate_permutation_periodic::<F, EF>(&gadget, trace, &None, &s.air.periodic, pv, lookups, &challenges);
    let c3np_ms = ms(t);
    let t = Instant::now();
    let (b, tb) = gadget.generate_permutation::<F, EF>(&aug, &None, pv, &materialized, &challenges);
    let p3_ms = ms(t);
    let hash = |m: &RowMajorMatrix<EF>| {
        let mut h = Sha256::new();
        for v in &m.values {
            for c in <EF as BasedVectorSpace<F>>::as_basis_coefficients_slice(v) {
                h.update(c.as_canonical_u32().to_le_bytes());
            }
        }
        hex(&h.finalize())
    };
    let differing = a.values.iter().zip(&b.values).filter(|(x, y)| x != y).count();
    let (ta, tb) = (ta.as_ref().map(|t| t.0), tb.as_ref().map(|t| t.0));
    let equal = a.width() == b.width() && a.height() == b.height() && differing == 0 && ta == tb;
    json!({"what": "C3nP's permutation-trace generation (periodic columns in the row context) on F's trace and lookups, against p3-lookup's own generation on the same lookups with every periodic leaf rewritten to a main column of an augmented trace (F's columns, then the periodic values), with the same random challenges",
        "challenge_seed": format!("{seed:#x}"), "lookups_read_periodic_columns": reads_periodic, "augmented_width": w + np,
        "permutation_width_ef8": a.width(), "rows": a.height(), "differing_ef8_values": differing,
        "c3np_permutation_sha256": hash(&a), "p3_lookup_permutation_sha256": hash(&b),
        "terminals_equal": ta == tb, "terminal_is_zero": ta == Some(EF::ZERO),
        "c3np_ms": c3np_ms, "p3_lookup_ms": p3_ms, "equal": equal})
}

/// `f-negative`: one trace-level negative on F's trace for B: the honest trace from B's proof (or the variant's child, a
/// natively invalid B), the variant's edit, the constraint and bus check on every row; the targeted group must be
/// violated (and, where stated, nothing else).
pub fn f_negative_mode(variant: &str, in_dir: &Path, b_vk: &Path, b_dir: &Path, child_dir: Option<&Path>, out: &Path) {
    fs::create_dir(out).expect("fresh output directory required");
    let exp = fvariants::expected(variant);
    let bc = fchild::b_child(in_dir, b_vk);
    let spec = fchild::b_spec(&bc);
    let s = Schedule::build(&spec);
    let (_, _, _, vk) = f_identity(&s);
    let dir = child_dir.unwrap_or(b_dir);
    let (brun, bytes, pv0) = b_proof(dir, &bc);
    assert_eq!(exp.child_level, child_dir.is_some(), "a child-level variant names its child; the others use B's accepted proof");
    let t = Instant::now();
    let (cd, replay_report) = fchild::replay_b(&bc, &s, &bytes, &pv0, brun["native_expected"].as_str().unwrap());
    let (mut kt, xs, honest_report) = ftracegen::honest(&s, &cd);
    let honest_trace = kt.finalize();
    let (constraints, honest_check, honest_names, honest_roles) = fcheck_report(&s, &honest_trace, &cd.pv);
    if exp.child_level {
        assert!(fvariants::exact_met(&exp, &honest_names, &honest_roles), "the variant child's trace: {honest_check}");
    } else {
        assert_eq!(honest_names, exp.honest, "the honest generation from B's proof: {honest_check}");
    }
    let mut pv = cd.pv.clone();
    let edit = if exp.child_level || variant == "P" { json!({"edit": "none: the honest generation from the child"}) } else { fvariants::apply(variant, &mut kt, &s, &cd, &xs, &mut pv) };
    let trace = if variant == "P" || exp.child_level { honest_trace } else { kt.finalize() };
    let (_, this_check, names, roles) = fcheck_report(&s, &trace, &pv);
    let targeted = fvariants::target_met(&exp, &names, &roles);
    let rejected = !names.is_empty();
    let as_expected = rejected == (exp.expect == "reject") && targeted;
    let doc = json!({"schema": crate::SCHEMA, "review": REVIEW, "tier": TIER, "variant": variant, "child": s.child.name,
        "expected": exp.expect, "targeted_constraint_group": exp.target, "expected_exact_violations": exp.exact, "expected_alu_roles": exp.roles,
        "edit": edit, "b_proof": brun,
        "constraint_check": {"constraints_per_row": constraints, "rows": s.n,
            "honest_generation_violations": honest_names, "this_trace": this_check, "targeted_group_violated": targeted},
        "verdict": if rejected { "REJECTED by constraints" } else { "every constraint holds" }, "as_expected": as_expected,
        "f_vk_digest": hex(&vk), "replay": replay_report, "honest_generation": honest_report,
        "ms": ms(t), "peak_rss_kib": peak_rss_kib()});
    save(&out.join("negative.json"), &serde_json::to_vec_pretty(&doc).unwrap());
    event(json!({"phase": "f_negative_done", "variant": variant, "verdict": doc["verdict"], "violated": names, "roles": roles,
        "targeted": targeted, "as_expected": as_expected}));
    if !as_expected {
        std::process::exit(3);
    }
}

/// A changed verifier's schedule at the honest table height (a control must not move the height).
fn rebuilt(spec: &fschedule::ChildSpec, log_n: usize) -> Schedule {
    Schedule::build_with(spec, true, log_n).unwrap_or_else(|need| panic!("the changed verifier's schedule needs {need} rows"))
}

/// `f-controls`: F's honest trace for B (it satisfies every constraint of the honest F) checked under changed verifiers:
/// F's schedule (one fold butterfly as a product), B's pinned preprocessed cap (one element), B's identity in B's prefix
/// (one byte of B's verifier-key digest), the compiled program of B (one LogUp fraction pin dropped), the public-value
/// binding map (one absorbed lane bound to another public value). Each changed verifier has another F verifier-key
/// digest and the honest trace violates its constraints; no proof is made.
pub fn f_controls_mode(in_dir: &Path, b_vk: &Path, b_dir: &Path, out: &Path) {
    fs::create_dir(out).expect("fresh output directory required");
    let bc = fchild::b_child(in_dir, b_vk);
    let spec = fchild::b_spec(&bc);
    let s = Schedule::build(&spec);
    let (_, _, _, vk) = f_identity(&s);
    let (_, bytes, pv) = b_proof(b_dir, &bc);
    let (cd, _) = fchild::replay_b(&bc, &s, &bytes, &pv, "accepted");
    let (kt, _, _) = ftracegen::honest(&s, &cd);
    let trace = kt.finalize();
    drop(kt);
    let (_, _, honest_names, _) = fcheck_report(&s, &trace, &cd.pv);
    assert!(honest_names.is_empty(), "the honest trace satisfies the honest F");
    let mut rows = vec![];
    let mut record = |case: &str, what: &str, s2: &Schedule| {
        let (_, _, _, vk2) = f_identity(s2);
        let (_, doc, names, _) = fcheck_report(s2, &trace, &cd.pv);
        let row = json!({"case": case, "what": what, "f_vk_digest": hex(&vk2), "digest_differs": vk2 != vk, "rows": s2.n,
            "violated": names, "failing_evaluations": doc["failing_constraint_evaluations"], "unbalanced_tuples": doc["bus"]["unbalanced_tuples"],
            "as_expected": vk2 != vk && !names.is_empty()});
        event(json!({"phase": "f_control", "control": row}));
        rows.push(row);
    };
    // F's schedule: one fold butterfly (query 5, round 1) computed as a product.
    let target = s.program.iter().position(|i| i.role == "fri.fold" && i.query == Some(5) && i.round == Some(1)).unwrap();
    let mut bad = rebuilt(&spec, s.log_n);
    let (bf, mu) = (bad.air.pidx.op[2], bad.air.pidx.op[0]);
    let row = s.instr_row[target];
    bad.air.periodic[bf][row] = F::ZERO;
    bad.air.periodic[mu][row] = F::ONE;
    record("schedule_opcode", "a verifier whose schedule computes one fold butterfly of B's FRI (query 5, round 1) as a product", &bad);
    drop(bad);
    // B's pinned preprocessed cap: entry 3, element 2 plus one.
    let mut wrong_pre = spec.clone();
    wrong_pre.pre_cap[3][2] += F::ONE;
    record("b_pinned_preprocessed_cap", "a verifier pinning another preprocessed cap of B (entry 3, element 2 plus one)", &rebuilt(&wrong_pre, s.log_n));
    // B's identity in B's prefix: B's verifier-key digest with byte 0 flipped (and the child identity F's digest covers).
    let mut wrong_vk = spec.clone();
    for item in wrong_vk.prefix.iter_mut() {
        if let PrefixItem::Bytes(name, b) = item {
            if name == "b_vk_digest" {
                b[0] ^= 1;
            }
        }
    }
    wrong_vk.child_vk[0] ^= 1;
    record("b_vk_digest_in_prefix", "a verifier absorbing another B verifier-key digest (byte 0 flipped) in B's prefix", &rebuilt(&wrong_vk, s.log_n));
    // The compiled program of B without B's first LogUp fraction pin.
    let (_, dropped, _) = fchild::compile_b(&bc, crate::compiler::Options::default(), Some(0));
    record("program_dropped_logup_constraint", "a verifier whose program of B is compiled without B's first LogUp fraction pin", &rebuilt(&fchild::b_spec_with_program(&spec, dropped), s.log_n));
    // The public-value binding map: the first binding term rebound to another public value of a different value.
    let mut bad2 = rebuilt(&spec, s.log_n);
    let target2 = (0..8).find_map(|l| bad2.air.pub_terms[l].iter().enumerate().find_map(|(t, &(_, j))| (0..cd.pv.len()).find(|&k| cd.pv[k] != cd.pv[j]).map(|j2| (l, t, j2))));
    let (lane, ti, j2) = target2.expect("two different public values");
    bad2.air.pub_terms[lane][ti].1 = j2;
    record("public_binding_map", &format!("a verifier whose transcript.public binds one absorbed lane (lane {lane}, term {ti}) to public value {j2}, whose value differs"), &bad2);
    drop(bad2);
    let all = rows.iter().all(|r| r["as_expected"].as_bool().unwrap());
    let doc = json!({"schema": crate::SCHEMA, "review": REVIEW, "tier": TIER, "f_vk_digest_honest": hex(&vk),
        "what": "F's honest trace for B (it satisfies every constraint of the honest F) checked under changed verifiers; each changed verifier has another F verifier-key digest; no proof is made",
        "all_as_expected": all, "controls": rows, "peak_rss_kib": peak_rss_kib()});
    save(&out.join("controls.json"), &serde_json::to_vec_pretty(&doc).unwrap());
    if !all {
        std::process::exit(3);
    }
}

/// The prefix items as recorded.
pub fn prefix_record(prefix: &[PrefixItem]) -> Value {
    json!(prefix.iter().map(|it| match it {
        PrefixItem::Bytes(n, b) => json!({"name": n, "kind": "constant bytes (length, then each byte)", "bytes": b.len()}),
        PrefixItem::PubBytes(n, f, l) => json!({"name": n, "kind": "statement (length, then F's public values)", "public_values": [f, f + l]}),
        PrefixItem::Fields(n, f) => json!({"name": n, "kind": "constant field elements", "elements": f.len()}),
    }).collect::<Vec<_>>())
}
