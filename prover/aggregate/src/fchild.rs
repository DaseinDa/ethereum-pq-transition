//! F1 (L5, 2026-11-01): B as F's child. B is B2's kernel layer B for L0' v2 (its AIR, schedule and compiled program
//! byte-identical to B2's: `kernel.rs`, `schedule.rs`, `compiler.rs`), re-proven with p3_batch_stark_c3 (C3b's copy of
//! p3-batch-stark) under the kernel's child tail: Merkle cap height 5 and FRI arity at most 4. This module describes B
//! as F's verifier pins it and replays B's native verification for F's trace generator (`ftracegen.rs`):
//! - **B's identity**: L0' v2's key recomputed and checked against L0' v2's vk.json (B2's `l0p2_def`), B's schedule and
//!   key recomputed from the seed (`b2_keygen`) and checked against B's pinned vk.json field by field, B's verifier-key
//!   digest (`b2_vk_digest`);
//! - **B's prefix** exactly as B's configuration absorbs it (`b2_config`): B's domain and verifier-key digest as constant
//!   bytes (each its length, then its bytes), then the statement (its length, then the 198 public values);
//! - **B's AIR compiled** with the kernel's compiler (`compiler.rs`, G1's, unchanged): B's base and LogUp constraints as
//!   p3_batch_stark_c3's own symbolic evaluation builds them with B's key's packed lookups, B's preprocessed columns as
//!   claims at zeta, B's public values; and **F's child specification of B**: one table of 2^16 rows, C3 (not C3n): the
//!   main trace (the library's default next-row set: every column) and the permutation trace opened in full at zeta and
//!   zeta * g, the preprocessed trace at zeta only (B's AIR reads none of it at the next row); the batch seed from
//!   p3_batch_stark_c3's `BatchShape` (no next-row bitmaps), the PCS and FRI seeds from the claims' shape and B's FRI
//!   parameters;
//! - **the replay**: p3_batch_stark_c3::verify_batch, unchanged, under B's configuration with B2's recording wrappers
//!   (`replay.rs`: every duplexing, every multi-opening with its cap and pruned paths), p3-fri's own `open_inputs` per
//!   height on the claims C3's own `commitments_with_opening_points` builds, and the native values of B's identity
//!   (`VerifierConstraintFolderWithLookups` of C3, the AIR's own eval through the LogUp gadget) and of the terminal sum.
//! The kernel's constraints, not this module, decide acceptance; this module only supplies the honest witness and the
//! native values the trace generator checks itself against.
//! Research measurement; loop-internal self-review; not independently reviewed.
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::sync::Arc;
use std::time::Instant;

use p3_air::symbolic::AirLayout;
use p3_air::{BaseAir, RowWindow};
use p3_commit::{Pcs, PolynomialSpace};
use p3_field::{BasedVectorSpace, ExtensionField, Field, PrimeCharacteristicRing};
use p3_fri::{FriParameters, FriShape, PcsShape, fold_schedule};
use p3_koala_bear::{KoalaBear as F, default_koalabear_poseidon2_16};
use p3_lookup::{LogUpGadget, LookupProtocol};
use p3_matrix::dense::RowMajorMatrixView;
use p3_matrix::stack::VerticalPair;
use rand::rngs::StdRng;
use rand::{RngExt, SeedableRng};
use serde_json::{Value, json};
use sha2::{Digest as _, Sha256};

use crate::compiler::{self, CVal, Input, Options, Program, Sel, TableConstraints, TableShape};
use crate::fschedule::{self, ChildSpec, PrefixItem, TableSpec};
use crate::ftracegen::{ChildData, NativeG1, NativeTable, to_ef};
use crate::{
    B_DOMAIN, BKey, CAP_HEIGHT, ChMmcs, Challenger, Claims, Compress, Config, EF, HPcs, Hash, K_CAP_HEIGHT, K_LOG_BLOWUP,
    K_LOG_FINAL_POLY_LEN, K_MAX_LOG_ARITY, K_QUERIES, KCommon, KProof, Mmcs, PointBuilder, RANDOM_CODEWORDS, Rec, SALT_ELEMS, hex,
    ms, os_rng, peak_rss_kib, replay, sha256_hex,
};

/// B's FRI parameters (B's PCS, `b2_pcs`): blowup 2^6, a final polynomial of 2^2 coefficients, arity at most 2^2,
/// 43 queries, cap height 5, no grinding.
pub fn b_fri_params(rng: StdRng) -> FriParameters<ChMmcs> {
    let perm = default_koalabear_poseidon2_16();
    FriParameters {
        log_blowup: K_LOG_BLOWUP,
        log_final_poly_len: K_LOG_FINAL_POLY_LEN,
        max_log_arity: K_MAX_LOG_ARITY,
        num_queries: K_QUERIES,
        batch_proof_of_work_bits: 0,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 0,
        mmcs: ChMmcs::new(Mmcs::new(Hash::new(perm.clone()), Compress::new(perm), K_CAP_HEIGHT, rng)),
    }
}

/// B as F's verifier pins it.
pub struct BChild {
    /// B's schedule for L0' v2 (B2's; B's AIR is `s.air`).
    pub s: crate::schedule::Schedule,
    /// B's key's common data: the pinned preprocessed commitment and the packed lookups.
    pub common: KCommon,
    pub key: BKey,
    /// B's verifier-key digest.
    pub vk: [u8; 32],
    pub vk_check: Value,
    /// B's statement: L0' v2's PI_bytes, 198 public values.
    pub statement: Vec<F>,
    /// B's prefix as B's configuration absorbs it.
    pub prefix: Vec<PrefixItem>,
    pub record: Value,
}

/// B's definition: L0' v2's key checked, B's schedule, B's key recomputed from its seed and checked against B's pinned
/// vk.json, B's verifier-key digest and prefix.
pub fn b_child(in_dir: &Path, b_vk_path: &Path) -> BChild {
    let t = Instant::now();
    let def = crate::l0p2_def(in_dir);
    let spec = crate::child_spec(&def);
    let s = crate::schedule::Schedule::build(&spec);
    let schedule_ms = ms(t);
    let (data, key) = crate::b2_keygen(&s);
    let vk = crate::b2_vk_digest(&s, &key);
    let vk_check = crate::check_b2_vk(&crate::b2_vk_json(&s, &data.common, &key, &vk), &crate::read_json(b_vk_path));
    assert_eq!(vk_check["all_equal"], json!(true), "B's recomputed key differs from B's pinned vk.json: {vk_check}");
    let crate::KData { common, prover_only } = data;
    drop(prover_only);
    let statement = def.statement.clone();
    // b2_config: observe(|domain|), domain bytes; observe(|vk|), vk bytes; observe(|pv|), pv.
    let prefix = vec![
        PrefixItem::Bytes("b_domain".into(), B_DOMAIN.to_vec()),
        PrefixItem::Bytes("b_vk_digest".into(), vk.to_vec()),
        PrefixItem::PubBytes("statement".into(), 0, statement.len()),
    ];
    let record = json!({"b_vk_digest": hex(&vk), "b_domain": String::from_utf8_lossy(B_DOMAIN), "b_rows": s.n, "b_log_n": s.log_n,
        "b_main_width": crate::kernel::WIDTH, "b_preprocessed_width": s.air.pre.len(), "b_public_values": s.num_public,
        "b_air_digest": hex(&key.air_digest), "b_program_digest": hex(&key.program_digest), "b_salt_seed": hex(&key.salt_seed),
        "b_preprocessed_cap_entries": key.commitment.roots().len(), "b_compiled_l0p2_program_sha256": hex(&s.child.program_sha256),
        "b_key_recomputed_against_vk_json": vk_check, "b_keygen_ms": key.keygen_ms, "l0p2_and_b_schedule_ms": schedule_ms,
        "l0p2_definition": def.record});
    BChild { s, common, key, vk, vk_check, statement, prefix, record }
}

/// The global bus index of every lookup, the bus count and the widest tuple (C3's `lay_out_lookup_challenges`).
pub fn bus_layout_lk(all: &[p3_lookup::Lookups<F>]) -> (Vec<Vec<usize>>, usize, usize) {
    let mut names: Vec<String> = vec![];
    let mut next = 0;
    let mut width = 1;
    let mut out = vec![];
    for lk in all {
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
    (out, next, width)
}

/// B's symbolic constraints (base, LogUp) as p3_batch_stark_c3's symbolic evaluation builds them with B's key's lookups.
pub fn b_symbolic(bc: &BChild) -> (Vec<p3_air::symbolic::SymbolicExpression<F>>, Vec<p3_air::symbolic::SymbolicExpressionExt<F, EF>>) {
    let air = &bc.s.air;
    let lk: &[p3_lookup::Lookup<F>] = &bc.common.lookups[0];
    let gadget = LogUpGadget::new();
    p3_batch_stark_c3::symbolic::get_symbolic_constraints::<F, EF, _, _>(air, AirLayout::from_air(air), lk, &gadget)
}

/// B's AIR compiled into one straight-line EF8 program (the kernel's compiler, unchanged); `drop_ext` drops one LogUp
/// constraint (the changed-program check). Returns B's table shape, the program and its file's SHA-256.
pub fn compile_b(bc: &BChild, opts: Options, drop_ext: Option<usize>) -> (TableShape, Program, [u8; 32]) {
    let air = &bc.s.air;
    let lk: &[p3_lookup::Lookup<F>] = &bc.common.lookups[0];
    let layout = AirLayout::from_air(air);
    let gadget = LogUpGadget::new();
    let (base, mut ext) = b_symbolic(bc);
    if let Some(k) = drop_ext {
        ext.remove(k);
    }
    let pcs = crate::b2_pcs([os_rng(), os_rng(), os_rng()]);
    let init = <HPcs as Pcs<EF, Challenger>>::natural_domain_for_degree(&pcs, bc.s.n);
    let lqd = p3_batch_stark_c3::symbolic::get_log_num_quotient_chunks_for_domain::<F, EF, _, _>(air, layout, init, lk, 1, &gadget);
    let (buses, nbus, width) = bus_layout_lk(&bc.common.lookups);
    let shape = TableShape {
        name: "B".into(),
        log_trace: bc.s.log_n,
        log_ext: bc.s.log_n + 1,
        width: BaseAir::<F>::width(air),
        num_public: BaseAir::<F>::num_public_values(air),
        preprocessed_width: air.pre.len(),
        perm_width: if lk.is_empty() { 0 } else { lk.len() + 1 },
        lookup_bus: buses[0].clone(),
        log_quotient_degree: lqd,
        chunks: 1usize << (lqd + 1),
    };
    let tc = vec![TableConstraints { base: &base, ext: &ext }];
    let p = compiler::compile(std::slice::from_ref(&shape), &tc, nbus, width, opts);
    let digest: [u8; 32] = Sha256::digest(p.file_bytes(&hex(&bc.vk))).into();
    (shape, p, digest)
}

/// F's child specification of B from B's compiled program: the table, the FRI tail, the prefix, the three transcript
/// seeds of p3_batch_stark_c3 (the batch seed has no next-row bitmaps), the pinned preprocessed cap, the lookup layout.
pub fn b_spec_from(bc: &BChild, shape: TableShape, program: Program, program_sha256: [u8; 32]) -> ChildSpec {
    let air = &bc.s.air;
    let width = BaseAir::<F>::width(air);
    let (buses, nbus, mw) = bus_layout_lk(&bc.common.lookups);
    // C3 (p3_batch_stark_c3, verifier/mod.rs l. 107-345): the main trace is opened at zeta * g in full as soon as the AIR
    // declares a next-row column (B's AIR keeps the library's default: every column); the preprocessed trace at zeta
    // only (B's AIR declares none at the next row); every permutation trace at zeta and zeta * g in full.
    let next_main = BaseAir::<F>::main_next_row_columns(air);
    assert_eq!(next_main, (0..width).collect::<Vec<_>>(), "C3 opens B's whole main trace at zeta * g");
    let next_pre = BaseAir::<F>::preprocessed_next_row_columns(air);
    assert!(next_pre.is_empty(), "B's preprocessed trace is opened at zeta only");
    let table = TableSpec {
        name: shape.name.clone(),
        log_trace: shape.log_trace,
        width,
        pre_width: air.pre.len(),
        public: (0..bc.s.num_public).collect(),
        next_main,
        next_pre,
        next_perm: (0..shape.perm_width).collect(),
        perm_width: shape.perm_width,
        lookup_bus: buses[0].clone(),
        log_qd: shape.log_quotient_degree,
        chunks: shape.chunks,
    };
    let index_bits = shape.log_trace + 1 + K_LOG_BLOWUP;
    let arities = fold_schedule(&[index_bits], K_LOG_BLOWUP + K_LOG_FINAL_POLY_LEN, K_MAX_LOG_ARITY);
    // The batch transcript's seed (C3 transcript.rs l. 202-440: no next-row bitmaps).
    let bshape = p3_batch_stark_c3::BatchShape {
        trace_widths: vec![width],
        public_value_counts: vec![bc.s.num_public],
        preprocessed_widths: vec![air.pre.len()],
        has_preprocessed_commitment: bc.common.preprocessed.is_some(),
        num_lookup_instances: 1,
        lookup_pow_bits: 0,
        has_randomization_commitment: true,
        ood_pow_bits: 0,
    };
    let mut batch = Rec(vec![]);
    bshape.domain_separator::<F, EF>().seed(&mut batch);
    let draft = ChildSpec {
        name: "B (B2's kernel layer B for L0' v2: one table of 2^16 rows, 265 main and 139 preprocessed columns, one LogUp bus of 10 slots packed into 4 fraction columns), re-proven with p3_batch_stark_c3 at cap height 5, FRI arity <= 4, blowup 2^6, 43 queries, a final polynomial of 4 coefficients".into(),
        tables: vec![table],
        rc: RANDOM_CODEWORDS,
        salt: SALT_ELEMS,
        log_blowup: K_LOG_BLOWUP,
        log_final_poly_len: K_LOG_FINAL_POLY_LEN,
        max_log_arity: K_MAX_LOG_ARITY,
        num_queries: K_QUERIES,
        index_bits,
        fri_log_arities: arities.clone(),
        prefix: bc.prefix.clone(),
        num_public: bc.s.num_public,
        seeds: [vec![], vec![], vec![]],
        child_vk: bc.vk,
        pre_cap: bc.key.commitment.roots().to_vec(),
        num_buses: nbus,
        max_message_width: mw,
        program: Arc::new(program),
        program_sha256,
    };
    // The PCS's seed from the claimed-evaluation counts the trees fix (pcs_transcript.rs l. 98-164).
    let trees = fschedule::trees(&draft);
    let counts: Vec<Vec<Vec<usize>>> = trees
        .iter()
        .filter(|t| matches!(t.kind, fschedule::TreeKind::Input(_)))
        .map(|t| t.mats.iter().map(|m| m.points.iter().map(|_| m.width).collect()).collect())
        .collect();
    let mut pcs = Rec(vec![]);
    PcsShape { claimed_evaluation_counts: counts, batch_pow_bits: 0 }.domain_separator::<F, EF>().seed(&mut pcs);
    let mut fri = Rec(vec![]);
    FriShape::with_schedule(&b_fri_params(os_rng()), arities, index_bits).domain_separator::<F, EF>().seed(&mut fri);
    ChildSpec { seeds: [batch.0, pcs.0, fri.0], ..draft }
}

pub fn b_spec(bc: &BChild) -> ChildSpec {
    let (shape, program, sha) = compile_b(bc, Options::default(), None);
    b_spec_from(bc, shape, program, sha)
}

/// The same specification with another compiled program (the changed-program check).
pub fn b_spec_with_program(spec: &ChildSpec, program: Program) -> ChildSpec {
    let mut s = spec.clone();
    s.program_sha256 = Sha256::digest(program.file_bytes(&hex(&spec.child_vk))).into();
    s.program = Arc::new(program);
    s
}

/// The lookup challenges as the batch transcript lays them out (C3 transcript.rs l. 461-541): per lookup, the prefix of
/// its bus (alpha_L + (bus + 1) gamma, gamma = beta_L^W) and beta_L.
pub fn lookup_challenges_f(spec: &ChildSpec, la: EF, lb: EF) -> Vec<Vec<EF>> {
    let gamma = lb.exp_u64(spec.max_message_width as u64);
    let prefix: Vec<EF> = (0..spec.num_buses).map(|b| la + gamma * F::from_usize(b + 1)).collect();
    spec.tables.iter().map(|t| t.lookup_bus.iter().flat_map(|&b| [prefix[b], lb]).collect()).collect()
}

/// The native verifier's values of B's identity and of the terminal check, with C3's and p3-commit's functions:
/// `selectors_at_point` and `vanishing_poly_at_point` over B's trace domain, every constraint by the AIR's own eval through
/// the LogUp gadget (`PointBuilder`), the accumulator of C3's `VerifierConstraintFolderWithLookups` (verifier/data.rs
/// l. 53-123, the preprocessed next row zero as C3's verifier passes it, mod.rs l. 783-792), the chunk domains and factors,
/// `recompose_quotient_from_chunks`, folded * inv_vanishing = quotient, and `verify_terminal_sum`.
pub fn native_b(spec: &ChildSpec, air: &crate::kernel::KernelAir, common: &KCommon, ov: &p3_batch_stark_c3::BatchOpenedValues<EF>,
    terminals: &[Option<p3_lookup::LookupTerminal<EF>>], public: &[F], alpha: EF, zeta: EF, la: EF, lb: EF) -> NativeG1 {
    let gadget = LogUpGadget::new();
    let pcs = crate::b2_pcs([os_rng(), os_rng(), os_rng()]);
    let chal = lookup_challenges_f(spec, la, lb);
    let tb = &spec.tables[0];
    let inst = &ov.instances[0];
    let bo = &inst.base_opened_values;
    let tn: Vec<EF> = bo.trace_next.clone().expect("C3 opens B's main trace at zeta * g");
    let pre_local: Vec<EF> = bo.preprocessed_local().map(<[EF]>::to_vec).unwrap_or_default();
    let pre_next: Vec<EF> = bo.preprocessed_next().map(<[EF]>::to_vec).unwrap_or_else(|| vec![EF::ZERO; tb.pre_width]);
    let recompose = |flat: &[EF]| -> Vec<EF> { flat.chunks_exact(8).map(|c| <EF as ExtensionField<F>>::from_ext_basis_coefficients(c).unwrap()).collect() };
    let perm_local = recompose(&inst.permutation_local);
    let perm_next = recompose(&inst.permutation_next);
    let terminal = terminals[0].as_ref().map(|t| t.0);
    let tv: Vec<EF> = terminal.into_iter().collect();
    let init = <HPcs as Pcs<EF, Challenger>>::natural_domain_for_degree(&pcs, 1usize << tb.log_trace);
    let ext = <HPcs as Pcs<EF, Challenger>>::natural_domain_for_degree(&pcs, 1usize << (tb.log_trace + 1));
    let sels = init.selectors_at_point(zeta);
    let z_h = init.vanishing_poly_at_point(zeta);
    let lk: &[p3_lookup::Lookup<F>] = &common.lookups[0];
    let mut pb = PointBuilder {
        main: RowWindow::from_two_rows(&bo.trace_local, &tn),
        pre: RowWindow::from_two_rows(&pre_local, &pre_next),
        perm: RowWindow::from_two_rows(&perm_local, &perm_next),
        public,
        challenges: &chal[0],
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
        public_values: public,
        is_first_row: sels.is_first_row,
        is_last_row: sels.is_last_row,
        is_transition: sels.is_transition,
        alpha,
        accumulator: EF::ZERO,
    };
    let mut folder = p3_batch_stark_c3::folder::VerifierConstraintFolderWithLookups::<Config> {
        inner,
        permutation: VerticalPair::new(RowMajorMatrixView::new_row(&perm_local), RowMajorMatrixView::new_row(&perm_next)),
        permutation_challenges: &chal[0],
        permutation_values: &tv,
    };
    gadget.eval_air_and_lookups(air, &mut folder, lk);
    let folded = folder.inner.accumulator;
    let qdom = ext.try_create_disjoint_domain(1usize << (tb.log_trace + 1 + tb.log_qd)).expect("quotient domain");
    let domains = qdom.split_domains(tb.chunks);
    let zps: Vec<EF> = (0..domains.len())
        .map(|k| domains.iter().enumerate().filter(|(j, _)| *j != k).map(|(_, o)| o.vanishing_poly_at_point(zeta) * o.vanishing_poly_at_point(domains[k].first_point()).inverse()).product::<EF>())
        .collect();
    let chunk_vanishing: Vec<EF> = domains.iter().map(|d| d.vanishing_poly_at_point(zeta)).collect();
    let chunk_values: Vec<EF> = bo.quotient_chunks.iter().map(|ch| <EF as ExtensionField<F>>::from_ext_basis_coefficients(ch).unwrap()).collect();
    let quotient = p3_uni_stark::recompose_quotient_from_chunks::<Config>(&domains, &bo.quotient_chunks, zeta);
    let identity_holds = folded * sels.inv_vanishing == quotient;
    let table = NativeTable {
        trace_local: bo.trace_local.clone(),
        trace_next: tn.clone(),
        pre_local: pre_local.clone(),
        perm_local: perm_local.clone(),
        perm_next: perm_next.clone(),
        perm_local_flat: inst.permutation_local.clone(),
        perm_next_flat: inst.permutation_next.clone(),
        chunks: bo.quotient_chunks.clone(),
        public: public.to_vec(),
        challenges: chal[0].clone(),
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
    };
    let terminal_sum_zero = gadget.verify_terminal_sum(terminals).is_ok();
    NativeG1 { alpha, zeta, lookup_alpha: la, lookup_beta: lb, tables: vec![table], terminal_sum_zero }
}

/// The compile check of B's program: at random points, every constraint value, the selectors, the fold, the quotient,
/// the identity verdict and the terminal verdict equal the native functions'; the point made consistent is accepted by
/// both; a program without one LogUp constraint differs from the native fold; zeta in B's trace domain has no inverse.
pub fn b_differential(bc: &BChild, spec: &ChildSpec, points: usize, seed: u64) -> Value {
    let p = &spec.program;
    let (_, unfactored, _) = compile_b(bc, Options { factor_min: 0 }, None);
    let (_, dropped, _) = compile_b(bc, Options::default(), Some(0));
    let tb = &spec.tables[0];
    let mut rng = StdRng::seed_from_u64(seed);
    let rand_ef = |rng: &mut StdRng| EF::from_basis_coefficients_fn(|_| rng.random::<F>());
    let (mut agree, mut agree_identity, mut dropped_differs) = (0, 0, 0);
    let t = Instant::now();
    for _ in 0..points {
        let tl: Vec<EF> = (0..tb.width).map(|_| rand_ef(&mut rng)).collect();
        let tn: Vec<EF> = (0..tb.width).map(|_| rand_ef(&mut rng)).collect();
        let pre: Vec<EF> = (0..tb.pre_width).map(|_| rand_ef(&mut rng)).collect();
        let pl: Vec<EF> = (0..8 * tb.perm_width).map(|_| rand_ef(&mut rng)).collect();
        let pn: Vec<EF> = (0..8 * tb.perm_width).map(|_| rand_ef(&mut rng)).collect();
        let chunks: Vec<Vec<EF>> = (0..tb.chunks).map(|_| (0..8).map(|_| rand_ef(&mut rng)).collect()).collect();
        let terminals = vec![Some(p3_lookup::LookupTerminal(rand_ef(&mut rng)))];
        let public: Vec<F> = (0..tb.public.len()).map(|_| rng.random::<F>()).collect();
        let (alpha, zeta, la, lb) = (rand_ef(&mut rng), rand_ef(&mut rng), rand_ef(&mut rng), rand_ef(&mut rng));
        let build_ov = |ch: Vec<Vec<EF>>| p3_batch_stark_c3::BatchOpenedValues {
            instances: vec![p3_batch_stark_c3::proof::OpenedValuesWithLookups {
                base_opened_values: p3_uni_stark::OpenedValues {
                    trace_local: tl.clone(),
                    trace_next: Some(tn.clone()),
                    preprocessed: Some(p3_uni_stark::PreprocessedOpenedValues { local: pre.clone(), next: None }),
                    quotient_chunks: ch,
                    random: None,
                },
                permutation_local: pl.clone(),
                permutation_next: pn.clone(),
            }],
        };
        let nk = native_b(spec, &bc.s.air, &bc.common, &build_ov(chunks.clone()), &terminals, &public, alpha, zeta, la, lb);
        let input = |i: Input| -> EF {
            match i {
                Input::TraceLocal(_, k) => nk.tables[0].trace_local[k],
                Input::TraceNext(_, k) => nk.tables[0].trace_next[k],
                Input::PreLocal(_, k) => nk.tables[0].pre_local[k],
                Input::PreNext(..) => unreachable!("B's AIR reads no preprocessed column at the next row"),
                Input::PermLocal(_, j, k) => nk.tables[0].perm_local_flat[8 * j + k],
                Input::PermNext(_, j, k) => nk.tables[0].perm_next_flat[8 * j + k],
                Input::Public(_, k) => EF::from(nk.tables[0].public[k]),
                Input::Alpha => alpha,
                Input::Zeta => zeta,
                Input::LookupAlpha => la,
                Input::LookupBeta => lb,
                Input::Periodic(..) => panic!("periodic advice requires the aggregation binding path"),
                Input::Terminal(_) => nk.tables[0].terminal.unwrap(),
                Input::Chunk(_, c, k) => nk.tables[0].chunks[c][k],
            }
        };
        let (v, eqs) = p.eval(&input);
        let eq_of = |i: usize| eqs.iter().find(|e| e.0 == i).unwrap().1;
        let o = &p.tables[0];
        let nt = &nk.tables[0];
        let got = |id: usize| v[id].expect("value");
        assert_eq!([got(o.is_first_row), got(o.is_last_row), got(o.is_transition), got(o.inv_vanishing)], nt.sels, "B: selectors");
        assert_eq!(o.constraints.len(), nt.constraints.len(), "B: constraint count");
        for (k, cv) in o.constraints.iter().enumerate() {
            let val = match cv.expect("every constraint compiled") {
                CVal::Plain(id) => got(id),
                CVal::Factored(sl, id) => {
                    let s = match sl {
                        Sel::First => nt.sels[0],
                        Sel::Last => nt.sels[1],
                        Sel::Transition => nt.sels[2],
                    };
                    s * got(id)
                }
            };
            assert_eq!(val, nt.constraints[k], "B constraint {k}");
        }
        assert_eq!(got(o.folded), nt.folded, "B: folded");
        assert_eq!(got(o.quotient), nt.quotient, "B: quotient");
        assert_eq!(eq_of(o.identity), nt.identity_holds, "B: identity verdict");
        let (vu, _) = unfactored.eval(&input);
        assert_eq!(vu[unfactored.tables[0].folded].unwrap(), nt.folded, "B: the unfactored program's fold");
        assert_eq!(eq_of(p.terminal_check), nk.terminal_sum_zero, "terminal-sum verdict");
        let (vd, _) = dropped.eval(&input);
        if vd[dropped.tables[0].folded].unwrap() != nt.folded {
            dropped_differs += 1;
        }
        agree += 1;
        // The same point made consistent: chunk 0 coordinate 0 chosen so that B's identity holds.
        let target = nt.folded * nt.sels[3];
        let rest: EF = (1..nt.chunk_values.len()).map(|c| nt.zps[c] * nt.chunk_values[c]).sum();
        let q0 = (target - rest) * nt.zps[0].inverse();
        let x = EF::from_basis_coefficients_fn(|k| if k == 1 { F::ONE } else { F::ZERO });
        let others: EF = (1..8).map(|k| x.exp_u64(k as u64) * nt.chunks[0][k]).sum();
        let mut ch2 = chunks.clone();
        ch2[0][0] = q0 - others;
        let nk2 = native_b(spec, &bc.s.air, &bc.common, &build_ov(ch2), &terminals, &public, alpha, zeta, la, lb);
        assert!(nk2.tables[0].identity_holds, "the adjusted point satisfies B's identity natively");
        let input2 = |i: Input| -> EF {
            match i {
                Input::Chunk(_, c, k) => nk2.tables[0].chunks[c][k],
                other => input(other),
            }
        };
        let (_, eqs2) = p.eval(&input2);
        assert!(eqs2.iter().find(|e| e.0 == o.identity).unwrap().1, "the program accepts the adjusted point");
        agree_identity += 1;
    }
    let diff_ms = ms(t);
    // zeta in B's trace domain: the native vanishing value is zero and the program's inverse of Z_H has no value.
    let mut in_domain = vec![];
    for e in [0u64, 3] {
        let w = <F as p3_field::TwoAdicField>::two_adic_generator(tb.log_trace).exp_u64(e);
        let zeta = EF::from(w);
        let init = p3_field::coset::TwoAdicMultiplicativeCoset::new(F::ONE, tb.log_trace).unwrap();
        let zero = init.vanishing_poly_at_point(zeta).is_zero();
        let input = |i: Input| -> EF {
            match i {
                Input::Zeta => zeta,
                _ => EF::from_basis_coefficients_fn(|k| F::from_u32(1 + k as u32)),
            }
        };
        let (v, _) = p.eval(&input);
        assert!(zero && v[p.tables[0].inv_vanishing].is_none(), "zeta = w^{e} in H: Z_H = 0 natively and no inverse in the program");
        in_domain.push(json!({"zeta": format!("w^{e}"), "native_vanishing_is_zero": zero, "program_inverse_of_z_h": Value::Null}));
    }
    json!({"points": points, "seed": format!("{seed:#x}"),
        "selectors_constraints_folded_quotient_identity_and_terminal_verdict_equal_native": agree,
        "consistent_points_accepted_by_both": agree_identity, "unfactored_program_folds_equal_native": agree,
        "dropped_lookup_constraint": {"extension_constraint": 0, "instructions": dropped.instrs.len(), "folds_differing_from_native": dropped_differs},
        "unfactored_instructions": unfactored.instrs.len(),
        "native_functions": "selectors_at_point (p3-commit), B's AIR's own eval through the LogUp gadget (PointBuilder) for every constraint, VerifierConstraintFolderWithLookups (p3_batch_stark_c3 folder.rs, p3-lookup), recompose_quotient_from_chunks (p3-uni-stark), verify_terminal_sum (p3-lookup)",
        "zeta_in_h": in_domain, "ms": diff_ms})
}

/// B's key's common data for the recording configuration (the same values; the configuration type differs).
fn recast_common_b(c: &KCommon) -> p3_batch_stark_c3::CommonData<replay::RecConfig> {
    let pre = c.preprocessed.as_ref().map(|g| p3_batch_stark_c3::common::GlobalPreprocessed::<replay::RecConfig> {
        commitment: g.commitment.clone(),
        instances: g.instances.clone(),
        matrix_to_instance: g.matrix_to_instance.clone(),
    });
    p3_batch_stark_c3::CommonData::new(pre, c.lookups.clone())
}

/// B's proof's claimed values per (input round, matrix, point) as the PCS absorbs them: C3's own
/// `commitments_with_opening_points` (verifier/mod.rs l. 107-345) with the hiding PCS's random-codeword values appended.
fn claims_b(bc: &BChild, proof: &KProof, zeta: EF, lqd: usize) -> Claims {
    let cfg = crate::b2_config(&bc.vk, &bc.statement);
    let (rounds, _, _) = p3_batch_stark_c3::verifier::commitments_with_opening_points(&cfg, std::slice::from_ref(&bc.s.air), zeta, &proof.commitments,
        &proof.opened_values, &bc.common, &proof.degree_bits, &[bc.s.air.pre.len()], &[lqd])
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

fn ef_flat(out: &mut Vec<F>, values: impl Iterator<Item = EF>) {
    for v in values {
        out.extend_from_slice(v.as_basis_coefficients_slice());
    }
}
fn cap_flat(out: &mut Vec<F>, cap: &crate::Cap) {
    for d in cap.roots() {
        out.extend_from_slice(d);
    }
}

/// B's proof's witness stream in F's schedule's order (the events' witness segments).
fn witness_stream_b(fs: &fschedule::Schedule, proof: &KProof, claims: &Claims) -> Vec<F> {
    let mut wit = vec![];
    let fri = &proof.opening_proof.1;
    let input_trees: Vec<usize> = (0..fs.trees.len()).filter(|&t| matches!(fs.trees[t].kind, fschedule::TreeKind::Input(_))).collect();
    for (name, first, len) in &fs.wit_segments {
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
            let ti = fs.trees.iter().position(|t| t.name == parts[0]).unwrap();
            let round = input_trees.iter().position(|&x| x == ti).unwrap();
            let m: usize = parts[1][1..].parse().unwrap();
            let pt_name = parts[2..].join(".");
            let p = fs.trees[ti].mats[m].points.iter().position(|&pp| fschedule::pt_name(pp) == pt_name).unwrap();
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
    assert_eq!(wit.len(), fs.wit_len);
    wit
}

pub type RecBProof = p3_batch_stark_c3::BatchProof<replay::RecConfig>;

/// Run B's native verifier (p3_batch_stark_c3::verify_batch with recording wrappers) on B's proof and collect what F's
/// trace generator needs: the duplexings, the multi-openings with their caps and restored paths, the witness stream,
/// p3-fri's own reduced openings per height and the native values of B's identity and of the terminal check. `expect`
/// is the native verdict the child must get: "accepted", or the error it must be rejected with.
pub fn replay_b(bc: &BChild, fs: &fschedule::Schedule, bytes: &[u8], pv: &[F], expect: &str) -> (ChildData, Value) {
    let (proof, rest) = postcard::take_from_bytes::<RecBProof>(bytes).expect("decode B's proof");
    assert!(rest.is_empty(), "trailing bytes");
    let decoded: KProof = crate::decode_strict(bytes);
    assert_eq!(decoded.degree_bits, vec![bc.s.log_n + 1], "B's proof's degree bits differ from B's shape");
    let prefix = fschedule::prefix_elements(&fs.child.prefix, pv);
    // B2's recording configuration: its MMCS has the child cap height CAP_HEIGHT, which is B's (K_CAP_HEIGHT).
    assert_eq!(CAP_HEIGHT, K_CAP_HEIGHT, "the recording MMCS's cap height is B's");
    let (cfg, rec) = replay::rec_config((K_LOG_BLOWUP, K_LOG_FINAL_POLY_LEN, K_MAX_LOG_ARITY, K_QUERIES), RANDOM_CODEWORDS, &prefix, None);
    let rec_common = recast_common_b(&bc.common);
    let t = Instant::now();
    let verdict = p3_batch_stark_c3::verify_batch(&cfg, std::slice::from_ref(&bc.s.air), &proof, &[pv.to_vec()], &rec_common);
    let native_ms = ms(t);
    let native_verdict = format!("{verdict:?}");
    match expect {
        "accepted" => assert!(verdict.is_ok(), "B's native verifier rejected B's proof: {verdict:?}"),
        e => assert!(native_verdict.contains(e), "B's proof must be rejected with {e}: {verdict:?}"),
    }
    let perm_log = rec.perms.lock().unwrap().clone();
    let calls = rec.mmcs.lock().unwrap().clone();
    assert_eq!(pv.len(), fs.num_public);
    let out_ef = |row: usize| -> EF { to_ef(&core::array::from_fn(|k| perm_log[row].1[7 - k])) };
    let (alpha, zeta, pcs_alpha, la, lb) = (out_ef(fs.alpha_row), out_ef(fs.zeta_row), out_ef(fs.pcs_alpha_row), out_ef(fs.lookup_alpha_row), out_ef(fs.lookup_beta_row));
    let lqd = fs.child.tables[0].log_qd;
    let claims = claims_b(bc, &decoded, zeta, lqd);
    let wit = witness_stream_b(fs, &decoded, &claims);
    let pre_cap = bc.key.commitment.roots().to_vec();
    let mut tree_caps: Vec<Vec<[F; 8]>> = vec![];
    for t in &fs.trees {
        let cap: Vec<[F; 8]> = match t.kind {
            fschedule::TreeKind::Input(0) => decoded.commitments.main.roots().to_vec(),
            fschedule::TreeKind::Input(1) => decoded.commitments.quotient_chunks.roots().to_vec(),
            fschedule::TreeKind::Input(2) => pre_cap.clone(),
            fschedule::TreeKind::Input(3) => decoded.commitments.permutation.as_ref().unwrap().roots().to_vec(),
            fschedule::TreeKind::Fri(r) => decoded.opening_proof.1.commit_phase_commits[r].roots().to_vec(),
            fschedule::TreeKind::Input(_) => unreachable!(),
        };
        tree_caps.push(cap);
    }
    let (mut leaves, mut sibs, mut idx, mut summary) = (vec![], vec![], vec![], vec![]);
    for (ti, cap) in tree_caps.iter().enumerate() {
        let t = &fs.trees[ti];
        let found: Vec<&replay::MmcsCall> = calls.iter().filter(|c| &c.cap == cap).collect();
        assert_eq!(found.len(), 1, "tree {}: expected one native multi-opening", t.name);
        let call = found[0];
        if expect == "accepted" {
            assert!(call.accepted, "tree {}: the native multi-opening was rejected", t.name);
        }
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
            "distinct_indices": call.indices.iter().collect::<BTreeSet<_>>().len(),
            "pruned_sibling_digests": call.pruned.sibling_hashes.len(), "walked_levels": t.mc, "cap_entries": cap.len(), "accepted": call.accepted}));
    }
    assert_eq!(calls.len(), fs.trees.len(), "unexpected extra multi-openings");
    // p3-fri's own reduced openings per height (open_inputs, verifier.rs l. 1093-1418), under B's FRI parameters.
    let perm = default_koalabear_poseidon2_16();
    let mmcs = Mmcs::new(Hash::new(perm.clone()), Compress::new(perm), K_CAP_HEIGHT, os_rng());
    let global_idx: Vec<usize> = idx[fs.canon()].clone();
    let t = Instant::now();
    let ro = p3_fri::verifier::open_inputs::<F, EF, Mmcs, ChMmcs>(&b_fri_params(os_rng()), fs.child.index_bits, &global_idx,
        &decoded.opening_proof.1.input_openings, pcs_alpha, &mmcs, &claims).expect("p3-fri open_inputs on B's proof");
    let open_inputs_ms = ms(t);
    let native_ro: Vec<BTreeMap<usize, EF>> = ro.into_iter().map(|v| v.into_iter().collect()).collect();
    let t = Instant::now();
    let native = native_b(&fs.child, &bc.s.air, &bc.common, &decoded.opened_values, &decoded.lookup_terminals, pv, alpha, zeta, la, lb);
    let identity_ms = ms(t);
    let init = [F::ZERO; 16];
    let report = json!({"child_proof_sha256": sha256_hex(bytes), "child_proof_bytes": bytes.len(),
        "native_verifier": "p3_batch_stark_c3::verify_batch (C3b's copy, unchanged) with B2's recording wrappers (RecPerm, RecMmcs), B's pinned key and B's prefix",
        "native_verdict_of_the_replay": native_verdict, "expected": expect,
        "native_verify_ms": native_ms, "native_duplexings_recorded": perm_log.len(),
        "preprocessed_cap_is_the_pinned_one": pre_cap == fs.child.pre_cap,
        "native_multi_openings": summary, "child_vk_digest": hex(&fs.child.child_vk),
        "native_reduced_openings": {"function": "p3_fri::verifier::open_inputs (verifier.rs l. 1093-1418) on B's proof, per height",
            "queries": native_ro.len(), "heights": native_ro[0].keys().collect::<Vec<_>>(), "ms": open_inputs_ms},
        "native_identities": {"tables": native.tables.iter().map(|t| json!({"identity_holds": t.identity_holds, "constraints": t.constraints.len()})).collect::<Vec<_>>(),
            "terminal_sum_zero": native.terminal_sum_zero, "ms": identity_ms},
        "peak_rss_kib": peak_rss_kib()});
    (ChildData { pv: pv.to_vec(), wit, pre_cap, leaves, sibs, idx, caps: tree_caps, perm_log, init, native_ro, native }, report)
}
