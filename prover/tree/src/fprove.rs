//! F2 (L5 layer F2, 2026-11-01): F's proof, its verification and its controls, and the controls of changes (a) and (d).
//!
//! - `f-prove`: F's honest trace for B's accepted proof (variant `P`), or a trace-level negative of F (F1's variants
//!   A, B, C, claim_write) or the honest generation from a natively invalid B (`corpus_b_invalid`), proven by F's
//!   prover (p3_batch_stark_c3np with F's opened next-row sets, F's PCS with salts from a seed, fresh operating-system
//!   randomness for this attempt) after F's key is recomputed and checked against F's pinned `f-vk.json`; the proof is
//!   encoded, stored, decoded strictly and verified in this process by F's verifier; its exact byte breakdown
//!   (`fbreakdown.rs`) is recorded. The prover never checks constraints (a release build), so a negative's proof is made
//!   and must be rejected by F's verifier.
//! - `f-verify`: a fresh process rebuilds B's identity, F's schedule and F's key, compares them with F's pinned
//!   `f-vk.json`, decodes the proof strictly and verifies it with the statement (timed; run with 24 threads and with 1).
//! - `f-proof-controls`: verify-only controls on the accepted proof (the statement, F's verifier-key digest, the
//!   next-row sets as derived instead of as opened, another schedule with its own digest, F's domain).
//! - `f-degree` (change (a)): the pinned prover's quotient chunk count and LogUp packing budget by maximum constraint
//!   degree, with and without zero knowledge, from the library's own functions on small AIRs, and F's own degrees.
//! - `f-salts` (change (d)): the PRG-salt MMCS against the pinned hiding MMCS: the salts are ChaCha20(seed, stream =
//!   row) samples of the pinned sampler, the commitment equals the pinned tree over the same salts, openings verify
//!   under both crates, fresh seeds per attempt, the salts' empirical distribution, and the resident-set effect.
//! Research measurement; loop-internal self-review; not independently reviewed.
use crate::memory_io as fs;
use std::path::Path;
use std::time::Instant;

use p3_air::symbolic::AirLayout;
use p3_air::{Air, BaseAir, WindowAccess};
use p3_batch_stark_c3np::{NextRowColumns, OmittedFill, StarkInstance};
use p3_commit::{BatchOpeningRef, Mmcs as _};
use p3_field::{Field, PrimeCharacteristicRing, PrimeField32};
use p3_koala_bear::{KoalaBear as F, default_koalabear_poseidon2_16};
use p3_lookup::{Count, InteractionBuilder, LogUpGadget, LookupBus, LookupProtocol};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::stack::HorizontalPair;
use p3_matrix::Dimensions;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use serde_json::{Value, json};
use sha2::{Digest as _, Sha256};

use crate::fmodes::{self, b_proof, check_f_vk, f_config, f_identity, f_vk_json, fcheck_report};
use crate::fschedule::Schedule;
use crate::{
    Compress, EF, FCommon, FMmcs, FProof, Hash, Mmcs, REVIEW, TIER, event, fbreakdown, fchild, ftracegen, fvariants, hex, mem_available_kib, ms,
    os_rng, peak_rss_kib, pv_json, read_json, save, sha256_hex,
};

/// Strict decoding of F's proof: the whole input, nothing left over.
pub fn decode_strict_f(bytes: &[u8]) -> FProof {
    let (proof, rest) = postcard::take_from_bytes::<FProof>(bytes).expect("decode F's proof");
    assert!(rest.is_empty(), "trailing bytes");
    proof
}

/// F's verifier: the proof against F's verifier-key digest (F's challenger prefix), F's key (the packed lookups) and
/// F's opened next-row sets; omitted next-row entries are zero (C3n's verifier). Returns (accepted, error, ms).
pub fn verify_f(s: &Schedule, vk: &[u8; 32], common: &FCommon, opened: &NextRowColumns, proof: &FProof, pv: &[F]) -> (bool, Option<String>, f64) {
    let t = Instant::now();
    let cfg = f_config(vk, pv);
    let r = p3_batch_stark_c3np::verify_batch_with_next_row_columns(&cfg, std::slice::from_ref(&s.air), proof, &[pv.to_vec()], common,
        std::slice::from_ref(opened), OmittedFill::Zero);
    (r.is_ok(), r.err().map(|e| format!("{e:?}")), ms(t))
}

/// F's identity, recomputed and checked against F's pinned key record.
fn f_identity_checked(s: &Schedule, f_vk_path: &Path) -> (FCommon, (NextRowColumns, NextRowColumns), [u8; 32], Value) {
    let (cm, next, _rule, vk) = f_identity(s);
    let check = check_f_vk(&f_vk_json(s, &cm, &next, &vk), &read_json(f_vk_path));
    (cm, next, vk, check)
}

fn trace_sha256(trace: &RowMajorMatrix<F>) -> String {
    let mut h = Sha256::new();
    for v in &trace.values {
        h.update(v.as_canonical_u32().to_le_bytes());
    }
    hex(&h.finalize())
}

/// `f-prove`: one proof of F (see the module documentation).
pub fn f_prove_mode(variant: &str, in_dir: &Path, b_vk: &Path, b_dir: &Path, child_dir: Option<&Path>, f_vk_path: &Path, out: &Path) {
    fs::create_dir(out).expect("fresh output directory required");
    ftracegen::ef_selftest();
    let exp = fvariants::expected(variant);
    let t0 = Instant::now();
    let bc = fchild::b_child(in_dir, b_vk);
    let spec = fchild::b_spec(&bc);
    let s = Schedule::build(&spec);
    let schedule_ms = ms(t0);
    let t = Instant::now();
    let (common, next, vk, vk_check) = f_identity_checked(&s, f_vk_path);
    assert_eq!(vk_check["all_equal"], json!(true), "F's recomputed key differs from F's pinned f-vk.json: {vk_check}");
    let identity_ms = ms(t);
    let dir = child_dir.unwrap_or(b_dir);
    assert_eq!(exp.child_level, child_dir.is_some(), "a child-level variant names its child; the others use B's accepted proof");
    let (brun, bytes, pv0) = if crate::memory_io::is_memory(dir) {
        crate::pipeline::b_proof_memory(dir, &bc)
    } else { b_proof(dir, &bc) };
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
    let trace = if variant == "P" || exp.child_level {
        honest_trace
    } else {
        drop(honest_trace);
        kt.finalize()
    };
    drop(kt);
    let (_, this_check, names, roles) = fcheck_report(&s, &trace, &pv);
    let targeted = fvariants::target_met(&exp, &names, &roles);
    let tracegen_ms = ms(t);
    let trace_sha = trace_sha256(&trace);
    let statement_is_b = pv == bc.statement;
    // Everything of B is dropped before F's prover runs (the model's process base: F's schedule and trace held).
    drop(cd);
    drop(bc);
    drop(spec);
    let rss_before_prove = fmodes::rss_now_kib();
    let hwm_before_prove = peak_rss_kib();
    let t = Instant::now();
    let data = fmodes::f_data(&s);
    let keygen_ms = ms(t);
    let cfg = f_config(&vk, &pv);
    let mem_before = mem_available_kib();
    let t = Instant::now();
    let airs = [s.air.clone()];
    let traces = [&trace];
    let instances = StarkInstance::new_multiple(&airs, &traces, &[pv.clone()]);
    let proof = p3_batch_stark_c3np::prove_batch_with_next_row_columns(&cfg, &instances, &data, std::slice::from_ref(&next.1)).expect("F's prover");
    let prove_ms = ms(t);
    let rss_after = peak_rss_kib();
    drop(instances);
    drop(data);
    let encoded = postcard::to_allocvec(&proof).unwrap();
    drop(proof);
    save(&out.join("proof.postcard"), &encoded);
    let decoded = decode_strict_f(&encoded);
    let (accepted, error, verify_ms) = verify_f(&s, &vk, &common, &next.1, &decoded, &pv);
    let (bd, bd_errors) = fbreakdown::report(&encoded, &decoded, &fbreakdown::FShape::of(&s, &next.1, &common));
    save(&out.join("breakdown.json"), &serde_json::to_vec_pretty(&bd).unwrap());
    let statement = json!({"schema": crate::SCHEMA, "variant": variant, "public_values": pv_json(&pv),
        "public_values_sha256": sha256_hex(&pv.iter().flat_map(|v| v.as_canonical_u32().to_le_bytes()).collect::<Vec<u8>>()),
        "f_vk_digest": hex(&vk), "b_vk_digest": hex(&s.child.child_vk), "compiled_program_sha256": hex(&s.child.program_sha256),
        "statement_is_b_statement_l0p2_pi198": statement_is_b});
    save(&out.join("statement.json"), &serde_json::to_vec_pretty(&statement).unwrap());
    let terminal_zero = decoded.lookup_terminals.iter().flatten().all(|x| x.0 == EF::ZERO);
    let as_expected = accepted == (exp.expect == "accept") && targeted && bd_errors.is_empty();
    let report = json!({"schema": crate::SCHEMA, "review": REVIEW, "tier": TIER, "n": 1, "variant": variant,
        "expected": exp.expect, "targeted_constraint_group": exp.target, "expected_exact_violations": exp.exact, "expected_alu_roles": exp.roles,
        "edit": edit, "b_proof": brun,
        "native_row_check": {"constraints_per_row": constraints, "rows": s.n,
            "honest_generation_violations": honest_names, "honest_generation_check": if honest_names.is_empty() { Value::Null } else { honest_check },
            "this_trace": this_check, "targeted_group_violated": targeted},
        "proved_trace_sha256_u32le_row_major": trace_sha, "lookup_terminal_is_zero": terminal_zero,
        "in_process": {"accepted": accepted, "error": error, "as_expected": accepted == (exp.expect == "accept")},
        "as_expected": as_expected,
        "proof_bytes": encoded.len(), "proof_sha256": sha256_hex(&encoded), "against_max_proof_bytes_196608": 196_608i64 - encoded.len() as i64,
        "f_vk_digest": hex(&vk), "f_key_recomputed_against_f_vk_json": vk_check,
        "next_row_opened": {"main": next.1.main.len(), "main_split": next.1.main_split().is_split(), "permutation_ef8": next.1.permutation.len(),
            "permutation_split": next.1.permutation_split(8).is_split()},
        "breakdown_summary": bd["summary"], "breakdown_all_checks_passed": bd["all_checks_passed"], "breakdown_errors": bd_errors,
        "replay": replay_report, "honest_generation": honest_report,
        "timings_ms": {"b_child_and_f_schedule": schedule_ms, "f_identity": identity_ms, "replay_trace_variant_and_checks": tracegen_ms,
            "f_keygen": keygen_ms, "prove": prove_ms, "verify_in_process": verify_ms},
        "mem_available_kib_before_prove": mem_before, "rss_kib_before_prove": rss_before_prove, "peak_rss_kib_before_prove": hwm_before_prove,
        "peak_rss_kib_after_prove": rss_after, "rayon_threads": std::env::var("RAYON_NUM_THREADS").ok(), "f_proof_parameters": fmodes::f_params()});
    save(&out.join("report.json"), &serde_json::to_vec_pretty(&report).unwrap());
    event(json!({"phase": "f_prove_done", "variant": variant, "accepted_in_process": accepted, "error": report["in_process"]["error"],
        "violated": names, "roles": roles, "lookup_terminal_is_zero": terminal_zero, "proof_bytes": encoded.len(), "prove_ms": prove_ms,
        "peak_rss_kib": rss_after, "breakdown_ok": bd_errors.is_empty(), "as_expected": as_expected}));
    if !as_expected {
        std::process::exit(3);
    }
}

/// `f-verify`: a fresh process verifies a proof of F (see the module documentation).
pub fn f_verify_mode(in_dir: &Path, b_vk: &Path, f_vk_path: &Path, dir: &Path, out: &Path) {
    assert!(!out.exists(), "refusing to overwrite {}", out.display());
    let t = Instant::now();
    let bc = fchild::b_child(in_dir, b_vk);
    let spec = fchild::b_spec(&bc);
    let s = Schedule::build(&spec);
    let schedule_ms = ms(t);
    let t = Instant::now();
    let (common, next, vk, vk_check) = f_identity_checked(&s, f_vk_path);
    let identity_ms = ms(t);
    let st = read_json(&dir.join("statement.json"));
    let pv = crate::pv_from_json(&st["public_values"]);
    let bytes = fs::read(dir.join("proof.postcard")).unwrap();
    let t = Instant::now();
    let proof = decode_strict_f(&bytes);
    let decode_ms = ms(t);
    let (accepted, error, verify_ms) = verify_f(&s, &vk, &common, &next.1, &proof, &pv);
    let key_ok = vk_check["all_equal"] == json!(true);
    let statement_ok = st["f_vk_digest"].as_str() == Some(hex(&vk).as_str()) && st["b_vk_digest"].as_str() == Some(hex(&s.child.child_vk).as_str())
        && pv.len() == s.num_public;
    let statement_is_b = pv == bc.statement;
    let doc = json!({"schema": crate::SCHEMA, "review": REVIEW, "phase": "fresh_process_verify_f", "variant": st["variant"],
        "f_key_recomputed_against_f_vk_json": vk_check, "statement_names_this_verifier_and_b": statement_ok,
        "statement_is_l0p2_pi198": statement_is_b,
        "stark_verifier_accepted": accepted, "stark_verifier_error": error,
        "verdict": if accepted && key_ok && statement_ok { "ACCEPTED" } else { "REJECTED" },
        "proof_bytes": bytes.len(), "proof_sha256": sha256_hex(&bytes), "f_vk_digest": hex(&vk),
        "timings_ms": {"b_child_key_compile_schedule": schedule_ms, "f_key_next_rows_digest": identity_ms, "decode": decode_ms, "verify": verify_ms},
        "peak_rss_kib": peak_rss_kib(), "rayon_threads": std::env::var("RAYON_NUM_THREADS").ok()});
    save(out, &serde_json::to_vec_pretty(&doc).unwrap());
    event(doc);
}

/// `f-proof-controls`: verify-only controls on the accepted positive control's proof of F.
pub fn f_proof_controls_mode(in_dir: &Path, b_vk: &Path, f_vk_path: &Path, dir: &Path, out: &Path) {
    assert!(!out.exists(), "refusing to overwrite {}", out.display());
    let bc = fchild::b_child(in_dir, b_vk);
    let spec = fchild::b_spec(&bc);
    let s = Schedule::build(&spec);
    let (common, next, vk, vk_check) = f_identity_checked(&s, f_vk_path);
    assert_eq!(vk_check["all_equal"], json!(true));
    let st = read_json(&dir.join("statement.json"));
    assert_eq!(st["variant"], "P", "controls run on the accepted positive-control proof");
    let pv = crate::pv_from_json(&st["public_values"]);
    let bytes = fs::read(dir.join("proof.postcard")).unwrap();
    let proof = decode_strict_f(&bytes);
    let mut rows = vec![];
    let mut record = |case: &str, what: &str, expect_accept: bool, r: (bool, Option<String>, f64)| {
        let row = json!({"case": case, "what": what, "expected": if expect_accept {"accept"} else {"reject"},
            "accepted": r.0, "error": r.1, "verify_ms": r.2, "as_expected": r.0 == expect_accept});
        event(json!({"phase": "f_proof_control", "control": row}));
        rows.push(row);
    };
    record("honest", "the positive-control proof and statement under F's honest key", true, verify_f(&s, &vk, &common, &next.1, &proof, &pv));
    let mut p2 = pv.clone();
    p2[3] = F::from_u8((pv[3].as_canonical_u32() as u8) ^ 1);
    record("statement_public_value_3_flipped", "the honest proof; the statement's public value 3 (PI_bytes byte 3) with bit 0 flipped", false, verify_f(&s, &vk, &common, &next.1, &proof, &p2));
    let mut wrong_vk = vk;
    wrong_vk[0] ^= 1;
    record("f_vk_digest_bit_flipped", "the honest proof against F's verifier-key digest with one bit flipped (F's challenger prefix)", false, verify_f(&s, &wrong_vk, &common, &next.1, &proof, &pv));
    record("next_row_sets_as_derived", "a verifier opening the next-row sets as C3nP derives them (the permutation trace split), not as F opens them (the break-even rule)", false,
        verify_f(&s, &vk, &common, &next.0, &proof, &pv));
    let mut main_short = next.1.clone();
    main_short.main.pop();
    record("next_row_main_set_without_its_last_column", "a verifier whose opened main next-row set lacks its last column (the AIR reads it at the next row)", false,
        verify_f(&s, &vk, &common, &main_short, &proof, &pv));
    // Another schedule (one fold butterfly as a product), with its own identity.
    let target = s.program.iter().position(|i| i.role == "fri.fold" && i.query == Some(5) && i.round == Some(1)).unwrap();
    let mut bad = crate::fschedule::Schedule::build_with(&spec, true, s.log_n).expect("the same height");
    let (bf, mu) = (bad.air.pidx.op[2], bad.air.pidx.op[0]);
    let row = s.instr_row[target];
    bad.air.periodic[bf][row] = F::ZERO;
    bad.air.periodic[mu][row] = F::ONE;
    let (bcm, bnext, _, bvk) = f_identity(&bad);
    record("schedule_opcode_changed_own_digest", "a verifier whose schedule computes one fold butterfly of B's FRI (query 5, round 1) as a product, with its own F verifier-key digest", false,
        verify_f(&bad, &bvk, &bcm, &bnext.1, &proof, &pv));
    record("schedule_opcode_changed_honest_digest", "the same changed schedule under the honest F verifier-key digest", false,
        verify_f(&bad, &vk, &bcm, &bnext.1, &proof, &pv));
    let all = rows.iter().all(|r| r["as_expected"].as_bool().unwrap());
    let doc = json!({"schema": crate::SCHEMA, "review": REVIEW, "tier": TIER, "proof_sha256": sha256_hex(&bytes), "f_vk_digest": hex(&vk),
        "all_as_expected": all, "controls": rows, "peak_rss_kib": peak_rss_kib()});
    save(out, &serde_json::to_vec_pretty(&doc).unwrap());
    if !all {
        std::process::exit(3);
    }
}

// ---------- (a) quotient degree ----------

/// A one-column AIR of a given maximum degree: `x^d = 0` on every row, optionally a periodic factor, optionally one
/// lookup on a named bus (an entry and a read of the same message).
#[derive(Clone)]
struct DegAir {
    d: usize,
    periodic: Option<Vec<F>>,
    lookup_tuples: usize,
}
impl BaseAir<F> for DegAir {
    fn width(&self) -> usize {
        2
    }
    fn num_periodic_columns(&self) -> usize {
        usize::from(self.periodic.is_some())
    }
    fn periodic_columns(&self) -> std::borrow::Cow<'_, [Vec<F>]> {
        std::borrow::Cow::Owned(self.periodic.iter().cloned().collect())
    }
}
impl<AB: InteractionBuilder<F = F>> Air<AB> for DegAir {
    fn eval(&self, b: &mut AB) {
        let main = b.main();
        let x: AB::Expr = main.current(0).unwrap().into();
        let y: AB::Expr = main.current(1).unwrap().into();
        let per: Vec<AB::Expr> = b.periodic_values().iter().map(|&v| v.into()).collect();
        let mut e = if per.is_empty() { x.clone() } else { per[0].clone() };
        for _ in 1..self.d {
            e = e * x.clone();
        }
        b.assert_zero(e);
        let bus = LookupBus::new("deg");
        for _ in 0..self.lookup_tuples {
            bus.lookup_key(b, vec![x.clone(), y.clone()], Count::bounded(y.clone(), 1));
        }
    }
}

/// `f-degree`: change (a). The chunk count and the packing budget the pinned C3nP functions give by degree; F's degrees.
pub fn f_degree_mode(in_dir: &Path, b_vk: &Path, out: &Path) {
    fs::create_dir(out).expect("fresh output directory required");
    let n = 1usize << 14;
    let gadget = LogUpGadget::new();
    let mut rows = vec![];
    for d in 2..=6 {
        for periodic in [false, true] {
            let air = DegAir { d, periodic: periodic.then(|| (0..n).map(|i| F::from_usize(i % 7)).collect()), lookup_tuples: 0 };
            let layout = AirLayout::from_air(&air);
            let deg = p3_batch_stark_c3np::symbolic::get_max_constraint_degree::<F, EF, _, _>(&air, layout, n, &[], &gadget);
            let lc0 = p3_batch_stark_c3np::symbolic::get_log_num_quotient_chunks::<F, EF, _, _>(&air, layout, n, &[], 0, &gadget);
            let lc1 = p3_batch_stark_c3np::symbolic::get_log_num_quotient_chunks::<F, EF, _, _>(&air, layout, n, &[], 1, &gadget);
            rows.push(json!({"max_degree": d, "periodic_factor": periodic, "degree_by_library": deg,
                "chunks_without_zk": 1usize << lc0, "chunks_with_zk": 1usize << (lc1 + 1),
                "logup_packing_budget_with_zk": (1usize << lc1) + 1 - 1, "logup_packing_budget_without_zk": (1usize << lc0) + 1}));
        }
    }
    // F's own degrees: base constraints only, with the packed lookups; the groups at the maximum.
    let bc = fchild::b_child(in_dir, b_vk);
    let spec = fchild::b_spec(&bc);
    let s = Schedule::build(&spec);
    let (cm, _, _, vk) = f_identity(&s);
    let lookups: &[p3_lookup::Lookup<F>] = &cm.lookups[0];
    let layout = AirLayout::from_air(&s.air);
    let (base0, _) = p3_batch_stark_c3np::symbolic::get_symbolic_constraints::<F, EF, _, _>(&s.air, layout, &[], &gadget);
    let tags = crate::fkernel::constraint_tags(&s.air, s.num_public);
    let mut at_max: std::collections::BTreeMap<&str, usize> = Default::default();
    let base_max = base0.iter().map(|c| c.degree_multiple()).max().unwrap();
    for (t, c) in tags.iter().zip(&base0) {
        if c.degree_multiple() == base_max {
            *at_max.entry(t).or_default() += 1;
        }
    }
    let with_lookups = p3_batch_stark_c3np::symbolic::get_max_constraint_degree::<F, EF, _, _>(&s.air, layout, s.n, lookups, &gadget);
    let lc = p3_batch_stark_c3np::symbolic::get_log_num_quotient_chunks::<F, EF, _, _>(&s.air, layout, s.n, lookups, 1, &gadget);
    let pins: Vec<Value> = lookups.iter().map(|l| json!({"column": l.column, "tuples": l.elements.len(), "fraction_pin_degree": gadget.constraint_degree(l)})).collect();
    let doc = json!({"schema": crate::SCHEMA, "review": REVIEW, "tier": TIER,
        "what": "change (a), quotient degree 3: the pinned prover's quotient chunk count and LogUp packing budget by maximum constraint degree, from p3_batch_stark_c3np's own symbolic functions on one-column AIRs (x^d = 0, with and without a periodic factor), and F's own degrees",
        "rule_in_the_pinned_sources": "symbolic.rs get_log_num_quotient_chunks: log2_ceil((d + is_zk).max(2) - 1); prover.rs: n_chunks = 2^(log_chunks + is_zk); common.rs: packing budget 2^log_chunks + 1 - is_zk",
        "by_degree": rows,
        "f": {"f_vk_digest": hex(&vk), "max_degree_base_constraints": base_max, "base_groups_at_the_maximum": at_max,
            "max_degree_with_lookups": with_lookups, "chunks_with_zk": 1usize << (lc + 1), "packing_budget": (1usize << lc), "fraction_pins": pins},
        "reading": "with zero knowledge, maximum degree 3 and 4 both give log_chunks 2: 8 committed chunks and a packing budget of 4 (fraction pins of 3 tuples stay at degree 4); 4 chunks need maximum degree 2, which F's Poseidon2Air (x^3 S-box: degree 3 with or without registers) cannot reach. So restructuring F to degree 3 (at least 32 more main columns for the DEEP lane's powers) would cost bytes and memory and save neither: not applied.",
        "peak_rss_kib": peak_rss_kib()});
    save(&out.join("degree.json"), &serde_json::to_vec_pretty(&doc).unwrap());
    event(json!({"phase": "f_degree_done", "f_max_degree": with_lookups, "f_chunks": 1usize << (lc + 1),
        "chunks_with_zk_by_degree": rows.iter().filter(|r| r["periodic_factor"] == json!(false)).map(|r| (r["max_degree"].clone(), r["chunks_with_zk"].clone())).collect::<Vec<_>>()}));
}

// ---------- (d) salts from a seed ----------

fn rss_now() -> u64 {
    fmodes::rss_now_kib().unwrap_or(0)
}

/// Chi-square of field elements over 256 equal buckets of [0, p).
fn chi_square(values: &[F]) -> f64 {
    let p = F::ORDER_U32 as u64;
    let mut buckets = [0u64; 256];
    for v in values {
        buckets[(v.as_canonical_u32() as u64 * 256 / p) as usize] += 1;
    }
    let expected = values.len() as f64 / 256.0;
    buckets.iter().map(|&b| (b as f64 - expected).powi(2) / expected).sum()
}

/// `f-salts`: change (d)'s controls (see the module documentation).
pub fn f_salts_mode(out: &Path, log_height_memory: usize) {
    fs::create_dir(out).expect("fresh output directory required");
    let perm = default_koalabear_poseidon2_16();
    let new_f = |rng: StdRng| FMmcs::new(Hash::new(perm.clone()), Compress::new(perm.clone()), 0, rng);
    let new_pinned = |rng: StdRng| Mmcs::new(Hash::new(perm.clone()), Compress::new(perm.clone()), 0, rng);
    let mut data_rng = StdRng::seed_from_u64(0x6632_5a17);
    let (h, w) = (1usize << 10, 16usize);
    let m = RowMajorMatrix::<F>::rand(&mut data_rng, h, w);
    // 1. The salts are ChaCha20(seed, stream = row) samples of the pinned sampler, the seed being the MMCS generator's
    // first 32 bytes.
    let mmcs_seed = 0x6632_0001u64;
    let fm = new_f(StdRng::seed_from_u64(mmcs_seed));
    let (cap, data) = fm.commit(vec![m.clone()]);
    let mut seed = [0u8; 32];
    StdRng::seed_from_u64(mmcs_seed).fill_bytes(&mut seed);
    let regen = p3_merkle_tree_ps::PrgSalts::<F, 8>::new(seed, h);
    let mut salts = Vec::with_capacity(h * 8);
    let (mut salt_rows_equal, mut openings_verified_f, mut openings_verified_pinned) = (0usize, 0usize, 0usize);
    let pinned_verifier = new_pinned(StdRng::seed_from_u64(1));
    let dims = [Dimensions { width: w, height: h }];
    for r in 0..h {
        let opening = fm.open_batch(r, &data);
        let (vals, (s_rows, siblings)) = (&opening.opened_values, &opening.opening_proof);
        let expect = regen.salt_row(r);
        if s_rows[0] == expect {
            salt_rows_equal += 1;
        }
        salts.extend_from_slice(&s_rows[0]);
        if fm.verify_batch(&cap, &dims, r, BatchOpeningRef::new(vals, &opening.opening_proof)).is_ok() {
            openings_verified_f += 1;
        }
        let proof_for_pinned = (s_rows.clone(), siblings.clone());
        if pinned_verifier.verify_batch(&cap, &dims, r, BatchOpeningRef::new(vals, &proof_for_pinned)).is_ok() {
            openings_verified_pinned += 1;
        }
    }
    // 2. The commitment equals the pinned (non-hiding) tree over the same rows with those salts appended.
    let salts_m = RowMajorMatrix::new(salts.clone(), 8);
    let inner = p3_merkle_tree::MerkleTreeMmcs::<<F as Field>::Packing, <F as Field>::Packing, Hash, Compress, 2, 8>::new(Hash::new(perm.clone()), Compress::new(perm.clone()), 0);
    let (cap_inner, _) = inner.commit(vec![HorizontalPair::new(m.clone(), salts_m)]);
    let commitment_equal = cap_inner == cap;
    // 3. A tampered salt fails both verifiers.
    let opening = fm.open_batch(7, &data);
    let mut bad = opening.opening_proof.clone();
    bad.0[0][0] += F::ONE;
    let tampered_rejected = fm.verify_batch(&cap, &dims, 7, BatchOpeningRef::new(&opening.opened_values, &bad)).is_err()
        && pinned_verifier.verify_batch(&cap, &dims, 7, BatchOpeningRef::new(&opening.opened_values, &bad)).is_err();
    // 4. Fresh operating-system seeds per attempt: two MMCS from the OS commit the same matrix to different caps; the
    // same seeded generator twice gives the same cap (the salts are a function of the seed alone).
    let (c1, _) = new_f(os_rng()).commit(vec![m.clone()]);
    let (c2, _) = new_f(os_rng()).commit(vec![m.clone()]);
    let (c3, _) = new_f(StdRng::seed_from_u64(mmcs_seed)).commit(vec![m.clone()]);
    // 5. The salts' empirical distribution: 2^20 PRG salt elements and 2^20 elements of the pinned way (the generator's
    // sequential draws), each against 256 equal buckets (df 255: mean 255, standard deviation 22.6).
    let big = p3_merkle_tree_ps::PrgSalts::<F, 8>::new(seed, 1 << 17);
    let prg_values: Vec<F> = (0..1usize << 17).flat_map(|r| big.salt_row(r)).collect();
    let stored_values: Vec<F> = RowMajorMatrix::<F>::rand(&mut StdRng::seed_from_u64(9), 1 << 17, 8).values;
    let (chi_prg, chi_stored) = (chi_square(&prg_values), chi_square(&stored_values));
    // 6. The resident-set effect: one matrix of 2^log rows x 16 committed by each MMCS, its prover data held.
    let lh = log_height_memory;
    let big_m = RowMajorMatrix::<F>::rand(&mut data_rng, 1 << lh, 16);
    let matrix_kib = (big_m.values.len() * 4 / 1024) as u64;
    let measure = |pinned: bool| -> (u64, u64, f64) {
        let before = rss_now();
        let t = Instant::now();
        let after = if pinned {
            let (_c, d) = new_pinned(os_rng()).commit(vec![big_m.clone()]);
            let a = rss_now();
            drop(d);
            a
        } else {
            let (_c, d) = new_f(os_rng()).commit(vec![big_m.clone()]);
            let a = rss_now();
            drop(d);
            a
        };
        (before, after, ms(t))
    };
    let (pb, pa, pt) = measure(true);
    let (fb, fa, ft) = measure(false);
    let salt_kib = ((1u64 << lh) * 8 * 4) / 1024;
    let doc = json!({"schema": crate::SCHEMA, "review": REVIEW, "tier": TIER,
        "what": "change (d): p3_merkle_tree_ps's hiding MMCS (salts regenerated from a per-matrix seed) against the pinned p3-merkle-tree's",
        "salts_are_chacha20_stream_per_row": {"rows": h, "salt_rows_equal_to_chacha20_seed_stream_row": salt_rows_equal, "all": salt_rows_equal == h,
            "seed_source": "the first 32 bytes of the MMCS's generator (here StdRng::seed_from_u64 for the check; F's prover: the operating system)"},
        "openings": {"verified_by_p3_merkle_tree_ps": openings_verified_f, "verified_by_the_pinned_p3_merkle_tree": openings_verified_pinned, "of": h,
            "tampered_salt_rejected_by_both": tampered_rejected},
        "commitment_equals_the_pinned_tree_over_the_same_salts": commitment_equal,
        "fresh_seeds": {"two_os_seeded_commitments_differ": c1 != c2, "same_seed_same_commitment": c3 == cap},
        "distribution": {"elements": prg_values.len(), "buckets": 256, "chi_square_prg_salts": chi_prg, "chi_square_stored_way_stdrng": chi_stored,
            "df": 255, "note": "a sanity check of the sampler's output, not a test of pseudorandomness"},
        "memory": {"log_height": lh, "matrix_kib": matrix_kib, "salt_matrix_kib_if_stored": salt_kib,
            "pinned": {"rss_before_kib": pb, "rss_with_prover_data_kib": pa, "increase_kib": pa.saturating_sub(pb), "ms": pt},
            "prg": {"rss_before_kib": fb, "rss_with_prover_data_kib": fa, "increase_kib": fa.saturating_sub(fb), "ms": ft},
            "difference_kib": (pa.saturating_sub(pb)) as i64 - (fa.saturating_sub(fb)) as i64},
        "peak_rss_kib": peak_rss_kib()});
    save(&out.join("salts.json"), &serde_json::to_vec_pretty(&doc).unwrap());
    let ok = salt_rows_equal == h && openings_verified_f == h && openings_verified_pinned == h && commitment_equal && tampered_rejected && c1 != c2 && c3 == cap;
    event(json!({"phase": "f_salts_done", "ok": ok, "chi_square_prg": chi_prg, "chi_square_stored": chi_stored,
        "memory_increase_kib_pinned_vs_prg": [pa.saturating_sub(pb), fa.saturating_sub(fb)], "salt_matrix_kib": salt_kib}));
    if !ok {
        std::process::exit(3);
    }
}
