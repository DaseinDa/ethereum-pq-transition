//! Pipeline modes of code/pq-proof-pipeline-20261101 (2026-11-01), added to F2's binary (code/l5-layer-f2-20261031)
//! as two new modules (this one and `material.rs`, the standalone verifier's key-material module, byte-identical). B's
//! and F's AIRs, schedules, compilers, keys, provers and verifiers are the recorded ones; nothing here changes a
//! source that a verifier-key digest covers.
//! - `b-prove-statement --in IN --child-dir DIR --vk VK_B --out OUT`: B's proof (B as F1 re-proved it: C3, cap height
//!   5, arity at most 4) for the L0' v2 proof in DIR (`l0p2.postcard`, `metrics.json` from the L0' v2 pipeline mode
//!   `prove-statement`) with that proof's PI198 as B's statement. It is `prove_mode`'s honest path (variant `P`, child
//!   L0' v2) with one difference: the statement is the child's PI198 instead of the research fixture's. B's key is
//!   recomputed and compared with the recorded vk.json; the proof is verified in the proving process; the output
//!   directory has `prove_mode`'s layout (`proof.postcard`, `statement.json`, `report.json`, `breakdown.json`), which
//!   F's recorded `f-prove` mode reads.
//! - `f-export-key --in IN --b-vk VK_B --f-vk VK_F --proof-dir P --out OUT`: F's verifier-key material for the
//!   standalone verifier (`f-key-material.json`, `f-periodic.rle`, and `f-periodic.u32le`, the raw columns). In this
//!   process: F's key is recomputed from B's identity and compared with F's recorded vk.json (15 fields); the material
//!   is written, read back with `material.rs`, F's AIR rebuilt from it and compared with the schedule's field by field;
//!   L0' v2's, B's and F's digests recomputed by `material.rs` and compared with the recorded functions' values; the
//!   recorded proof in P verified with the rebuilt AIR.
//! research packaging; loop-internal self-review; not independently reviewed.
use crate::memory_io as fs;
use std::path::Path;
use std::time::Instant;

use p3_batch_stark_c3np::OmittedFill;
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_koala_bear::KoalaBear as F;
use serde_json::{Value, json};
use sha2::{Digest as _, Sha256};

use crate::fschedule::{PrefixItem, Schedule as FSchedule};
use crate::material::{self, DigestSources};
use crate::schedule::Schedule;
use crate::{EF, fchild, fmodes, fprove, hex, ms, peak_rss_kib, save, sha256_hex};

const SCHEMA: &str = "pq-proof-pipeline/f2/v1";
const TIER: &str = "research packaging; loop-internal self-review; not independently reviewed";

/// The sources the digests cover, as this binary compiled them (the same files `fmodes.rs` and `main.rs` include).
pub fn sources() -> DigestSources<'static> {
    DigestSources {
        fkernel: include_bytes!("fkernel.rs"),
        fschedule: include_bytes!("fschedule.rs"),
        compiler: include_bytes!("compiler.rs"),
        fchild: include_bytes!("fchild.rs"),
        fmodes: include_bytes!("fmodes.rs"),
        kernel: include_bytes!("kernel.rs"),
        schedule: include_bytes!("schedule.rs"),
    }
}

fn read_json(path: &Path) -> Value {
    serde_json::from_slice(&fs::read(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))).expect("JSON")
}

fn unhex(s: &str) -> Vec<u8> {
    material::unhex(s.trim()).expect("lower-case hex")
}

// ---------- B's proof for a statement ----------

/// `prove_mode`'s honest path for L0' v2's proof in `child_dir`, with that proof's PI198 as B's statement.
pub fn b_prove_statement(in_dir: &Path, child_dir: &Path, vk_path: &Path, out: &Path) {
    fs::create_dir(out).expect("fresh output directory required");
    crate::tracegen::ef_selftest();
    let exp = crate::variants::expected("P");
    let t0 = Instant::now();
    let mut def = crate::l0p2_def(in_dir);
    let metrics = read_json(&child_dir.join("metrics.json"));
    let bytes = fs::read(child_dir.join("l0p2.postcard")).expect("l0p2.postcard");
    assert_eq!(metrics["proof_sha256"], json!(sha256_hex(&bytes)), "the child proof is the one its prove run recorded");
    let pi = unhex(metrics["params"]["pi_bytes"].as_str().expect("params.pi_bytes"));
    assert_eq!(pi.len(), 198, "PI198");
    let research_statement = def.statement.clone();
    // The one difference from `prove_mode`: B's statement is the child's PI198.
    def.statement = pi.iter().map(|&v| F::from_u8(v)).collect();
    let spec = crate::child_spec(&def);
    let s = Schedule::build(&spec);
    let schedule_ms = ms(t0);
    let t = Instant::now();
    let (cd, replay_report) = crate::replay_child(&def, &s, &bytes, &def.statement, "accepted");
    let replay_ms = ms(t);
    let t = Instant::now();
    let (kt, _xs, honest_report) = crate::tracegen::honest(&s, &cd);
    let trace = kt.finalize();
    drop(kt);
    let (constraints, honest_check, honest_names, _honest_roles) = crate::check_report(&s, &trace, &cd.pv);
    assert_eq!(honest_names, exp.honest, "the honest generation from the child: {honest_check}");
    let tracegen_ms = ms(t);
    let pv = cd.pv.clone();
    assert_eq!(pv, def.statement, "B's public values are the child's PI198");
    drop(cd);
    let trace_sha = {
        let mut h = Sha256::new();
        for v in &trace.values {
            h.update(v.as_canonical_u32().to_le_bytes());
        }
        hex(&h.finalize())
    };
    let rss_before_keygen = peak_rss_kib();
    let (data, key) = crate::b2_keygen(&s);
    let vk = crate::b2_vk_digest(&s, &key);
    let vk_check = crate::check_b2_vk(&crate::b2_vk_json(&s, &data.common, &key, &vk), &read_json(vk_path));
    assert_eq!(vk_check["all_equal"], json!(true), "B's recomputed key differs from the recorded vk.json: {vk_check}");
    let rss_after_keygen = peak_rss_kib();
    let cfg = crate::b2_config(&vk, &pv);
    let mem_before = crate::mem_available_kib();
    let t = Instant::now();
    let proof = crate::prove_kernel(&cfg, &s, &data, &trace, &pv);
    let prove_ms = ms(t);
    let rss_after = peak_rss_kib();
    let encoded = postcard::to_allocvec(&proof).unwrap();
    drop(proof);
    save(&out.join("proof.postcard"), &encoded);
    let decoded = crate::decode_strict(&encoded);
    let (accepted, error, verify_ms) = crate::verify_kernel(&s, &vk, &data.common, &decoded, &pv);
    let (bd, bd_errors) = crate::breakdown::report(&encoded, &decoded, &crate::kshape(&s, &data.common));
    save(&out.join("breakdown.json"), &serde_json::to_vec_pretty(&bd).unwrap());
    let statement = json!({"schema": crate::SCHEMA, "variant": "P", "child_kind": "l0p2", "public_values": crate::pv_json(&pv),
        "public_values_sha256": sha256_hex(&pv.iter().flat_map(|v| v.as_canonical_u32().to_le_bytes()).collect::<Vec<u8>>()),
        "b2_vk_digest": hex(&vk), "child_vk_digest": hex(&s.child.child_vk), "compiled_program_sha256": hex(&s.child.program_sha256),
        "b2_preprocessed_commitment_keccak256": vk_check["commitment_keccak256"], "pi198_hex": hex(&pi),
        "pipeline": SCHEMA});
    save(&out.join("statement.json"), &serde_json::to_vec_pretty(&statement).unwrap());
    let terminal_zero = decoded.lookup_terminals.iter().flatten().all(|x| x.0 == EF::ZERO);
    let as_expected = accepted && bd_errors.is_empty();
    let report = json!({"schema": crate::SCHEMA, "pipeline": SCHEMA, "review": crate::REVIEW, "tier": TIER, "n": 1, "variant": "P", "child_kind": "l0p2",
        "expected": exp.expect, "what": "prove_mode's honest path (variant P, child L0' v2) with the child's PI198 as B's statement",
        "statement_differs_from_the_research_fixture": pv != research_statement,
        "child_run": {"kind": "L0' v2 pipeline proof", "native_verdict": "accepted", "proof_sha256": sha256_hex(&bytes), "proof_bytes": bytes.len()},
        "native_row_check": {"constraints_per_row": constraints, "rows": s.n, "honest_generation_violations": honest_names},
        "proved_trace_sha256_u32le_row_major": trace_sha, "lookup_terminal_is_zero": terminal_zero,
        "in_process": {"accepted": accepted, "error": error, "as_expected": accepted},
        "as_expected": as_expected,
        "proof_bytes": encoded.len(), "proof_sha256": sha256_hex(&encoded), "b2_vk_digest": hex(&vk), "key_recomputed_against_vk_json": vk_check,
        "breakdown_summary": bd["summary"], "breakdown_all_checks_passed": bd["all_checks_passed"], "breakdown_errors": bd_errors,
        "compiled_program_sha256": hex(&s.child.program_sha256), "replay": replay_report, "honest_generation": honest_report,
        "timings_ms": {"schedule_and_compile": schedule_ms, "child_replay_open_inputs_and_identities": replay_ms, "trace_generation_and_check": tracegen_ms,
            "b_keygen": key.keygen_ms, "prove": prove_ms, "verify_in_process": verify_ms},
        "mem_available_kib_before_prove": mem_before, "peak_rss_kib_before_keygen": rss_before_keygen, "peak_rss_kib_after_keygen": rss_after_keygen,
        "peak_rss_kib_after_prove": rss_after, "rayon_threads": std::env::var("RAYON_NUM_THREADS").ok(), "b2_proof_parameters": crate::b2_params()});
    save(&out.join("report.json"), &serde_json::to_vec_pretty(&report).unwrap());
    crate::event(json!({"phase": "pipeline_b_prove_done", "accepted_in_process": accepted, "error": error, "proof_bytes": encoded.len(),
        "prove_ms": prove_ms, "peak_rss_kib": rss_after, "as_expected": as_expected}));
    if !as_expected {
        std::process::exit(3);
    }
}

/// Same B statement/hash checks as fmodes::b_proof, using memory descriptors.
/// fmodes.rs is a digest source and deliberately remains byte-identical.
pub fn b_proof_memory(dir: &Path, bc: &fchild::BChild) -> (Value, Vec<u8>, Vec<F>) {
    let st = read_json(&dir.join("statement.json"));
    let report = read_json(&dir.join("report.json"));
    assert_eq!(st["b2_vk_digest"].as_str().unwrap(), hex(&bc.vk));
    let bytes = fs::read(dir.join("proof.postcard")).unwrap();
    assert_eq!(report["proof_sha256"].as_str().unwrap(), sha256_hex(&bytes));
    let pv = crate::pv_from_json(&st["public_values"]);
    let expect = if report["in_process"]["accepted"] == json!(true) { "accepted" } else { "OodEvaluationMismatch" };
    (json!({"variant": st["variant"], "proof_sha256": sha256_hex(&bytes), "proof_bytes": bytes.len(),
        "b_in_process_verdict": report["in_process"], "native_expected": expect}), bytes, pv)
}

// ---------- F's verifier-key material ----------

fn table_json(t: &crate::schedule::TableSpec) -> Value {
    json!({"name": t.name, "log_trace": t.log_trace, "width": t.width, "pre_width": t.pre_width, "perm_width": t.perm_width,
        "chunks": t.chunks, "log_qd": t.log_qd, "public": t.public, "next_main": t.next_main, "next_pre": t.next_pre,
        "next_perm": t.next_perm, "lookup_bus": t.lookup_bus})
}
fn ftable_json(t: &crate::fschedule::TableSpec) -> Value {
    json!({"name": t.name, "log_trace": t.log_trace, "width": t.width, "pre_width": t.pre_width, "perm_width": t.perm_width,
        "chunks": t.chunks, "log_qd": t.log_qd, "public": t.public, "next_main": t.next_main, "next_pre": t.next_pre,
        "next_perm": t.next_perm, "lookup_bus": t.lookup_bus})
}
fn cap_u32(cap: &[[F; 8]]) -> Vec<[u32; 8]> {
    cap.iter().map(|d| d.map(|x| x.as_canonical_u32())).collect()
}

/// `f-export-key` (see the module documentation).
pub fn f_export_key(in_dir: &Path, b_vk_path: &Path, f_vk_path: &Path, proof_dir: &Path, out: &Path) {
    fs::create_dir(out).expect("fresh output directory required");
    let t0 = Instant::now();
    // F's identity, exactly as `f-prove` and `f-verify` rebuild it.
    let bc = fchild::b_child(in_dir, b_vk_path);
    let spec = fchild::b_spec(&bc);
    let s = FSchedule::build(&spec);
    let (common, next, _rule, vk) = fmodes::f_identity(&s);
    let f_vk_check = fmodes::check_f_vk(&fmodes::f_vk_json(&s, &common, &next, &vk), &read_json(f_vk_path));
    assert_eq!(f_vk_check["all_equal"], json!(true), "F's recomputed key differs from the recorded vk.json: {f_vk_check}");
    let identity_ms = ms(t0);
    // L0' v2's identity as B pins it (`l0p2_def`; L0' v2's key recomputed and checked against its vk.json).
    let def = crate::l0p2_def(in_dir);
    let lb = crate::l0p2::build();
    let l_next = p3_batch_stark_c3n::next_row_columns_for_batch(lb.airs.iter(), &def.data.common);
    let l_pre_cap = def.pre_cap();
    assert_eq!(crate::l0p2::vk_digest(&lb, &l_pre_cap, &l_next), def.child_vk, "L0' v2's identity digest");
    assert_eq!(def.child_vk, bc.s.child.child_vk, "B pins L0' v2's identity digest");
    assert_eq!(bc.vk, s.child.child_vk, "F pins B's verifier-key digest");
    let src = sources();
    // The prefixes the digests cover must be the ones the material's sections describe.
    let l_prefix_recorded: Vec<F> = crate::schedule::prefix_elements(&bc.s.child.prefix, &vec![F::ZERO; bc.s.child.num_public]);
    let f_prefix_recorded: Vec<F> = crate::fschedule::prefix_elements(&s.child.prefix, &vec![F::ZERO; s.child.num_public]);
    let b_domain = match &s.child.prefix[0] {
        PrefixItem::Bytes(name, bytes) if name == "b_domain" => String::from_utf8(bytes.clone()).expect("ASCII domain"),
        other => panic!("B's prefix starts with {}", other.name()),
    };
    let l0p2_section = json!({
        "vk_label": "PQ-MIGRATE-RESEARCH-L5-B1-CHILD-L0P2-VK-v1",
        "domain": String::from_utf8_lossy(crate::l0p2::DOMAIN), "air_digest": hex(&crate::l0p2::air_digest()), "program_digest": hex(&lb.digest),
        "descriptor": crate::l0p2::descriptor(lb.canonical_bits), "degree_bits": crate::l0p2::degrees(),
        "preprocessed_cap": cap_u32(&l_pre_cap),
        "next_rows": l_next.iter().map(|n| json!({"main_width": n.main_width, "main": n.main, "preprocessed_width": n.preprocessed_width,
            "preprocessed": n.preprocessed, "permutation_width": n.permutation_width, "permutation": n.permutation})).collect::<Vec<_>>(),
        "vk_digest": hex(&def.child_vk)});
    let bs = &bc.s;
    let bchild = &bs.child;
    let b_section = json!({
        "vk_label": "PQ-MIGRATE-RESEARCH-L5-B2-VK-v1", "domain": b_domain,
        "schedule": {"n": bs.n, "main_width": crate::kernel::WIDTH, "pre_width": bs.air.pre.len(), "q": bs.q, "num_public": bs.num_public,
            "t_rows": bs.t_rows, "block_rows": bs.block_rows, "program_len": bs.program.len()},
        "params": {"log_blowup": crate::K_LOG_BLOWUP, "log_final_poly_len": crate::K_LOG_FINAL_POLY_LEN, "max_log_arity": crate::K_MAX_LOG_ARITY,
            "num_queries": crate::K_QUERIES, "random_codewords": crate::RANDOM_CODEWORDS, "salt_elems": crate::SALT_ELEMS,
            "digest_elems": crate::DIGEST_ELEMS, "cap_height": crate::K_CAP_HEIGHT},
        "child": {"index_bits": bchild.index_bits, "num_queries": bchild.num_queries, "log_final_poly_len": bchild.log_final_poly_len,
            "log_blowup": bchild.log_blowup, "cap_height": crate::CAP_HEIGHT, "fri_log_arities": bchild.fri_log_arities,
            "tables": bchild.tables.iter().map(table_json).collect::<Vec<_>>(), "vk_digest": hex(&bchild.child_vk),
            "num_public": bchild.num_public, "program_sha256": hex(&bchild.program_sha256)},
        "air_digest": hex(&bc.key.air_digest), "program_digest": hex(&bc.key.program_digest), "salt_seed": hex(&bc.key.salt_seed),
        "preprocessed_cap": cap_u32(bc.key.commitment.roots()), "bus": crate::kernel::BUS, "vk_digest": hex(&bc.vk)});
    let fchild_spec = &s.child;
    let f_section = json!({
        "vk_label": "PQ-MIGRATE-RESEARCH-L5-F2-VK-v1", "domain": String::from_utf8_lossy(fmodes::F_DOMAIN), "bus": crate::fkernel::BUS,
        "schedule": {"n": s.n, "q": s.q, "num_public": s.num_public, "t_rows": s.t_rows, "block_rows": s.block_rows, "program_len": s.program.len()},
        "params": {"log_blowup": fmodes::F_LOG_BLOWUP, "log_final_poly_len": fmodes::F_LOG_FINAL_POLY_LEN, "max_log_arity": fmodes::F_MAX_LOG_ARITY,
            "num_queries": fmodes::F_QUERIES, "random_codewords": crate::RANDOM_CODEWORDS, "salt_elems": crate::SALT_ELEMS,
            "digest_elems": crate::DIGEST_ELEMS, "cap_height": fmodes::F_CAP_HEIGHT},
        "child": {"index_bits": fchild_spec.index_bits, "num_queries": fchild_spec.num_queries, "log_final_poly_len": fchild_spec.log_final_poly_len,
            "log_blowup": fchild_spec.log_blowup, "cap_height": crate::K_CAP_HEIGHT, "fri_log_arities": fchild_spec.fri_log_arities,
            "tables": fchild_spec.tables.iter().map(ftable_json).collect::<Vec<_>>(), "vk_digest": hex(&fchild_spec.child_vk),
            "domain": b_domain, "num_public": fchild_spec.num_public, "program_sha256": hex(&fchild_spec.program_sha256)},
        "air": material::air_to_json(&s.air),
        "next_row_derived": material::next_rows_to_json(&next.0), "next_row_opened": material::next_rows_to_json(&next.1),
        "lookups": common.lookups[0].iter().map(|l| json!({"kind": format!("{:?}", l.kind), "column": l.column, "tuples": l.elements.len(), "count_weight": l.count_weight})).collect::<Vec<_>>(),
        "vk_digest": hex(&vk)});
    let doc = json!({"schema": material::SCHEMA, "review": crate::REVIEW, "tier": TIER,
        "what": "F's verifier-key material: F's AIR data (the schedule's periodic columns in f-periodic.rle, their indices, the public-value binding map, the first transcript row's count), F's next-row sets, and the preimages of F's, B's and L0' v2's identity digests; a verifier rebuilds F's AIR from it and recomputes the three digests",
        "sources_sha256": material::sources_json(&src), "f": f_section, "b": b_section, "l0p2": l0p2_section});
    let json_bytes = serde_json::to_vec_pretty(&doc).unwrap();
    save(&out.join("f-key-material.json"), &json_bytes);
    let rle = material::encode_periodic(&s.air.periodic);
    save(&out.join("f-periodic.rle"), &rle);
    let raw: Vec<u8> = s.air.periodic.iter().flat_map(|c| c.iter().flat_map(|v| v.as_canonical_u32().to_le_bytes())).collect();
    save(&out.join("f-periodic.u32le"), &raw);
    // ---- read back with material.rs and check against the recorded functions ----
    let t = Instant::now();
    let m: Value = serde_json::from_slice(&fs::read(out.join("f-key-material.json")).unwrap()).unwrap();
    let fa = &m["f"]["air"];
    let cols = material::decode_periodic(&fs::read(out.join("f-periodic.rle")).unwrap(), material::num(&fa["periodic"], "columns").unwrap(),
        material::num(&fa["periodic"], "rows").unwrap()).expect("decode the periodic columns");
    assert_eq!(hex(&material::periodic_sha256(&cols)), fmodes::periodic_sha256(&s), "the periodic columns' SHA-256");
    let air = material::air_from_material(fa, cols).expect("F's AIR from the material");
    let same_air = air.log_n == s.air.log_n && air.num_public == s.air.num_public && air.periodic == s.air.periodic
        && air.periodic_names == s.air.periodic_names && format!("{:?}", air.pidx) == format!("{:?}", s.air.pidx)
        && air.pub_terms == s.air.pub_terms && air.k0 == s.air.k0;
    assert!(same_air, "F's AIR rebuilt from the material differs from the schedule's");
    let derived = material::next_rows_from_json(&m["f"]["next_row_derived"]).unwrap();
    let opened = material::next_rows_from_json(&m["f"]["next_row_opened"]).unwrap();
    assert_eq!((&derived, &opened), (&next.0, &next.1), "next-row sets");
    let recomputed_derived = p3_batch_stark_c3np::next_row_columns_for_batch(std::iter::once(&air), &common).remove(0);
    assert_eq!(recomputed_derived, next.0, "the derived next-row sets of the rebuilt AIR");
    let [_, _, _, q, cw, salt, _, _] = material::f_params(&m["f"]).unwrap();
    assert_eq!(material::opened_from_derived(&recomputed_derived, q, cw, salt), next.1, "the break-even rule");
    let (f_vk, b_vk, l_vk) = material::digest_chain(&m, &air, &derived, &opened, &src).expect("the digest chain");
    assert_eq!((f_vk, b_vk, l_vk), (vk, bc.vk, def.child_vk), "material.rs's digests equal the recorded functions'");
    assert_eq!(material::prefix_elements(&material::l0p2_prefix_json(&m["l0p2"]).unwrap()).unwrap(), l_prefix_recorded, "L0' v2's prefix");
    assert_eq!(material::prefix_elements(&material::b_prefix_json(&b_domain, &bc.vk, s.child.num_public)).unwrap(), f_prefix_recorded, "B's prefix");
    let readback_ms = ms(t);
    // The recorded proof of F, verified with the rebuilt AIR, F's key data and F's opened next-row sets.
    let st = read_json(&proof_dir.join("statement.json"));
    let pv = crate::pv_from_json(&st["public_values"]);
    let bytes = fs::read(proof_dir.join("proof.postcard")).expect("proof.postcard");
    let proof = fprove::decode_strict_f(&bytes);
    let t = Instant::now();
    let r = p3_batch_stark_c3np::verify_batch_with_next_row_columns(&fmodes::f_config(&vk, &pv), std::slice::from_ref(&air), &proof,
        &[pv.clone()], &common, std::slice::from_ref(&opened), OmittedFill::Zero);
    let verify_ms = ms(t);
    assert!(r.is_ok(), "the recorded proof with the rebuilt AIR: {r:?}");
    let report = json!({"schema": SCHEMA, "review": crate::REVIEW, "tier": TIER, "phase": "f_export_key",
        "f_key_recomputed_against_f_vk_json": f_vk_check, "f_vk_digest": hex(&vk), "b_vk_digest": hex(&bc.vk), "l0p2_vk_digest": hex(&def.child_vk),
        "material_digests_equal_recorded_functions": true, "air_rebuilt_equal_to_schedule": same_air,
        "periodic_columns": {"count": s.air.periodic.len(), "rows": s.n, "sha256_u32le_column_major": fmodes::periodic_sha256(&s),
            "raw_bytes": raw.len(), "rle_bytes": rle.len(), "rle_sha256": sha256_hex(&rle)},
        "files": {"f-key-material.json": {"bytes": json_bytes.len(), "sha256": sha256_hex(&json_bytes)},
            "f-periodic.rle": {"bytes": rle.len(), "sha256": sha256_hex(&rle)}, "f-periodic.u32le": {"bytes": raw.len(), "sha256": sha256_hex(&raw)}},
        "recorded_proof": {"dir": proof_dir.display().to_string(), "proof_sha256": sha256_hex(&bytes), "proof_bytes": bytes.len(),
            "accepted_with_the_rebuilt_air": true, "verify_ms": verify_ms},
        "timings_ms": {"b_child_schedule_f_identity": identity_ms, "readback_and_digests": readback_ms}, "peak_rss_kib": peak_rss_kib()});
    save(&out.join("export-report.json"), &serde_json::to_vec_pretty(&report).unwrap());
    crate::event(report);
}

pub fn cli(args: &[String]) {
    let arg = |name: &str| -> std::path::PathBuf {
        let i = args.iter().position(|a| a == name).unwrap_or_else(|| panic!("{name} required"));
        std::path::PathBuf::from(&args[i + 1])
    };
    match args.get(1).map(String::as_str) {
        Some("b-prove-statement") => b_prove_statement(&arg("--in"), &arg("--child-dir"), &arg("--vk"), &arg("--out")),
        Some("f-export-key") => f_export_key(&arg("--in"), &arg("--b-vk"), &arg("--f-vk"), &arg("--proof-dir"), &arg("--out")),
        other => panic!("unknown pipeline mode {other:?}"),
    }
}
