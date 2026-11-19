//! L5 leaf L0' v2 (2026-10-31): the AIR shape of L0' v2 as its verifier sees it, by the same symbolic evaluation that
//! `verify_batch` runs before every verification, with C3n's next-row column sets.
//!
//! Adapted from code/l5-leaf-l0p-20261031/l0p/air_shape.rs (L0' v1's, itself from code/l5-soundcalc-20261031/air_shape.rs).
//! What changed from L0' v1's, and only that:
//! - every table's next-row column sets (main, preprocessed, permutation) are derived by `p3_batch_stark_c3n`'s
//!   `next_row_columns_for_batch` (the prover's and the verifier's function), next to the AIR's own declaration
//!   (`BaseAir::main_next_row_columns`, every column by default);
//! - the committed matrices of each tree follow C3n: a trace whose set is a proper subset is two matrices (the set's
//!   columns at zeta and zeta*g, then the rest at zeta), an empty set one matrix at zeta, a full set one matrix at both
//!   points; each matrix carries its own opening points;
//! - the claims (EF8 values the PCS absorbs: every committed column, random codewords included, at each of its
//!   points) are counted per matrix-point, for C3n and, for comparison, for the C3 layout of the same AIRs;
//! - no periodic column remains: the count and the Horner steps are reported (they should be zero).
//! Measurement only: no proving, no verification; no proof is read.
//! loop-internal self-review; not independently reviewed.
use super::*;
use p3_air::BaseAir;
use p3_air::symbolic::AirLayout;
use p3_batch_stark_c3n::symbolic::{get_log_num_quotient_chunks_for_domain, get_max_constraint_degree, get_symbolic_constraints};
use p3_commit::PolynomialSpace;
use p3_lookup::Kind;
use p3_lookup::logup::LogUpGadget;
use p3_uni_stark::{OpeningShape, StarkGenericConfig};

pub fn cli(args: &[&str]) {
    match args {
        ["--out", out] => run(Path::new(out)),
        _ => panic!("usage: shape --out OUT.json"),
    }
}

/// p3-fri 0.9.0-rc.1 `fold_schedule` (config.rs l. 323-358, with `compute_log_arity_for_round` l. 260-287), as
/// re-implemented by the L5 soundcalc driver: the arity is capped by the distance to the final height, to the next
/// input height, and by the configured maximum; an input whose height the fold reaches is rolled in there.
pub fn fold_schedule(input_log_heights: &[usize], log_final_height: usize, max_log_arity: usize) -> Vec<usize> {
    let mut heights: Vec<usize> = input_log_heights.to_vec();
    heights.sort_unstable_by(|a, b| b.cmp(a));
    heights.dedup();
    let (mut log_height, mut nxt, mut schedule) = (heights[0], 1usize, Vec::new());
    while log_height > log_final_height {
        let mut cap = log_height - log_final_height;
        if nxt < heights.len() {
            cap = cap.min(log_height - heights[nxt]);
        }
        let step = cap.min(max_log_arity);
        schedule.push(step);
        log_height -= step;
        if nxt < heights.len() && heights[nxt] == log_height {
            nxt += 1;
        }
    }
    schedule
}

/// One committed matrix as a tree lists it.
fn matrix(table: &str, what: &str, lde: usize, ood_width: usize, random_codewords: usize, points: usize, columns: Value) -> Value {
    json!({"table": table, "matrix": what, "lde_log_height": lde, "width": ood_width + random_codewords,
        "ood_width": ood_width, "of_which_random_codewords": random_codewords, "salt_elements": SALT_ELEMS,
        "opening_points": points, "columns": columns})
}

fn run(out: &Path) {
    assert!(!out.exists(), "refusing to overwrite {}", out.display());
    let start = Instant::now();
    let b = build();
    let airs = &b.airs;
    let degree_bits = degrees();
    let data = keygen(&b);
    let common = &data.common;
    let config = config(Binding::Expected, &b.digest, b.canonical_bits);
    let pcs = config.pcs();
    let is_zk = config.is_zk();
    let gadget = LogUpGadget::new();
    let none: &[p3_lookup::Lookup<F>] = &[];
    assert_eq!(airs.len(), degree_bits.len());
    assert_eq!(airs.len(), common.lookups.len());
    let derive_start = Instant::now();
    let layout = next_rows(&b, common);
    let derive_ms = derive_start.elapsed().as_secs_f64() * 1e3;

    let mut tables = Vec::new();
    let (mut total_constraints, mut max_degree, mut max_chunks) = (0usize, 0usize, 0usize);
    let (mut claims_c3n, mut claims_c3, mut p3_count_c3) = (0usize, 0usize, 0usize);
    let mut heights = Vec::new();
    let mut trees: Vec<(String, Vec<Value>)> = vec![("main".into(), vec![]), ("quotient_and_random (C3)".into(), vec![]),
        ("preprocessed".into(), vec![]), ("permutation".into(), vec![])];
    let mut random_mats = Vec::new();
    for (i, air) in airs.iter().enumerate() {
        let name = TABLES[i];
        let base_db = degree_bits[i] - is_zk;
        let n = 1usize << base_db;
        heights.push(n);
        let domain = <Pcs as p3_commit::Pcs<EF, Challenger>>::natural_domain_for_degree(pcs, n);
        let td = domain.transition_degree_multiple();
        let pre_w = common.preprocessed.as_ref().and_then(|g| g.instances[i].as_ref().map(|m| m.width)).unwrap_or(0);
        // The layout exactly as `verify_batch` builds it (p3-batch-stark verifier/mod.rs).
        let air_layout = AirLayout {
            preprocessed_width: pre_w,
            main_width: BaseAir::<F>::width(air),
            num_public_values: BaseAir::<F>::num_public_values(air),
            num_periodic_columns: BaseAir::<F>::num_periodic_columns(air),
            ..Default::default()
        };
        let lookups = &common.lookups[i];
        let log_chunks = get_log_num_quotient_chunks_for_domain::<F, EF, _, _>(air, air_layout, domain, lookups, is_zk, &gadget);
        let n_chunks = 1usize << (log_chunks + is_zk);
        let (base_all, ext_all) = get_symbolic_constraints::<F, EF, _, _>(air, air_layout, lookups, &gadget);
        let (base_air, ext_air) = get_symbolic_constraints::<F, EF, _, _>(air, air_layout, none, &gadget);
        let d_all = get_max_constraint_degree::<F, EF, _, _>(air, air_layout, n, lookups, &gadget);
        let d_air = get_max_constraint_degree::<F, EF, _, _>(air, air_layout, n, none, &gadget);
        let hint = BaseAir::<F>::max_constraint_degree(air);
        let declared_main_next = BaseAir::<F>::main_next_row_columns(air);
        let declared_pre_next = BaseAir::<F>::preprocessed_next_row_columns(air);
        let l = &layout[i];
        assert_eq!(l.main_width, air_layout.main_width);
        assert_eq!(l.preprocessed_width, pre_w);
        let mut lk = Vec::new();
        for lu in lookups.iter() {
            let (kind, bus) = match &lu.kind { Kind::Local => ("local", None), Kind::Global(name) => ("global", Some(name.clone())) };
            let widths: Vec<usize> = lu.elements.iter().map(|t| t.len()).collect();
            let denominators = if lu.flags.is_some() { 1 } else { lu.elements.len() };
            lk.push(json!({"kind": kind, "bus": bus, "column": lu.column, "tuples": lu.elements.len(),
                "tuple_width": widths.first().copied(), "widths_uniform": widths.windows(2).all(|w| w[0] == w[1]),
                "exclusive": lu.flags.is_some(), "denominators_per_row": denominators, "count_weight": lu.count_weight,
                "fraction_pin_degree": gadget.constraint_degree_with_transition(lu, td)}));
        }
        let perm_ef = if lookups.is_empty() { 0 } else { lookups.len() + 1 };
        assert_eq!(l.permutation_width, perm_ef);
        let constraints = base_all.len() + ext_all.len();
        total_constraints += constraints;
        max_degree = max_degree.max(d_all).max(hint.unwrap_or(0));
        max_chunks = max_chunks.max(n_chunks);
        let lde = degree_bits[i] + LOG_BLOWUP;
        // C3n's committed matrices and their claims (width with random codewords, at each point).
        let main_split = l.main_split();
        let mut table_claims = 0usize;
        for (cols, at_next) in main_split.matrices() {
            let points = 1 + usize::from(at_next);
            table_claims += (cols.len() + RANDOM_CODEWORDS) * points;
            let what = if main_split.is_split() { if at_next { "main: next-row columns" } else { "main: other columns" } } else { "main" };
            trees[0].1.push(matrix(name, what, lde, cols.len(), RANDOM_CODEWORDS, points,
                if main_split.is_split() && at_next { json!(cols) } else { json!(format!("{} columns", cols.len())) }));
        }
        for _ in 0..n_chunks {
            table_claims += (8 + RANDOM_CODEWORDS) * 1;
            trees[1].1.push(matrix(name, "quotient chunk", lde, 8, RANDOM_CODEWORDS, 1, Value::Null));
        }
        table_claims += 8 + RANDOM_CODEWORDS;
        random_mats.push(matrix(name, "randomization polynomial (C3)", lde, 8, RANDOM_CODEWORDS, 1, Value::Null));
        if pre_w > 0 {
            let pre_points = 1 + usize::from(!l.preprocessed.is_empty());
            table_claims += pre_w * pre_points;
            trees[2].1.push(matrix(name, "preprocessed (public: zero rows interleaved, no random codewords; salts from the key generation's seeded RNG)",
                lde, pre_w, 0, pre_points, Value::Null));
        }
        let perm_split = l.permutation_split(8);
        if perm_ef > 0 {
            for (cols, at_next) in perm_split.matrices() {
                let points = 1 + usize::from(at_next);
                table_claims += (cols.len() + RANDOM_CODEWORDS) * points;
                let what = if perm_split.is_split() { if at_next { "permutation: next-row coordinates (accumulator)" } else { "permutation: other columns (fractions)" } } else { "permutation" };
                trees[3].1.push(matrix(name, what, lde, cols.len(), RANDOM_CODEWORDS, points,
                    if perm_split.is_split() && at_next { json!(cols) } else { json!(format!("{} columns", cols.len())) }));
            }
        }
        // The C3 layout of the same AIRs (L0' v1's batch layer; change 1 alone): every main column at both points (the
        // AIR's declaration), every preprocessed column at both points, every permutation column at both points.
        let c3_main_next = !declared_main_next.is_empty();
        let c3_pre_next = !declared_pre_next.is_empty();
        let c3_table_claims = (air_layout.main_width + RANDOM_CODEWORDS) * (1 + usize::from(c3_main_next))
            + n_chunks * (8 + RANDOM_CODEWORDS) + (8 + RANDOM_CODEWORDS)
            + pre_w * (1 + usize::from(c3_pre_next && pre_w > 0))
            + if perm_ef > 0 { 2 * (8 * perm_ef + RANDOM_CODEWORDS) } else { 0 };
        let k_c3 = p3_batch_stark_c3n::num_batched_openings(air_layout.main_width, c3_main_next, pre_w, c3_pre_next, n_chunks,
            lookups.len(), 8, OpeningShape::hiding(RANDOM_CODEWORDS));
        claims_c3n += table_claims;
        claims_c3 += c3_table_claims;
        p3_count_c3 += k_c3;
        tables.push(json!({
            "instance": i, "table": name, "extended_degree_bits": degree_bits[i], "trace_height": n,
            "lde_log_height": lde, "transition_degree_multiple": td,
            "main_width": air_layout.main_width, "preprocessed_width": pre_w,
            "num_public_values": air_layout.num_public_values, "num_periodic_columns": air_layout.num_periodic_columns,
            "periodic_periods": BaseAir::<F>::periodic_periods(air),
            "next_row": {
                "main_columns": l.main, "main_count": l.main.len(), "main_split": main_split.is_split(),
                "preprocessed_columns": l.preprocessed, "permutation_ef8_columns": l.permutation,
                "permutation_base_columns": perm_split.next,
                "declared_main_next_row_columns": declared_main_next.len(),
                "declared_preprocessed_next_row_columns": declared_pre_next.len(),
                "source": "p3_batch_stark_c3n::next_row_columns_for_batch: every offset-1 variable of the symbolic constraints, lookups included"},
            "main_next_row": !l.main.is_empty(), "preprocessed_next_row": !l.preprocessed.is_empty(),
            "constraints": {"air_base": base_air.len(), "air_extension": ext_air.len(),
                            "with_lookups_base": base_all.len(), "with_lookups_extension": ext_all.len(), "total": constraints},
            "max_constraint_degree": {"air_only": d_air, "with_lookups": d_all, "air_hint": hint,
                                      "verifier_bucket_degree": d_all.max(hint.unwrap_or(0))},
            "log_num_quotient_chunks": log_chunks, "num_quotient_chunks_committed": n_chunks,
            "num_lookups": lookups.len(), "permutation_ef_columns": perm_ef,
            "lookups": lk,
            "claims_ef8_c3n": table_claims, "claims_ef8_c3_layout": c3_table_claims, "num_batched_openings_p3_c3_layout": k_c3,
        }));
    }
    trees[1].1.extend(random_mats);
    let height_bound = p3_lookup::check_multiplicity_height_bound(&common.lookups, &heights);
    let input_lde: Vec<usize> = degree_bits.iter().map(|d| d + LOG_BLOWUP).collect();
    let schedule = fold_schedule(&input_lde, LOG_FINAL_POLY_LEN + LOG_BLOWUP, MAX_LOG_ARITY);
    let mut h = *input_lde.iter().max().unwrap();
    let fri_trees: Vec<Value> = schedule.iter().map(|&a| {
        let tree = json!({"arity": 1usize << a, "tree_log_height": h - a, "leaf_ef8_values": 1usize << a,
            "codeword_log_height_before_fold": h});
        h -= a;
        tree
    }).collect();
    let periodic_total: usize = airs.iter().map(|a| BaseAir::<F>::num_periodic_columns(a)).sum();
    let periodic_horner_steps: usize = airs.iter().map(|a| BaseAir::<F>::periodic_periods(a).iter().sum::<usize>()).sum();
    assert_eq!(claims_c3, p3_count_c3, "the C3-layout claims equal Plonky3's num_batched_openings");

    let report = json!({
        "schema": "l5-leaf-l0p2/air-shape/v1",
        "review": REVIEW,
        "tier": "measurement of L0' v2's AIR shape by the verifier's symbolic evaluation; no proving, no verification",
        "configuration": config_record(),
        "is_zk": is_zk,
        "degree_bits": degree_bits,
        "tables": tables,
        "next_row_columns": next_rows_record(&layout),
        "next_row_derivation_ms": derive_ms,
        "committed_trees": trees.iter().map(|(name, mats)| json!({"tree": name, "matrices": mats})).collect::<Vec<_>>(),
        "fri": {"input_lde_log_heights": input_lde, "log_final_poly_len": LOG_FINAL_POLY_LEN, "max_log_arity": MAX_LOG_ARITY,
                "fold_schedule_log_arities": schedule, "rounds": fri_trees,
                "source": "p3-fri 0.9.0-rc.1 fold_schedule (config.rs l. 323-358), ported"},
        "periodic_columns_remaining": {"count": periodic_total,
            "horner_steps_at_zeta_if_evaluated_by_coefficients": periodic_horner_steps,
            "note": "v2 commits every program column as preprocessed data (C4a for all): no table declares a periodic column"},
        "totals": {"constraints": total_constraints, "claims_ef8_c3n": claims_c3n, "claims_ef8_c3_layout": claims_c3,
                   "num_batched_openings_p3_c3_layout": p3_count_c3,
                   "max_constraint_degree": max_degree, "max_quotient_chunks": max_chunks},
        "multiplicity_height_bound": {"heights": heights, "check_multiplicity_height_bound": format!("{height_bound:?}")},
        "elapsed_ms": start.elapsed().as_secs_f64() * 1000.0,
        "peak_rss_kib": peak_rss_kib(),
    });
    save(out.parent().unwrap_or(Path::new(".")), out.file_name().unwrap().to_str().unwrap(),
         &serde_json::to_vec_pretty(&report).unwrap());
    event(json!({"stage": "air_shape_done", "out": out.display().to_string(), "totals": report["totals"],
        "next_row_columns": report["next_row_columns"].as_array().map(|a| a.iter().map(|t| json!([t["table"], t["main_next_row_columns"].as_array().map(|v| v.len()), t["preprocessed_next_row_columns"], t["permutation_next_row_ef8_columns"]])).collect::<Vec<_>>())}));
}
