//! Exact byte breakdown of a proof of B (L5 layer B2, 2026-11-01; F1: B's caps of 2^K_CAP_HEIGHT roots): C3b's breakdown (code/l5-c3b-20261031/c3b/breakdown.rs,
//! itself C3's and E0's) for B's batch-STARK proof under p3_batch_stark_c3 with a preprocessed round: four input trees
//! in opening order (main trace; the quotient chunks followed by the randomization polynomial in one tree; B's
//! preprocessed trace, pinned, without random codewords; the LogUp permutation trace), then the FRI rounds. Every
//! reported figure is the length of the postcard encoding of a decoded sub-value or an explicit framing part (vector
//! lengths as varints, `Option` tags). Every branch of the partition has its own independently computed encoded length
//! and must equal the sum of its parts; the root must equal the file size; re-encoding the decoded proof must give the
//! input bytes; the field encodings of `BatchProof`, `BatchCommitments`, the instance, the out-of-domain wire form, the
//! opening-proof tuple and `FriProof`, concatenated in order, must equal the whole. These checks guarantee totals, byte
//! coverage and shape; they cannot detect two errors that offset each other.
//! loop-internal self-review; not independently reviewed.
use serde::Serialize;
use serde_json::Map;

use super::*;

const F_BYTES: usize = 4;
const EF_BYTES: usize = 32;
const DIGEST_BYTES: usize = 4 * DIGEST_ELEMS;

/// B's committed shape: the expectations of the breakdown's shape checks.
pub struct KShape {
    pub log_n: usize,
    pub width: usize,
    pub pre_width: usize,
    /// Permutation width in base columns (8 per EF8 column: the accumulator and one per packed lookup).
    pub perm_width: usize,
    pub chunks: usize,
    pub fri_log_arities: Vec<usize>,
}

const BATCHES: [&str; 4] = ["main", "quotient_and_random", "preprocessed", "permutation"];

fn enc<T: Serialize + ?Sized>(v: &T) -> Vec<u8> {
    postcard::to_allocvec(v).expect("postcard encoding")
}
fn nb<T: Serialize + ?Sized>(v: &T) -> usize {
    enc(v).len()
}
fn vlen(n: usize) -> usize {
    nb(&n)
}

#[derive(Serialize)]
struct Node {
    name: String,
    bytes: usize,
    #[serde(skip_serializing_if = "Map::is_empty")]
    info: Map<String, Value>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    parts: Vec<Node>,
}

impl Node {
    fn leaf(name: &str, bytes: usize) -> Self {
        Node { name: name.into(), bytes, info: Map::new(), parts: vec![] }
    }
    fn branch(name: &str, bytes: usize, parts: Vec<Node>) -> Self {
        Node { name: name.into(), bytes, info: Map::new(), parts }
    }
    fn with(mut self, key: &str, value: Value) -> Self {
        self.info.insert(key.into(), value);
        self
    }
}

fn check_tree(node: &Node, path: &str, errors: &mut Vec<String>) -> usize {
    let here = if path.is_empty() { node.name.clone() } else { format!("{path}/{}", node.name) };
    if node.parts.is_empty() {
        return 1;
    }
    let sum: usize = node.parts.iter().map(|p| p.bytes).sum();
    if sum != node.bytes {
        errors.push(format!("{here}: parts sum to {sum}, encoded length {}", node.bytes));
    }
    node.parts.iter().map(|p| check_tree(p, &here, errors)).sum()
}

fn flat<T: Serialize>(name: &str, v: &[T], elem: usize) -> Node {
    Node::branch(name, nb(v), vec![Node::leaf("framing", vlen(v.len())), Node::leaf("values", elem * v.len())]).with("count", json!(v.len()))
}
fn nested2<T: Serialize>(name: &str, v: &[Vec<T>], elem: usize) -> Node {
    let framing = vlen(v.len()) + v.iter().map(|a| vlen(a.len())).sum::<usize>();
    let count: usize = v.iter().map(Vec::len).sum();
    Node::branch(name, nb(v), vec![Node::leaf("framing", framing), Node::leaf("values", elem * count)]).with("count", json!(count))
}
fn nested3<T: Serialize>(name: &str, v: &[Vec<Vec<T>>], elem: usize) -> Node {
    let mut framing = vlen(v.len());
    let mut count = 0;
    for a in v {
        framing += vlen(a.len());
        for b in a {
            framing += vlen(b.len());
            count += b.len();
        }
    }
    Node::branch(name, nb(v), vec![Node::leaf("framing", framing), Node::leaf("values", elem * count)]).with("count", json!(count))
}
fn nested4<T: Serialize>(name: &str, v: &[Vec<Vec<Vec<T>>>], elem: usize) -> Node {
    let mut framing = vlen(v.len());
    let mut count = 0;
    for a in v {
        framing += vlen(a.len());
        for b in a {
            framing += vlen(b.len());
            for c in b {
                framing += vlen(c.len());
                count += c.len();
            }
        }
    }
    Node::branch(name, nb(v), vec![Node::leaf("framing", framing), Node::leaf("values", elem * count)]).with("count", json!(count))
}
fn cap_node<C: Serialize>(name: &str, cap: &C, roots: usize) -> Node {
    Node::branch(name, nb(cap), vec![Node::leaf("framing", vlen(roots)), Node::leaf("digests", DIGEST_BYTES * roots)]).with("roots", json!(roots))
}
type Com = <HPcs as p3_commit::Pcs<EF, Challenger>>::Commitment;
fn opt_cap(name: &str, v: &Option<Com>) -> Node {
    match v {
        Some(cap) => Node::branch(name, nb(v), vec![Node::leaf("tag", 1), cap_node("cap", cap, cap.num_roots())]),
        None => Node::branch(name, nb(v), vec![Node::leaf("tag", 1)]),
    }
}
fn opt_vec_node<T: Serialize>(name: &str, v: &Option<Vec<T>>, elem: usize) -> Node {
    match v {
        Some(x) => Node::branch(name, nb(v), vec![Node::leaf("tag", 1), flat("vector", x, elem)]),
        None => Node::branch(name, nb(v), vec![Node::leaf("tag", 1)]),
    }
}
fn concat_check(label: &str, whole: &[u8], parts: &[Vec<u8>], checks: &mut Vec<Value>, errors: &mut Vec<String>) {
    let ok = parts.concat() == whole;
    if !ok {
        errors.push(format!("field order: {label}"));
    }
    checks.push(json!({"check": format!("field order: {label}"), "passed": ok}));
}
fn check(label: &str, ok: bool, detail: Value, checks: &mut Vec<Value>, errors: &mut Vec<String>) {
    if !ok {
        errors.push(format!("{label}: {detail}"));
    }
    checks.push(json!({"check": label, "passed": ok, "detail": detail}));
}

/// The exact partition of a proof of B, its component summary, its shape (tables, heights, widths, trees, queries) and
/// the self-checks.
pub fn report(bytes: &[u8], proof: &KProof, spec: &KShape) -> (Value, Vec<String>) {
    let mut errors = vec![];
    let mut checks = vec![];
    let total = bytes.len();
    check("element sizes (F 4, EF8 32, digest 32)", nb(&F::ONE) == F_BYTES && nb(&EF::ONE) == EF_BYTES && nb(&[F::ONE; DIGEST_ELEMS]) == DIGEST_BYTES,
        json!([nb(&F::ONE), nb(&EF::ONE), nb(&[F::ONE; DIGEST_ELEMS])]), &mut checks, &mut errors);
    let re = enc(proof);
    check("re-encoding gives the input bytes", re == bytes, json!({"input_sha256": sha256_hex(bytes), "reencoded_sha256": sha256_hex(&re)}), &mut checks, &mut errors);
    concat_check("BatchProof", bytes, &[enc(&proof.commitments), enc(&proof.opened_values), enc(&proof.opening_proof),
        enc(&proof.lookup_terminals), enc(&proof.degree_bits), enc(&proof.lookup_pow_witness), enc(&proof.ood_pow_witness)], &mut checks, &mut errors);
    let c = &proof.commitments;
    concat_check("BatchCommitments (main, permutation, quotient_chunks, random)", &enc(c),
        &[enc(&c.main), enc(&c.permutation), enc(&c.quotient_chunks), enc(&c.random)], &mut checks, &mut errors);
    let insts = &proof.opened_values.instances;
    check("one instance", insts.len() == 1, json!(insts.len()), &mut checks, &mut errors);
    let inst = &insts[0];
    concat_check("BatchOpenedValues (instance count, instance)", &enc(&proof.opened_values), &[enc(&insts.len()), enc(inst)], &mut checks, &mut errors);
    concat_check("OpenedValuesWithLookups (base, permutation_local, permutation_next)", &enc(inst),
        &[enc(&inst.base_opened_values), enc(&inst.permutation_local), enc(&inst.permutation_next)], &mut checks, &mut errors);
    let ov = &inst.base_opened_values;
    let pre_local = ov.preprocessed_local().map(<[EF]>::to_vec);
    let pre_next = ov.preprocessed_next().map(<[EF]>::to_vec);
    concat_check("out-of-domain values (OpenedValuesRepr wire form)", &enc(ov), &[enc(&ov.trace_local), enc(&ov.trace_next),
        enc(&pre_local), enc(&pre_next), enc(&ov.quotient_chunks), enc(&ov.random)], &mut checks, &mut errors);
    let (rcw, fri) = &proof.opening_proof;
    concat_check("opening proof (random-codeword openings, FriProof)", &enc(&proof.opening_proof), &[enc(rcw), enc(fri)], &mut checks, &mut errors);
    concat_check("FriProof", &enc(fri), &[enc(&fri.batch_pow_witness), enc(&fri.commit_phase_commits), enc(&fri.commit_pow_witnesses),
        enc(&fri.input_openings), enc(&fri.commit_phase_openings), enc(&fri.final_poly), enc(&fri.query_pow_witness)], &mut checks, &mut errors);

    // Shape against B's configuration.
    let w = spec.width;
    let lde = spec.log_n + 1 + K_LOG_BLOWUP;
    let chunks = ov.quotient_chunks.len();
    check("degree_bits = [log_n + 1] (hiding doubles the trace)", proof.degree_bits == vec![spec.log_n + 1], json!(proof.degree_bits), &mut checks, &mut errors);
    let widths: Vec<Vec<usize>> = fri.input_openings.iter().map(|b| b.opened_values[0].iter().map(Vec::len).collect()).collect();
    let expected_widths = vec![vec![w + RANDOM_CODEWORDS], vec![8 + RANDOM_CODEWORDS; spec.chunks + 1], vec![spec.pre_width], vec![spec.perm_width + RANDOM_CODEWORDS]];
    check("input batches [main, quotient_and_random, preprocessed, permutation]; widths: 8 random codewords on every matrix but the preprocessed one",
        widths == expected_widths, json!({"measured": widths, "expected": expected_widths}), &mut checks, &mut errors);
    let all_queries = fri.input_openings.iter().all(|b| b.opened_values.len() == K_QUERIES
        && b.opened_values.iter().all(|q| q.iter().map(Vec::len).collect::<Vec<_>>() == b.opened_values[0].iter().map(Vec::len).collect::<Vec<_>>())
        && b.opening_proof.0.len() == K_QUERIES
        && b.opening_proof.0.iter().all(|q| q.len() == b.opened_values[0].len() && q.iter().all(|s| s.len() == SALT_ELEMS)))
        && fri.commit_phase_openings.iter().all(|r| r.sibling_values.len() == K_QUERIES && r.opening_proof.0.len() == K_QUERIES
            && r.opening_proof.0.iter().all(|q| q.len() == 1 && q[0].len() == SALT_ELEMS));
    check("every input batch and FRI round: 43 queries with one 8-element salt per matrix", all_queries, json!(K_QUERIES), &mut checks, &mut errors);
    let arities: Vec<usize> = fri.commit_phase_openings.iter().map(|r| r.sibling_values[0].len() + 1).collect();
    let expected_arities: Vec<usize> = spec.fri_log_arities.iter().map(|&la| 1usize << la).collect();
    check("FRI arities = pinned fold_schedule (p3-fri config.rs l. 323)", arities == expected_arities, json!({"measured": arities, "expected": expected_arities}), &mut checks, &mut errors);
    check("final polynomial has 2^log_final_poly_len coefficients", fri.final_poly.len() == 1 << K_LOG_FINAL_POLY_LEN, json!(fri.final_poly.len()), &mut checks, &mut errors);
    check("out-of-domain shape: W at zeta and at zeta*g, the preprocessed trace at zeta only, the quotient chunks of 8, random 8",
        ov.trace_local.len() == w && ov.trace_next.as_ref().is_some_and(|v| v.len() == w) && chunks == spec.chunks
            && ov.quotient_chunks.iter().all(|c| c.len() == 8) && ov.random.as_ref().is_some_and(|r| r.len() == 8)
            && pre_local.as_ref().is_some_and(|v| v.len() == spec.pre_width) && pre_next.is_none(),
        json!({"trace_local": ov.trace_local.len(), "preprocessed_local": pre_local.as_ref().map(Vec::len), "preprocessed_next": pre_next.as_ref().map(Vec::len), "quotient_chunks": chunks}),
        &mut checks, &mut errors);
    check("LogUp out-of-domain shape: the permutation trace at zeta and zeta*g, (lookups + 1) x 8 values each",
        inst.permutation_local.len() == spec.perm_width && inst.permutation_next.len() == spec.perm_width,
        json!({"local": inst.permutation_local.len(), "next": inst.permutation_next.len(), "expected": spec.perm_width}), &mut checks, &mut errors);
    let rcw_shape: Vec<Vec<usize>> = rcw.iter().map(|r| r.iter().map(Vec::len).collect()).collect();
    let rcw_values: Vec<Vec<Vec<usize>>> = rcw.iter().map(|r| r.iter().map(|m| m.iter().map(Vec::len).collect()).collect()).collect();
    let rcw_ok = rcw.len() == BATCHES.len()
        && rcw.iter().enumerate().all(|(b, r)| r.iter().all(|m| m.iter().all(|p| p.len() == if BATCHES[b] == "preprocessed" { 0 } else { RANDOM_CODEWORDS })));
    check("random-codeword openings: 8 values per matrix and point, none for the preprocessed trace (no random codewords)", rcw_ok,
        json!({"points_per_matrix_per_batch": rcw_shape, "values": rcw_values}), &mut checks, &mut errors);
    // F1: caps of 2^K_CAP_HEIGHT roots (B2: one root, cap height 0).
    let roots = 1usize << K_CAP_HEIGHT;
    check("commitments: caps of 2^cap_height roots; a permutation commitment; no separate randomization commitment (C3)",
        c.main.num_roots() == roots && c.quotient_chunks.num_roots() == roots && c.permutation.as_ref().is_some_and(|x| x.num_roots() == roots)
            && c.random.is_none() && fri.commit_phase_commits.iter().all(|x| x.num_roots() == roots),
        json!({"separate_random_commitment": c.random.is_some(), "permutation_commitment": c.permutation.is_some()}), &mut checks, &mut errors);
    check("lookup envelope: one terminal (Some), a lookup grinding witness (Some)",
        proof.lookup_terminals.len() == 1 && proof.lookup_terminals[0].is_some() && proof.lookup_pow_witness.is_some(),
        json!({"terminals": proof.lookup_terminals.len(), "lookup_pow_witness": proof.lookup_pow_witness.is_some()}), &mut checks, &mut errors);

    // The partition.
    let commitments = Node::branch("commitments", nb(c), vec![
        cap_node("main", &c.main, c.main.num_roots()),
        opt_cap("permutation", &c.permutation),
        cap_node("quotient_chunks", &c.quotient_chunks, c.quotient_chunks.num_roots()),
        opt_cap("random", &c.random),
    ]);
    let ood = Node::branch("ood_values", nb(ov), vec![
        flat("trace_local", &ov.trace_local, EF_BYTES),
        opt_vec_node("trace_next", &ov.trace_next, EF_BYTES),
        opt_vec_node("preprocessed_local", &pre_local, EF_BYTES),
        opt_vec_node("preprocessed_next", &pre_next, EF_BYTES),
        nested2("quotient_chunks", &ov.quotient_chunks, EF_BYTES),
        opt_vec_node("random", &ov.random, EF_BYTES),
    ]);
    let opened = Node::branch("opened_values", nb(&proof.opened_values), vec![
        Node::leaf("framing_instance_count", vlen(insts.len())),
        Node::branch("instance0", nb(inst), vec![
            ood,
            flat("logup_permutation_local", &inst.permutation_local, EF_BYTES),
            flat("logup_permutation_next", &inst.permutation_next, EF_BYTES),
        ]),
    ]);
    let mut input_nodes = vec![Node::leaf("framing", vlen(fri.input_openings.len()))];
    let mut per_batch = vec![];
    for (i, b) in fri.input_openings.iter().enumerate() {
        let (salts, paths) = &b.opening_proof;
        let digests = paths.sibling_hashes.len();
        let name = BATCHES.get(i).copied().unwrap_or("unexpected");
        input_nodes.push(Node::branch(name, nb(b), vec![
            nested3("opened_rows", &b.opened_values, F_BYTES),
            nested3("salts", salts, F_BYTES),
            Node::branch("merkle_paths", nb(paths), vec![Node::leaf("framing", vlen(digests)), Node::leaf("digests", DIGEST_BYTES * digests)])
                .with("sibling_digests", json!(digests)),
        ]));
        per_batch.push(json!({"batch": i, "tree": name, "matrices": b.opened_values[0].len(),
            "widths": b.opened_values[0].iter().map(Vec::len).collect::<Vec<_>>(), "queries": b.opened_values.len(),
            "tree_log_height": lde, "opened_rows": nb(&b.opened_values), "salts": nb(salts), "merkle_paths": nb(paths), "sibling_digests": digests}));
    }
    let mut round_nodes = vec![Node::leaf("framing", vlen(fri.commit_phase_openings.len()))];
    let mut per_round = vec![];
    let mut height = lde;
    for (r, step) in fri.commit_phase_openings.iter().enumerate() {
        let (salts, paths) = &step.opening_proof;
        let digests = paths.sibling_hashes.len();
        let arity = step.sibling_values[0].len() + 1;
        height -= arity.trailing_zeros() as usize;
        round_nodes.push(Node::branch(&format!("round{r}"), nb(step), vec![
            nested2("sibling_values", &step.sibling_values, EF_BYTES),
            nested3("salts", salts, F_BYTES),
            Node::branch("merkle_paths", nb(paths), vec![Node::leaf("framing", vlen(digests)), Node::leaf("digests", DIGEST_BYTES * digests)])
                .with("sibling_digests", json!(digests)),
        ]));
        per_round.push(json!({"round": r, "arity": arity, "tree_log_height": height, "leaf_width_ef8": arity,
            "sibling_values": nb(&step.sibling_values), "salts": nb(salts), "merkle_paths": nb(paths), "sibling_digests": digests}));
    }
    let fri_node = Node::branch("fri", nb(fri), vec![
        Node::leaf("batch_pow_witness", nb(&fri.batch_pow_witness)),
        Node::branch("commit_phase_commits", nb(&fri.commit_phase_commits), {
            let mut v = vec![Node::leaf("framing", vlen(fri.commit_phase_commits.len()))];
            for (i, cap) in fri.commit_phase_commits.iter().enumerate() {
                v.push(cap_node(&format!("round{i}"), cap, cap.num_roots()));
            }
            v
        }),
        flat("commit_pow_witnesses", &fri.commit_pow_witnesses, F_BYTES),
        Node::branch("input_openings", nb(&fri.input_openings), input_nodes),
        Node::branch("commit_phase_openings", nb(&fri.commit_phase_openings), round_nodes),
        flat("final_poly", &fri.final_poly, EF_BYTES),
        Node::leaf("query_pow_witness", nb(&fri.query_pow_witness)),
    ]);
    let opening = Node::branch("opening_proof", nb(&proof.opening_proof), vec![nested4("random_codeword_ood_values", rcw, EF_BYTES), fri_node]);
    let terminals = Node::branch("lookup_terminals", nb(&proof.lookup_terminals), {
        let mut v = vec![Node::leaf("framing", vlen(proof.lookup_terminals.len()))];
        for (i, t) in proof.lookup_terminals.iter().enumerate() {
            v.push(match t {
                Some(_) => Node::branch(&format!("air{i}"), nb(t), vec![Node::leaf("tag", 1), Node::leaf("value", EF_BYTES)]),
                None => Node::branch(&format!("air{i}"), nb(t), vec![Node::leaf("tag", 1)]),
            });
        }
        v
    });
    let degree_bits = Node::branch("degree_bits", nb(&proof.degree_bits), vec![
        Node::leaf("framing", vlen(proof.degree_bits.len())),
        Node::leaf("values", proof.degree_bits.iter().map(|&d| vlen(d)).sum()),
    ]);
    let lookup_pow = match &proof.lookup_pow_witness {
        Some(x) => Node::branch("lookup_pow_witness", nb(&proof.lookup_pow_witness), vec![Node::leaf("tag", 1), Node::leaf("value", nb(x))]),
        None => Node::branch("lookup_pow_witness", nb(&proof.lookup_pow_witness), vec![Node::leaf("tag", 1)]),
    };
    let root = Node::branch("proof", total, vec![commitments, opened, opening, terminals, degree_bits, lookup_pow,
        Node::leaf("ood_pow_witness", nb(&proof.ood_pow_witness))]);
    let mut tree_errors = vec![];
    let leaves = check_tree(&root, "", &mut tree_errors);
    check("every branch of the partition equals the sum of its parts; the root is the file size", tree_errors.is_empty(),
        json!({"leaves": leaves, "errors": tree_errors}), &mut checks, &mut errors);

    // Component summary (C3b's rows), the input trees split by tree.
    let tree_bytes = |i: usize| -> (usize, usize, usize) {
        fri.input_openings.get(i).map_or((0, 0, 0), |b| (nb(&b.opened_values), nb(&b.opening_proof.0), nb(&b.opening_proof.1)))
    };
    let fri_values: usize = fri.commit_phase_openings.iter().map(|r| nb(&r.sibling_values)).sum();
    let fri_salts: usize = fri.commit_phase_openings.iter().map(|r| nb(&r.opening_proof.0)).sum();
    let fri_paths: usize = fri.commit_phase_openings.iter().map(|r| nb(&r.opening_proof.1)).sum();
    let ood_bytes = nb(ov);
    let logup_bytes = nb(&inst.permutation_local) + nb(&inst.permutation_next);
    let rcw_bytes = nb(rcw);
    let small = json!({"stark_commitments": nb(c), "fri_commit_phase_commits": nb(&fri.commit_phase_commits),
        "pow_witnesses": nb(&fri.batch_pow_witness) + nb(&fri.commit_pow_witnesses) + nb(&fri.query_pow_witness) + nb(&proof.ood_pow_witness),
        "final_poly": nb(&fri.final_poly),
        "vector_framing_input_batches_and_rounds": vlen(fri.input_openings.len()) + vlen(fri.commit_phase_openings.len())});
    let small_total: usize = small.as_object().unwrap().values().map(|v| v.as_u64().unwrap() as usize).sum();
    let envelope = json!({"instance_count": vlen(insts.len()), "lookup_terminals": nb(&proof.lookup_terminals), "lookup_pow_witness": nb(&proof.lookup_pow_witness)});
    let envelope_total: usize = envelope.as_object().unwrap().values().map(|v| v.as_u64().unwrap() as usize).sum();
    let metadata = nb(&proof.degree_bits);
    let mut rows: Vec<(String, usize)> = vec![];
    for (i, name) in BATCHES.iter().enumerate() {
        let (v, s, p) = tree_bytes(i);
        rows.push((format!("input_{name}_opened_rows"), v));
        rows.push((format!("input_{name}_salts"), s));
        rows.push((format!("input_{name}_merkle_paths"), p));
    }
    rows.extend([("fri_sibling_values".to_string(), fri_values), ("fri_salts".into(), fri_salts), ("fri_merkle_paths".into(), fri_paths),
        ("ood_values".into(), ood_bytes), ("logup_ood_values".into(), logup_bytes), ("random_codeword_ood_values".into(), rcw_bytes),
        ("commitments_pow_final_poly_framing".into(), small_total), ("batch_envelope".into(), envelope_total), ("metadata_degree_bits".into(), metadata)]);
    let sum: usize = rows.iter().map(|r| r.1).sum();
    check("component rows sum to the file size", sum == total, json!({"sum": sum, "file": total}), &mut checks, &mut errors);
    let summary: Map<String, Value> = rows.iter().map(|(k, v)| (k.clone(), json!(v))).collect();
    let digests_input: usize = fri.input_openings.iter().map(|b| b.opening_proof.1.sibling_hashes.len()).sum();
    let digests_fri: usize = fri.commit_phase_openings.iter().map(|r| r.opening_proof.1.sibling_hashes.len()).sum();
    let doc = json!({"schema": "l5-layer-b2/breakdown/v1", "review": REVIEW, "tier": TIER, "layout": "C3 with a preprocessed round",
        "file_bytes": total, "file_sha256": sha256_hex(bytes),
        "shape": {"tables": 1, "trace_height": 1usize << spec.log_n, "extended_trace_height": 1usize << (spec.log_n + 1), "lde_log_height": lde,
            "main_width": w, "preprocessed_width": spec.pre_width, "permutation_width_base": spec.perm_width, "quotient_chunks": spec.chunks,
            "input_trees": BATCHES, "fri_rounds": spec.fri_log_arities.len(), "fold_schedule_log_arities": spec.fri_log_arities,
            "queries": K_QUERIES, "final_poly_coefficients": 1usize << K_LOG_FINAL_POLY_LEN},
        "summary": summary, "small_parts": small, "batch_envelope_parts": envelope,
        "sibling_digests": {"input": digests_input, "fri": digests_fri},
        "ood_ef8_values": {"trace_local": ov.trace_local.len(), "trace_next": ov.trace_next.as_ref().map_or(0, Vec::len),
            "preprocessed_local": pre_local.as_ref().map_or(0, Vec::len), "preprocessed_next": pre_next.as_ref().map_or(0, Vec::len),
            "quotient": ov.quotient_chunks.iter().map(Vec::len).sum::<usize>(), "random": ov.random.as_ref().map_or(0, Vec::len),
            "logup_local": inst.permutation_local.len(), "logup_next": inst.permutation_next.len()},
        "random_codeword_points": rcw.iter().map(|r| r.iter().map(|m| m.iter().filter(|p| !p.is_empty()).count()).sum::<usize>()).sum::<usize>(),
        "random_codeword_values": rcw.iter().map(|r| r.iter().map(|m| m.iter().map(Vec::len).sum::<usize>()).sum::<usize>()).sum::<usize>(),
        "per_input_batch": per_batch, "per_fri_round": per_round, "self_checks": checks,
        "all_checks_passed": errors.is_empty(), "tree": root});
    (doc, errors)
}
