//! L5 leaf L0' v2 (2026-10-31): the exact postcard byte breakdown of an L0' v2 proof (C3n) or of the same statement's
//! C3 proof (`breakdown-c3`).
//!
//! Adapted from the L5 size accounting tool (code/l5-size-accounting-20261031/size_accounting.rs, SHA-256
//! d300075a...; its `inner` mode measured the S5 leaf) as L0' v1 adapted it (code/l5-leaf-l0p-20261031/l0p/
//! size_accounting.rs). What changed from L0' v1's tool, and only that:
//! - the input type is `p3_batch_stark_c3n::BatchProof<Config>` (the same wire layout as the C3 type);
//! - a committed trace may be two matrices (C3n's split, `TraceSplit::matrices`): the matrices of a round are taken
//!   from the proof's next-row openings, per instance: none (one matrix at zeta), as many as the trace (one matrix at
//!   both points), or fewer (the next-row matrix at both points, then the rest at zeta). The committed widths of the
//!   input openings check that reading (8 random codewords beyond each OOD width), and the next-row openings are
//!   compared with the layout the verifier derives (C3n: `next_row_columns_for_batch`; C3: every column of every
//!   reading trace, the library default);
//! - every preprocessed trace is one matrix (C3n supports none or every preprocessed column at zeta*g).
//! As in L0' v1: the PCS rounds follow the C3 batch layout (main, then the quotient chunks of every instance followed
//! by each instance's randomization polynomial in one tree, then preprocessed, then permutation); the FRI tree heights
//! are derived with `LOG_BLOWUP`; there is no outer-proof path.
//!
//! Every reported part is the length of the postcard encoding of that sub-value; vector lengths (varints) and
//! `Option` tags appear as explicit `framing` parts. Every branch's own length is computed independently of its
//! parts and compared with their sum, and the root equals the file size. These sum checks guarantee totals and byte
//! coverage, not labels. The table attribution is checked against shared parts computed from the partition's
//! framing leaves, and the matrix-to-table mapping against each matrix's committed width (the random codewords
//! beyond its OOD width in a hiding round, none in the preprocessed round). Nothing is proven or verified and no
//! proof is changed.
//!
//! Usage: `breakdown PROOF OUT.json [METRICS.json]` (C3n layout) | `breakdown-c3 PROOF OUT.json [METRICS.json]`.
//! loop-internal self-review; not independently reviewed.
use super::*;
use std::collections::BTreeMap;
use std::io::{Read as _, Write as _};

use serde::Serialize;
use serde_json::Map;
use sha2::{Digest as _, Sha256};

/// Read bound of this diagnostic tool only; it is not a carrier or protocol bound.
const READ_BOUND: u64 = 16 * 1024 * 1024;
const SCHEMA: &str = "l5-leaf-l0p2/breakdown/v1";

fn encode<T: Serialize + ?Sized>(value: &T) -> Vec<u8> {
    postcard::to_allocvec(value).expect("postcard encoding")
}
fn nbytes<T: Serialize + ?Sized>(value: &T) -> usize {
    encode(value).len()
}
/// Length of a postcard varint (vector lengths and `usize` fields).
fn vlen(n: usize) -> usize {
    nbytes(&n)
}
fn sha256_hex(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}
fn pct(part: usize, total: usize) -> f64 {
    if total == 0 {
        return 0.0;
    }
    (part as f64 * 10_000.0 / total as f64).round() / 100.0
}
fn ms(t: Instant) -> f64 {
    t.elapsed().as_secs_f64() * 1e3
}

/// One node of the byte partition. A branch's `bytes` is the encoded length of the sub-value it
/// stands for, computed independently of its parts; `check_tree` compares the two.
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
    fn leaf(name: impl Into<String>, bytes: usize) -> Self {
        Node { name: name.into(), bytes, info: Map::new(), parts: Vec::new() }
    }
    fn branch(name: impl Into<String>, bytes: usize, parts: Vec<Node>) -> Self {
        Node { name: name.into(), bytes, info: Map::new(), parts }
    }
    fn with(mut self, key: &str, value: Value) -> Self {
        self.info.insert(key.to_string(), value);
        self
    }
}

/// Every branch's parts must sum to its encoded length. Returns the number of leaves.
fn check_tree(node: &Node, path: &str, errors: &mut Vec<String>) -> usize {
    let here = if path.is_empty() { node.name.clone() } else { format!("{path}/{}", node.name) };
    if node.parts.is_empty() {
        return 1;
    }
    let sum: usize = node.parts.iter().map(|p| p.bytes).sum();
    if sum != node.bytes {
        errors.push(format!("{here}: parts sum to {sum}, encoded length is {}", node.bytes));
    }
    node.parts.iter().map(|p| check_tree(p, &here, errors)).sum()
}

/// The encodings of a value's fields, concatenated in declaration order, must equal the encoding of
/// the whole value (postcard writes struct and tuple fields in order with no framing of their own).
fn concat_check(label: &str, whole: &[u8], parts: &[&[u8]], checks: &mut Vec<Value>, errors: &mut Vec<String>) {
    let ok = parts.concat() == whole;
    if !ok {
        errors.push(format!("{label}: field encodings concatenated in order differ from the whole"));
    }
    checks.push(json!({"check": format!("field order: {label}"), "passed": ok}));
}

#[derive(Default)]
struct TableBytes {
    name: String,
    opened_rows: usize,
    opened_rows_by_round: BTreeMap<String, usize>,
    salts: usize,
    ood: usize,
    codeword_ood: usize,
    matrices: usize,
    lookup_terminal: usize,
}

impl TableBytes {
    /// The L5 plan's attribution convention: opened rows + salts + OOD + random-codeword OOD.
    fn total(&self) -> usize {
        self.opened_rows + self.salts + self.ood + self.codeword_ood
    }
}

struct Measured {
    total: usize,
    commitments: usize,
    input_opened_rows: usize,
    input_salts: usize,
    input_paths: usize,
    input_siblings: usize,
    fri_sibling_values: usize,
    fri_salts: usize,
    fri_paths: usize,
    fri_siblings: usize,
    ood: usize,
    codeword_ood: usize,
    lookup_terminals: usize,
    small: Vec<(&'static str, usize)>,
    input_rounds: usize,
    fold_rounds: usize,
    batches: Vec<Value>,
    rounds: Vec<Value>,
    ood_view: Vec<Value>,
    codeword_view: Vec<Value>,
    tables: Vec<TableBytes>,
    input_rows_framing: usize,
    input_salts_framing: usize,
    ood_framing: usize,
    codeword_framing: usize,
    fri_heights: Value,
}

impl Measured {
    fn small_total(&self) -> usize {
        self.small.iter().map(|x| x.1).sum()
    }
    /// The component rows of the L5 plan's Method B table.
    fn rows(&self) -> Vec<(&'static str, &'static str, usize)> {
        vec![
            ("input_opened_rows", "Input openings: opened rows", self.input_opened_rows),
            ("input_salts", "Input salts", self.input_salts),
            ("input_merkle_paths", "Input Merkle paths", self.input_paths),
            ("fri_sibling_values", "FRI sibling values", self.fri_sibling_values),
            ("fri_salts", "FRI salts", self.fri_salts),
            ("fri_merkle_paths", "FRI Merkle paths", self.fri_paths),
            ("ood_opened_values", "OOD opened values", self.ood),
            ("random_codeword_ood", "Random-codeword OOD values", self.codeword_ood),
            (
                "commitments_pow_final_poly_terminals_degree_bits",
                "Commitments, PoW witnesses, final polynomial, lookup terminals, degree bits, 2 B round-count framing",
                self.small_total(),
            ),
        ]
    }
    /// The figures of main.rs `breakdown()` (S5's function, unchanged), recomputed from this partition.
    fn s5_from_parts(&self) -> Value {
        json!({"total": self.total, "commitments": self.commitments, "ood_opened_values": self.ood,
            "random_codeword_openings": self.codeword_ood, "input_openings_values": self.input_opened_rows,
            "input_openings_merkle": self.input_salts + self.input_paths, "fold_sibling_values": self.fri_sibling_values,
            "fold_merkle": self.fri_salts + self.fri_paths, "fold_rounds": self.fold_rounds,
            "input_rounds": self.input_rounds, "lookup_terminals": self.lookup_terminals})
    }
}

/// Measures an L0' `BatchProof<Config>`. The PCS rounds are taken in the order in which the C3 batch verifier
/// builds its opening claims: main, quotient chunks then the randomization polynomials (one tree), preprocessed,
/// permutation, each only when committed.
fn measure(p: &BatchProof<Config>, names: &[String], random_codewords: usize, checks: &mut Vec<Value>,
           errors: &mut Vec<String>) -> (Node, Measured) {
    let inst = &p.opened_values.instances;
    let n = inst.len();
    if names.len() != n {
        errors.push(format!("{} table names for {n} instances", names.len()));
    }
    let name = |i: usize| names.get(i).cloned().unwrap_or_else(|| format!("instance{i}"));
    let mut tables: Vec<TableBytes> = (0..n).map(|i| TableBytes { name: name(i), ..Default::default() }).collect();

    // Commitments.
    let c = &p.commitments;
    if c.random.is_some() {
        errors.push("a separate randomization commitment is present (not the C3 layout)".into());
    }
    let commitments_node = Node::branch("commitments", nbytes(c), vec![
        Node::leaf("main", nbytes(&c.main)).with("cap_roots", json!(c.main.num_roots())),
        Node::leaf("permutation", nbytes(&c.permutation)).with("cap_roots", json!(c.permutation.as_ref().map(|x| x.num_roots()))),
        Node::leaf("quotient_chunks_and_randomization (C3)", nbytes(&c.quotient_chunks)).with("cap_roots", json!(c.quotient_chunks.num_roots())),
        Node::leaf("random (C3: None)", nbytes(&c.random)).with("cap_roots", json!(c.random.as_ref().map(|x| x.num_roots()))),
    ]);

    // Out-of-domain (OOD) values per instance, in the wire order of `OpenedValuesRepr`
    // (p3-uni-stark proof.rs l. 111-126) followed by the two permutation vectors.
    let ood_framing = vlen(n);
    let mut ood_parts = vec![Node::leaf("framing:instance_count", ood_framing)];
    let mut ood_view = Vec::new();
    for (i, x) in inst.iter().enumerate() {
        let b = &x.base_opened_values;
        let fields: Vec<(&str, Vec<u8>, Value)> = vec![
            ("trace_local", encode(&b.trace_local), json!(b.trace_local.len())),
            ("trace_next", encode(&b.trace_next), json!(b.trace_next.as_ref().map(|v| v.len()))),
            ("preprocessed_local", encode(&b.preprocessed_local()), json!(b.preprocessed_local().map(|v| v.len()))),
            ("preprocessed_next", encode(&b.preprocessed_next()), json!(b.preprocessed_next().map(|v| v.len()))),
            ("quotient_chunks", encode(&b.quotient_chunks), json!(b.quotient_chunks.iter().map(|v| v.len()).collect::<Vec<_>>())),
            ("random", encode(&b.random), json!(b.random.as_ref().map(|v| v.len()))),
            ("permutation_local", encode(&x.permutation_local), json!(x.permutation_local.len())),
            ("permutation_next", encode(&x.permutation_next), json!(x.permutation_next.len())),
        ];
        let whole = encode(x);
        concat_check(&format!("OOD instance {i} in wire order"), &whole,
                     &fields.iter().map(|f| f.1.as_slice()).collect::<Vec<_>>(), checks, errors);
        tables[i].ood = whole.len();
        let mut view = Map::new();
        view.insert("instance".into(), json!(i));
        view.insert("table".into(), json!(name(i)));
        view.insert("bytes".into(), json!(whole.len()));
        let mut parts = Vec::new();
        for (field, bytes, count) in fields {
            view.insert(field.into(), json!({"bytes": bytes.len(), "ef_values": count}));
            parts.push(Node::leaf(field, bytes.len()).with("ef_values", count));
        }
        ood_view.push(Value::Object(view));
        ood_parts.push(Node::branch(format!("instance{i}:{}", name(i)), whole.len(), parts));
    }
    let ood_bytes = nbytes(&p.opened_values);
    let ood_node = Node::branch("opened_values_ood", ood_bytes, ood_parts);

    // Round kinds (C3) and, per committed matrix, (instance, OOD values per opening point).
    let has_pre = inst.iter().any(|x| x.base_opened_values.preprocessed.is_some());
    let mut kinds: Vec<&'static str> = vec!["main", "quotient_and_random"];
    if has_pre {
        kinds.push("preprocessed");
    }
    if c.permutation.is_some() {
        kinds.push("permutation");
    }
    let pre_instances: Vec<usize> = (0..n).filter(|&i| inst[i].base_opened_values.preprocessed.is_some()).collect();
    // A trace's committed matrices from its opened widths (C3n's split, `TraceSplit::matrices`): (OOD width, points).
    // No next-row values: one matrix at zeta. As many as at zeta: one matrix at both points. Fewer: the next-row
    // matrix at both points, then the other columns at zeta.
    let split_of = |width: usize, next: Option<usize>| -> Vec<(usize, usize)> {
        match next {
            None | Some(0) => vec![(width, 1)],
            Some(k) if k == width => vec![(width, 2)],
            Some(k) => vec![(k, 2), (width.saturating_sub(k), 1)],
        }
    };
    // (instance, OOD width, is the randomization polynomial, opening points)
    let matrices = |kind: &str| -> Vec<(usize, usize, bool, usize)> {
        match kind {
            "main" => (0..n)
                .flat_map(|i| {
                    let b = &inst[i].base_opened_values;
                    split_of(b.trace_local.len(), b.trace_next.as_ref().map(Vec::len))
                        .into_iter().map(move |(w, pts)| (i, w, false, pts))
                })
                .collect(),
            "quotient_and_random" => (0..n)
                .flat_map(|i| inst[i].base_opened_values.quotient_chunks.iter().map(move |ch| (i, ch.len(), false, 1)))
                .chain((0..n).filter_map(|i| inst[i].base_opened_values.random.as_ref().map(|r| (i, r.len(), true, 1))))
                .collect(),
            // One key matrix per instance: at zeta, and at zeta*g when the proof carries the next row.
            "preprocessed" => pre_instances
                .iter()
                .map(|&i| {
                    let b = &inst[i].base_opened_values;
                    (i, b.preprocessed_local().map_or(0, |v| v.len()), false, 1 + usize::from(b.preprocessed_next().is_some()))
                })
                .collect(),
            "permutation" => (0..n)
                .filter(|&i| !inst[i].permutation_local.is_empty())
                .flat_map(|i| {
                    let next = (!inst[i].permutation_next.is_empty()).then_some(inst[i].permutation_next.len());
                    split_of(inst[i].permutation_local.len(), next).into_iter().map(move |(w, pts)| (i, w, false, pts))
                })
                .collect(),
            _ => Vec::new(),
        }
    };
    // Columns that a committed matrix carries beyond its OOD width: the random codewords in every hiding round
    // (the randomization polynomial included), none in the preprocessed round.
    let extra_of = |kind: &str| -> usize { if kind == "preprocessed" { 0 } else { random_codewords } };

    let (rand_open, fri) = &p.opening_proof;

    // Random-codeword openings at the OOD points (`opening_proof.0`): round -> matrix -> point -> values.
    if rand_open.len() != kinds.len() {
        errors.push(format!("{} random-codeword rounds, expected {:?}", rand_open.len(), kinds));
    }
    let mut codeword_framing = vlen(rand_open.len());
    let mut cw_parts = vec![Node::leaf("framing:round_count", codeword_framing)];
    let mut codeword_view = Vec::new();
    let mut codeword_mismatches: Vec<String> = Vec::new();
    for (r, round) in rand_open.iter().enumerate() {
        let kind = kinds.get(r).copied().unwrap_or("unknown");
        let mats = matrices(kind);
        if mats.len() != round.len() {
            errors.push(format!("random-codeword round {r} ({kind}): {} matrices, expected {}", round.len(), mats.len()));
        }
        codeword_framing += vlen(round.len());
        let mut parts = vec![Node::leaf("framing:matrix_count", vlen(round.len()))];
        let (mut points, mut values) = (0usize, 0usize);
        for (m, mat) in round.iter().enumerate() {
            let bytes = nbytes(mat);
            let owner = mats.get(m).map(|x| x.0);
            let mat_points = mats.get(m).map_or(0, |x| x.3);
            match owner {
                Some(_) if mat.len() == mat_points && mat.iter().all(|v| v.len() == extra_of(kind)) => {}
                Some(i) => codeword_mismatches.push(format!(
                    "random-codeword round {r} ({kind}) matrix {m}: values per point {:?}, expected {mat_points} point(s) of {} values for instance {i}",
                    mat.iter().map(|v| v.len()).collect::<Vec<_>>(), extra_of(kind))),
                None => codeword_mismatches.push(format!("random-codeword round {r} ({kind}) matrix {m}: no instance")),
            }
            if let Some(i) = owner {
                tables[i].codeword_ood += bytes;
            }
            points += mat.len();
            values += mat.iter().map(|v| v.len()).sum::<usize>();
            parts.push(Node::leaf(format!("matrix{m}"), bytes)
                .with("instance", json!(owner))
                .with("randomization_polynomial", json!(mats.get(m).map(|x| x.2)))
                .with("ef_values_per_point", json!(mat.iter().map(|v| v.len()).collect::<Vec<_>>())));
        }
        let rb = nbytes(round);
        codeword_view.push(json!({"round": r, "kind": kind, "bytes": rb, "matrices": round.len(), "points": points, "ef_values": values}));
        cw_parts.push(Node::branch(format!("round{r}:{kind}"), rb, parts));
    }
    let codeword_bytes = nbytes(rand_open);
    let cw_node = Node::branch("random_codeword_openings", codeword_bytes, cw_parts);

    // FRI input openings: one batch per PCS round, all queries sharing one pruned multiproof.
    let nb = fri.input_openings.len();
    if nb != kinds.len() {
        errors.push(format!("{nb} input batches, expected rounds {kinds:?}"));
    }
    let mut in_parts = vec![Node::leaf("framing:batch_count", vlen(nb))];
    let mut batches = Vec::new();
    let (mut input_opened_rows, mut input_salts, mut input_paths, mut input_siblings) = (0, 0, 0, 0);
    let (mut input_rows_framing, mut input_salts_framing) = (0usize, 0usize);
    let mut width_mismatches: Vec<String> = Vec::new();
    for (bi, o) in fri.input_openings.iter().enumerate() {
        let kind = kinds.get(bi).copied().unwrap_or("unknown");
        let mats = matrices(kind);
        let rows = &o.opened_values;
        let q = rows.len();
        let widths: Vec<usize> = rows.first().map(|r| r.iter().map(|v| v.len()).collect()).unwrap_or_default();
        if rows.iter().any(|r| r.len() != widths.len() || r.iter().zip(&widths).any(|(v, w)| v.len() != *w)) {
            errors.push(format!("input batch {bi}: row widths differ between queries"));
        }
        if mats.len() != widths.len() {
            errors.push(format!("input batch {bi} ({kind}): {} matrices, expected {}", widths.len(), mats.len()));
        }
        let rows_framing = vlen(q) + rows.iter().map(|r| vlen(r.len())).sum::<usize>();
        let mut vparts = vec![Node::leaf("framing:query_count_and_per_query_matrix_count", rows_framing)];
        let mut hiding = Vec::new();
        for (m, &w) in widths.iter().enumerate() {
            let bytes: usize = rows.iter().map(|r| r.get(m).map_or(0, |v| nbytes(v))).sum();
            let prefix: usize = rows.iter().map(|r| r.get(m).map_or(0, |v| vlen(v.len()))).sum();
            let owner = mats.get(m).map(|x| x.0);
            // An EF8 OOD value of the randomization polynomial is one committed base column per coordinate:
            // the OOD vector carries the 8 coordinates as 8 extension values, so its OOD width is 8.
            let extra = mats.get(m).map(|x| w as i64 - x.1 as i64);
            if extra != Some(extra_of(kind) as i64) {
                width_mismatches.push(format!(
                    "input batch {bi} ({kind}) matrix {m}: committed width {w}, OOD width {:?} of instance {owner:?}, expected {} columns beyond it",
                    mats.get(m).map(|x| x.1), extra_of(kind)));
            }
            hiding.push(extra);
            if let Some(i) = owner {
                tables[i].opened_rows += bytes;
                *tables[i].opened_rows_by_round.entry(kind.to_string()).or_default() += bytes;
                tables[i].matrices += 1;
            }
            vparts.push(Node::leaf(format!("matrix{m}"), bytes)
                .with("instance", json!(owner))
                .with("randomization_polynomial", json!(mats.get(m).map(|x| x.2)))
                .with("width", json!(w))
                .with("columns_beyond_ood_width", json!(extra))
                .with("row_length_prefix_bytes", json!(prefix))
                .with("value_bytes", json!(bytes - prefix)));
        }
        let salts = &o.opening_proof.0;
        let salt_widths: Vec<usize> = salts.first().map(|r| r.iter().map(|s| s.len()).collect()).unwrap_or_default();
        if salts.len() != q || salt_widths.len() != widths.len() {
            errors.push(format!("input batch {bi}: salt shape {}x{} differs from the opened rows {q}x{}", salts.len(), salt_widths.len(), widths.len()));
        }
        let salts_framing = vlen(salts.len()) + salts.iter().map(|r| vlen(r.len())).sum::<usize>();
        let mut sparts = vec![Node::leaf("framing:query_count_and_per_query_matrix_count", salts_framing)];
        for m in 0..salt_widths.len() {
            let bytes: usize = salts.iter().map(|r| r.get(m).map_or(0, |s| nbytes(s))).sum();
            let owner = mats.get(m).map(|x| x.0);
            if let Some(i) = owner {
                tables[i].salts += bytes;
            }
            sparts.push(Node::leaf(format!("matrix{m}"), bytes)
                .with("instance", json!(owner))
                .with("salt_elements", json!(salt_widths[m])));
        }
        let paths = &o.opening_proof.1;
        let ns = paths.sibling_hashes.len();
        let digest_bytes: usize = paths.sibling_hashes.iter().map(|d| nbytes(d)).sum();
        let (vb, sb, pb, ob) = (nbytes(rows), nbytes(salts), nbytes(paths), nbytes(o));
        input_opened_rows += vb;
        input_salts += sb;
        input_paths += pb;
        input_siblings += ns;
        input_rows_framing += rows_framing;
        input_salts_framing += salts_framing;
        batches.push(json!({"batch": bi, "kind": kind, "bytes": ob, "opened_values": vb, "salts": sb, "merkle_paths": pb,
            "sibling_digests": ns, "queries": q, "matrices": widths.len(), "widths": widths,
            "columns_beyond_ood_width": hiding, "salt_elements": salt_widths,
            "instances": mats.iter().map(|x| x.0).collect::<Vec<_>>(),
            "ood_widths": mats.iter().map(|x| x.1).collect::<Vec<_>>(),
            "opening_points": mats.iter().map(|x| x.3).collect::<Vec<_>>(),
            "randomization_polynomial": mats.iter().map(|x| x.2).collect::<Vec<_>>()}));
        in_parts.push(Node::branch(format!("batch{bi}:{kind}"), ob, vec![
            Node::branch("opened_values", vb, vparts),
            Node::branch("salts", sb, sparts),
            Node::branch("merkle_paths", pb, vec![
                Node::leaf("framing:digest_count", vlen(ns)),
                Node::leaf("sibling_digests", digest_bytes),
            ]).with("sibling_digests", json!(ns)),
        ]).with("queries", json!(q)));
    }
    let inputs_node = Node::branch("input_openings", nbytes(&fri.input_openings), in_parts);

    let width_ok = width_mismatches.is_empty();
    checks.push(json!({"check": format!("matrix-to-table mapping: every hiding-round matrix (the randomization polynomials included) is {random_codewords} columns (its random codewords) wider than its instance's OOD width, every preprocessed-round matrix exactly as wide"),
        "passed": width_ok, "random_codewords": random_codewords, "mismatches": width_mismatches}));
    errors.extend(width_mismatches);
    let codeword_ok = codeword_mismatches.is_empty();
    checks.push(json!({"check": format!("matrix-to-table mapping: every random-codeword opening has its instance's opening points, with {random_codewords} values per point in a hiding round and none in the preprocessed round"),
        "passed": codeword_ok, "mismatches": codeword_mismatches}));
    errors.extend(codeword_mismatches);

    // FRI commit-phase rounds. The tree heights are derived from the tallest committed height, max degree bits +
    // LOG_BLOWUP (the proof does not carry log_blowup).
    let max_degree_bits = p.degree_bits.iter().copied().max().unwrap_or(0);
    let mut height = max_degree_bits + LOG_BLOWUP;
    let fri_heights = json!({"start_log_height": height, "max_degree_bits": max_degree_bits, "log_blowup": LOG_BLOWUP,
        "log_blowup_source": "L0' constant LOG_BLOWUP (main.rs); the proof does not carry log_blowup",
        "rule": "each round's tree log height is the previous height minus log2 of its arity (p3-fri verifier: log_folded_height = log_current_height - log_arity)"});
    let mut cp_parts = vec![Node::leaf("framing:round_count", vlen(fri.commit_phase_openings.len()))];
    let mut rounds = Vec::new();
    let (mut fri_sibling_values, mut fri_salts, mut fri_paths, mut fri_siblings) = (0, 0, 0, 0);
    for (r, s) in fri.commit_phase_openings.iter().enumerate() {
        let sv = &s.sibling_values;
        let q = sv.len();
        let a1 = sv.first().map_or(0, |v| v.len());
        if sv.iter().any(|v| v.len() != a1) {
            errors.push(format!("FRI round {r}: sibling-value counts differ between queries"));
        }
        let arity = a1 + 1;
        height = height.saturating_sub(arity.trailing_zeros() as usize);
        let sv_framing = vlen(q) + sv.iter().map(|v| vlen(v.len())).sum::<usize>();
        let sv_values: usize = sv.iter().flat_map(|v| v.iter()).map(|x| nbytes(x)).sum();
        let salts = &s.opening_proof.0;
        let salt_framing = vlen(salts.len())
            + salts.iter().map(|row| vlen(row.len()) + row.iter().map(|x| vlen(x.len())).sum::<usize>()).sum::<usize>();
        let salt_values: usize = salts.iter().flat_map(|row| row.iter()).flat_map(|x| x.iter()).map(|e| nbytes(e)).sum();
        let paths = &s.opening_proof.1;
        let ns = paths.sibling_hashes.len();
        let digest_bytes: usize = paths.sibling_hashes.iter().map(|d| nbytes(d)).sum();
        let (svb, sb, pb, rb) = (nbytes(sv), nbytes(salts), nbytes(paths), nbytes(s));
        fri_sibling_values += svb;
        fri_salts += sb;
        fri_paths += pb;
        fri_siblings += ns;
        rounds.push(json!({"round": r, "arity": arity, "derived_tree_log_height": height, "log_blowup_used": LOG_BLOWUP,
            "bytes": rb, "sibling_values": svb, "salts": sb, "merkle_paths": pb, "sibling_digests": ns, "queries": q,
            "commitment_cap_roots": fri.commit_phase_commits.get(r).map(|x| x.num_roots())}));
        cp_parts.push(Node::branch(format!("round{r}"), rb, vec![
            Node::branch("sibling_values", svb, vec![
                Node::leaf("framing:query_count_and_per_query_count", sv_framing),
                Node::leaf("ef_values", sv_values),
            ]),
            Node::branch("salts", sb, vec![
                Node::leaf("framing:query_matrix_and_element_counts", salt_framing),
                Node::leaf("salt_elements", salt_values),
            ]),
            Node::branch("merkle_paths", pb, vec![
                Node::leaf("framing:digest_count", vlen(ns)),
                Node::leaf("sibling_digests", digest_bytes),
            ]),
        ]).with("arity", json!(arity)).with("derived_tree_log_height", json!(height)).with("sibling_digests", json!(ns)));
    }
    let cp_node = Node::branch("commit_phase_openings", nbytes(&fri.commit_phase_openings), cp_parts);

    let fri_whole = encode(fri);
    concat_check("FriProof", &fri_whole, &[
        encode(&fri.batch_pow_witness).as_slice(),
        encode(&fri.commit_phase_commits).as_slice(),
        encode(&fri.commit_pow_witnesses).as_slice(),
        encode(&fri.input_openings).as_slice(),
        encode(&fri.commit_phase_openings).as_slice(),
        encode(&fri.final_poly).as_slice(),
        encode(&fri.query_pow_witness).as_slice(),
    ], checks, errors);
    let fri_node = Node::branch("fri_proof", fri_whole.len(), vec![
        Node::leaf("batch_pow_witness", nbytes(&fri.batch_pow_witness)),
        Node::leaf("commit_phase_commits", nbytes(&fri.commit_phase_commits))
            .with("commitments", json!(fri.commit_phase_commits.len()))
            .with("cap_roots_each", json!(fri.commit_phase_commits.iter().map(|x| x.num_roots()).collect::<Vec<_>>())),
        Node::leaf("commit_pow_witnesses", nbytes(&fri.commit_pow_witnesses)).with("witnesses", json!(fri.commit_pow_witnesses.len())),
        inputs_node,
        cp_node,
        Node::leaf("final_poly", nbytes(&fri.final_poly)).with("ef_coefficients", json!(fri.final_poly.len())),
        Node::leaf("query_pow_witness", nbytes(&fri.query_pow_witness)),
    ]);
    let opening_whole = encode(&p.opening_proof);
    concat_check("PCS proof tuple (random-codeword openings, FriProof)", &opening_whole,
                 &[encode(rand_open).as_slice(), fri_whole.as_slice()], checks, errors);
    let opening_node = Node::branch("opening_proof", opening_whole.len(), vec![cw_node, fri_node]);

    // Lookup terminals, one per instance.
    let mut lt_parts = vec![Node::leaf("framing:count", vlen(p.lookup_terminals.len()))];
    for (i, t) in p.lookup_terminals.iter().enumerate() {
        let b = nbytes(t);
        if let Some(tb) = tables.get_mut(i) {
            tb.lookup_terminal = b;
        }
        lt_parts.push(Node::leaf(format!("instance{i}"), b).with("present", json!(t.is_some())));
    }
    let lookup_terminals = nbytes(&p.lookup_terminals);
    let lt_node = Node::branch("lookup_terminals", lookup_terminals, lt_parts);

    let whole = encode(p);
    concat_check("BatchProof", &whole, &[
        encode(&p.commitments).as_slice(),
        encode(&p.opened_values).as_slice(),
        opening_whole.as_slice(),
        encode(&p.lookup_terminals).as_slice(),
        encode(&p.degree_bits).as_slice(),
        encode(&p.lookup_pow_witness).as_slice(),
        encode(&p.ood_pow_witness).as_slice(),
    ], checks, errors);
    let commitments = nbytes(c);
    let tree = Node::branch("proof", whole.len(), vec![
        commitments_node,
        ood_node,
        opening_node,
        lt_node,
        Node::leaf("degree_bits", nbytes(&p.degree_bits)).with("values", json!(p.degree_bits)),
        Node::leaf("lookup_pow_witness", nbytes(&p.lookup_pow_witness)).with("present", json!(p.lookup_pow_witness.is_some())),
        Node::leaf("ood_pow_witness", nbytes(&p.ood_pow_witness)),
    ]);
    let small = vec![
        ("commitments (main, permutation, quotient chunks and randomization, random tag)", commitments),
        ("FRI commit-phase commitments", nbytes(&fri.commit_phase_commits)),
        ("PoW witness: FRI batch", nbytes(&fri.batch_pow_witness)),
        ("PoW witnesses: FRI commit phase", nbytes(&fri.commit_pow_witnesses)),
        ("PoW witness: FRI query", nbytes(&fri.query_pow_witness)),
        ("PoW witness: lookup (Option)", nbytes(&p.lookup_pow_witness)),
        ("PoW witness: OOD", nbytes(&p.ood_pow_witness)),
        ("final polynomial", nbytes(&fri.final_poly)),
        ("lookup terminals", lookup_terminals),
        ("degree bits", nbytes(&p.degree_bits)),
        ("framing: input-batch count and FRI-round count", vlen(nb) + vlen(fri.commit_phase_openings.len())),
    ];
    let measured = Measured {
        total: whole.len(), commitments, input_opened_rows, input_salts, input_paths, input_siblings,
        fri_sibling_values, fri_salts, fri_paths, fri_siblings, ood: ood_bytes, codeword_ood: codeword_bytes,
        lookup_terminals, small, input_rounds: nb, fold_rounds: fri.commit_phase_openings.len(), batches, rounds,
        ood_view, codeword_view, tables, input_rows_framing, input_salts_framing, ood_framing, codeword_framing,
        fri_heights,
    };
    (tree, measured)
}

/// Per-table attribution with the L5 plan's convention, plus the composition of the shared rest (unchanged from
/// the source tool: the shared parts are computed directly, never as a residual).
fn attribution(m: &Measured, total: usize, checks: &mut Vec<Value>, errors: &mut Vec<String>) -> Value {
    let attributed: usize = m.tables.iter().map(TableBytes::total).sum();
    let t_rows: usize = m.tables.iter().map(|t| t.opened_rows).sum();
    let t_salts: usize = m.tables.iter().map(|t| t.salts).sum();
    let t_ood: usize = m.tables.iter().map(|t| t.ood).sum();
    let t_cw: usize = m.tables.iter().map(|t| t.codeword_ood).sum();
    for (label, category, tables, framing) in [
        ("input opened rows", m.input_opened_rows, t_rows, m.input_rows_framing),
        ("input salts", m.input_salts, t_salts, m.input_salts_framing),
        ("OOD values", m.ood, t_ood, m.ood_framing),
        ("random-codeword OOD values", m.codeword_ood, t_cw, m.codeword_framing),
    ] {
        let ok = tables + framing == category;
        if !ok {
            errors.push(format!("table attribution, {label}: tables {tables} + framing leaves {framing} != encoded length {category}"));
        }
        checks.push(json!({"check": format!("table attribution, {label}: the tables' bytes plus the framing leaves equal the category's encoded length"),
            "passed": ok, "tables": tables, "framing_leaves": framing, "encoded_length": category}));
    }
    let shared_parts: Vec<(&str, usize)> = vec![
        ("input Merkle paths", m.input_paths),
        ("FRI commit phase: sibling values, salts and Merkle paths", m.fri_sibling_values + m.fri_salts + m.fri_paths),
        ("commitments, PoW witnesses, final polynomial, lookup terminals, degree bits, 2 B round-count framing", m.small_total()),
        ("framing: input opened rows (query count, per-query matrix count)", m.input_rows_framing),
        ("framing: input salts (query count, per-query matrix count)", m.input_salts_framing),
        ("framing: OOD instance count", m.ood_framing),
        ("framing: random-codeword round and matrix counts", m.codeword_framing),
    ];
    let shared: usize = shared_parts.iter().map(|x| x.1).sum();
    let ok = attributed + shared == total;
    if !ok {
        errors.push(format!("table attribution: attributed {attributed} + shared parts {shared} != file size {total}"));
    }
    checks.push(json!({"check": "table attribution plus the independently computed shared parts equals the file size", "passed": ok,
        "attributed": attributed, "shared": shared, "total": total}));
    let tables: Vec<Value> = m.tables.iter().enumerate().map(|(i, t)| {
        json!({"instance": i, "table": t.name, "bytes": t.total(), "share_percent": pct(t.total(), total),
            "opened_rows": t.opened_rows, "opened_rows_by_round": t.opened_rows_by_round, "salts": t.salts,
            "ood": t.ood, "codeword_ood": t.codeword_ood, "committed_matrices": t.matrices,
            "lookup_terminal_bytes_counted_in_shared": t.lookup_terminal})
    }).collect();
    json!({
        "convention": "as in the L5 plan's second table: a table's bytes are the opened-row bytes of its committed matrices (each row with its length prefix), their salts, its OOD block and its random-codeword OOD entries; everything else (Merkle paths, FRI, commitments, PoW witnesses, final polynomial, lookup terminals, degree bits and query/round-level framing) is shared",
        "tables": tables,
        "shared": {"bytes": shared, "share_percent": pct(shared, total),
            "computed_from": "the sum of its parts, each computed directly (category encodings and the partition's framing leaves); not a residual of the file size",
            "parts": shared_parts.iter().map(|(k, v)| json!({"part": k, "bytes": v, "share_percent": pct(*v, total)})).collect::<Vec<_>>()},
    })
}

/// The next-row openings a proof carries, per instance: (main, preprocessed, permutation) value counts (`None`:
/// absent). For C3n the layout the verifier derives; for C3 the library default (every column of every main trace,
/// since no AIR here narrows `main_next_row_columns`; every preprocessed column; every permutation column).
fn expected_next_counts(c3: bool) -> (Vec<(Option<usize>, Option<usize>, usize)>, Value) {
    let b = build();
    let data = keygen(&b);
    let layout = next_rows(&b, &data.common);
    let counts = layout.iter().map(|l| {
        let perm = l.permutation_split(8);
        if c3 {
            (Some(l.main_width), (l.preprocessed_width > 0).then_some(l.preprocessed_width), perm.width)
        } else {
            (l.main_split().next_len(), l.preprocessed_split().next_len(), perm.next.len())
        }
    }).collect();
    (counts, next_rows_record(&layout))
}

fn report(bytes: &[u8], metrics: Option<&Path>, c3: bool, checks: &mut Vec<Value>, errors: &mut Vec<String>) -> Map<String, Value> {
    let t = Instant::now();
    let p: BatchProof<Config> = decode_strict(bytes).expect("strict decode with the L0' verifier's decoder");
    let decode_ms = ms(t);
    let t = Instant::now();
    let reencoded = encode(&p);
    let names: Vec<String> = TABLES.iter().map(|s| s.to_string()).collect();
    let (root, m) = measure(&p, &names, RANDOM_CODEWORDS, checks, errors);
    let total = bytes.len();
    let mut out = Map::new();
    out.insert("type".into(), json!("p3_batch_stark_c3n::BatchProof<Config> (L0' v2 configuration; the C3 type has the same wire layout)"));
    out.insert("layout".into(), json!(if c3 { "C3 (p3_batch_stark_c3: every next-row column of a reading trace opened)" } else { "C3n (p3_batch_stark_c3n: next-row subset openings)" }));
    out.insert("decoder".into(), json!("decode_strict (main.rs, the L0' verify mode's decoder): postcard 1.1.3 take_from_bytes, trailing bytes rejected"));
    out.insert("table_names_source".into(), json!("S5 instance order FieldOp, BytePair, Keccak, Sha (main.rs build_with and prove_with)"));
    // The proof's next-row openings against the layout its verifier derives.
    let (expected, derived) = expected_next_counts(c3);
    let got: Vec<(Option<usize>, Option<usize>, usize)> = p.opened_values.instances.iter().map(|x| {
        let o = &x.base_opened_values;
        (o.trace_next.as_ref().map(Vec::len), o.preprocessed_next().map(|v| v.len()), x.permutation_next.len())
    }).collect();
    let layout_ok = got == expected;
    if !layout_ok {
        errors.push(format!("next-row openings {got:?} differ from the expected layout {expected:?}"));
    }
    checks.push(json!({"check": "the proof's next-row openings (main, preprocessed, permutation counts per table) equal the layout its verifier expects",
        "passed": layout_ok, "proof": got, "expected": expected}));
    out.insert("derived_next_row_columns".into(), derived);
    let identical = reencoded == bytes;
    if !identical {
        errors.push("re-encoding of the decoded proof differs from the input".into());
    }
    checks.insert(0, json!({"check": "re-encoding the decoded value gives the input bytes", "passed": identical,
        "input_sha256": sha256_hex(bytes), "reencoded_sha256": sha256_hex(&reencoded), "reencoded_bytes": reencoded.len()}));
    let before = errors.len();
    let leaves = check_tree(&root, "", errors);
    checks.push(json!({"check": "every branch of the byte partition equals the sum of its parts", "passed": errors.len() == before, "leaves": leaves}));
    let root_ok = root.bytes == total;
    if !root_ok {
        errors.push(format!("partition root {} != file size {total}", root.bytes));
    }
    checks.push(json!({"check": "the partition root equals the file size", "passed": root_ok, "root": root.bytes, "file": total}));
    let rows = m.rows();
    let rows_sum: usize = rows.iter().map(|x| x.2).sum();
    let rows_ok = rows_sum == total;
    if !rows_ok {
        errors.push(format!("component rows sum to {rows_sum}, file has {total}"));
    }
    checks.push(json!({"check": "the component rows sum to the file size", "passed": rows_ok, "sum": rows_sum, "file": total}));
    let summary: Vec<Value> = rows.iter()
        .map(|(k, l, b)| json!({"key": k, "component": l, "bytes": b, "share_percent": pct(*b, total)}))
        .collect();
    out.insert("summary".into(), json!(summary));
    out.insert("summary_sibling_digest_counts".into(), json!({"input": m.input_siblings, "fri": m.fri_siblings}));
    out.insert("small_components".into(), json!(m.small.iter().map(|(k, v)| json!({"component": k, "bytes": v})).collect::<Vec<_>>()));
    out.insert("per_input_batch".into(), json!(m.batches));
    out.insert("per_fri_round".into(), json!(m.rounds));
    out.insert("fri_tree_heights".into(), m.fri_heights.clone());
    out.insert("ood_per_instance".into(), json!(m.ood_view));
    out.insert("random_codeword_ood_per_round".into(), json!(m.codeword_view));
    let s5_fn = breakdown(&p);
    let s5_parts = m.s5_from_parts();
    let same = s5_fn == s5_parts;
    if !same {
        errors.push("main.rs breakdown() differs from this partition".into());
    }
    checks.push(json!({"check": "main.rs breakdown() (S5's function) equals the same figures summed from this partition", "passed": same}));
    let mut s5 = Map::new();
    s5.insert("by_breakdown_fn".into(), s5_fn.clone());
    s5.insert("from_this_partition".into(), s5_parts.clone());
    if let Some(path) = metrics {
        let recorded: Value = serde_json::from_slice(&fs::read(path).expect("metrics.json")).expect("metrics.json is JSON");
        let reference = recorded["breakdown"].as_object().cloned().unwrap_or_default();
        let mut cmp = Vec::new();
        let mut all = !reference.is_empty();
        for (key, want) in &reference {
            let ok = &s5_fn[key] == want && &s5_parts[key] == want;
            all &= ok;
            cmp.push(json!({"figure": key, "metrics_json": want, "breakdown_fn": s5_fn[key], "this_partition": s5_parts[key], "equal": ok}));
        }
        let size_ok = recorded["proof_bytes"] == json!(bytes.len());
        if !all || !size_ok {
            errors.push("metrics.json breakdown not reproduced".into());
        }
        checks.push(json!({"check": "metrics.json breakdown figures reproduced (breakdown() and this partition)", "passed": all && size_ok,
            "figures": reference.len(), "proof_bytes_equal": size_ok}));
        s5.insert("metrics_json_comparison".into(), json!(cmp));
    }
    out.insert("s5_style_breakdown".into(), Value::Object(s5));
    out.insert("table_attribution".into(), attribution(&m, total, checks, errors));
    out.insert("tree".into(), serde_json::to_value(&root).unwrap());
    out.insert("timings_ms".into(), json!({"decode": decode_ms, "measure_and_checks": ms(t)}));
    out
}

fn read_input(path: &Path) -> Vec<u8> {
    let mut bytes = Vec::new();
    fs::File::open(path).expect("input proof").take(READ_BOUND + 1).read_to_end(&mut bytes).expect("read input proof");
    assert!(bytes.len() as u64 <= READ_BOUND, "input exceeds this tool's diagnostic read bound");
    bytes
}

fn run(proof: &str, out: &str, metrics: Option<&str>, c3: bool) {
    let start = Instant::now();
    let out = Path::new(out);
    assert!(!out.exists(), "output file exists; outputs are never overwritten");
    let bytes = read_input(Path::new(proof));
    let read_ms = ms(start);
    let mut checks = Vec::new();
    let mut errors = Vec::new();
    let body = report(&bytes, metrics.map(Path::new), c3, &mut checks, &mut errors);
    let mut doc = Map::new();
    doc.insert("schema".into(), json!(SCHEMA));
    doc.insert("review".into(), json!(REVIEW));
    doc.insert("tier".into(), json!(TIER));
    doc.insert("n".into(), json!(1));
    doc.insert("input".into(), json!({"path": proof, "bytes": bytes.len(), "sha256": sha256_hex(&bytes)}));
    doc.insert("configuration".into(), config_record());
    doc.insert("all_checks_passed".into(), json!(errors.is_empty()));
    doc.insert("errors".into(), json!(errors));
    doc.insert("self_checks".into(), json!(checks));
    for (k, v) in body {
        doc.insert(k, v);
    }
    doc.insert("resources".into(), json!({"read_ms": read_ms, "total_ms_before_write": ms(start), "peak_rss_kib": peak_rss_kib()}));
    let encoded = serde_json::to_vec_pretty(&Value::Object(doc)).unwrap();
    fs::OpenOptions::new().write(true).create_new(true).open(out).and_then(|mut f| f.write_all(&encoded)).expect("fresh output file");
    event(json!({"stage": "breakdown_done", "input_bytes": bytes.len(), "input_sha256": sha256_hex(&bytes),
        "all_checks_passed": errors.is_empty(), "checks": checks.len(), "errors": errors, "peak_rss_kib": peak_rss_kib(),
        "elapsed_ms": ms(start)}));
    assert!(errors.is_empty(), "a size-accounting self-check failed");
}

/// `c3`: the input is the same statement's C3 proof (mode `breakdown-c3`), checked against the C3 layout.
pub fn cli(args: &[&str], c3: bool) {
    match args {
        [proof, out] => run(proof, out, None, c3),
        [proof, out, metrics] => run(proof, out, Some(*metrics), c3),
        _ => panic!("usage: breakdown[-c3] PROOF OUT.json [METRICS.json]"),
    }
}
