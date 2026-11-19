//! F1's trace-level negatives (L5 layer F1, 2026-11-01): B1's trace-level negatives (code/l5-layer-b1-20261031/b1/
//! variants.rs, module paths renamed), applied to F's trace for B: the ones that apply to B as a child are kept; the
//! others (two buses, roll-ins, a lower input tree, a constant final polynomial, the g1b children) are left out because B
//! has none of them. Added: U6's A (leaf link), B (position) and C (transcript IV) and a wrong claim (G1's and B2's
//! variants, ported to the write port of B1's kernel), and new ones for the interfaces F needs and B1's child did not
//! have: a C3 child's batch seed (no next-row bitmaps), a child prefix holding B's verifier-key digest and the
//! statement, a final polynomial of 4 coefficients, B's preprocessed columns and public values as program inputs, and
//! a natively invalid B. Each variant starts from F's honest trace for B's proof (or uses a B proof made for it) and
//! edits it, and where stated the statement; the Poseidon2Air columns are regenerated from the edited inputs, so every
//! row is a correct permutation; the base lane, the payloads, the DEEP lane, the bus memory, the ALU, the write port,
//! the reserved rows' operands and the controls are re-derived from the edited rows unless the variant edits them
//! itself. Then every constraint of F is evaluated on every row and the bus is counted exactly (`fkernel::check`); a
//! variant is rejected by constraints when a constraint group fails or the bus does not balance, and its targeted group
//! must be among the violated ones. Nothing is proven.
//! The machinery (`instr`, `writer_of`, `reader_of`, `rebind`, `transcript_with`, the expectation format) is G1's.
//! Research measurement; loop-internal self-review; not independently reviewed.
use std::collections::{BTreeMap, BTreeSet};

use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_koala_bear::KoalaBear as F;
use serde_json::{Value, json};

use crate::fkernel::CAP_BITS;
use crate::fschedule::{Schedule, Src, TreeKind, Val};
use crate::ftracegen::{ChildData, DeepEdits, E8, Hooks, KTrace, derive, end_columns, hi_of, kernel_query_elements, memory, no_hooks, run_alu, set_all_acc};

/// The query the single-path variants edit.
pub const VQ: usize = 5;
/// The claim the claim variant edits (G1's).
pub const VCLAIM: usize = 40;

pub const ALL: &[&str] = &[
    "P",
    // U6's three bindings and a wrong claim (G1's and B2's, on B1's write port)
    "A", "B", "C", "claim_write",
    // a C3 child (the batch seed without next-row bitmaps) and B's prefix (B's verifier-key digest; the statement twice)
    "seed_constant", "prefix_vk_digest", "prefix_omitted", "statement_public_value",
    // a final polynomial of 4 coefficients
    "final_coeff_read",
    // B's AIR in the program: a main-trace input, a preprocessed input, a public value
    "program_input_read", "program_pre_read", "public_value_unpack",
    // the 23-bit index lane and the caps; the joined DEEP chains of B's quotient tree
    "cap_entry_read", "index_high_bit", "deep_pass",
];

/// The child-level variants (each with a B proof made for it): a natively invalid B.
pub const CHILD_LEVEL: &[&str] = &["corpus_b_invalid"];

#[derive(Clone, Debug)]
pub struct Expected {
    pub expect: &'static str,
    pub target: &'static str,
    pub exact: Option<Vec<String>>,
    pub roles: Option<Vec<String>>,
    pub child_level: bool,
    pub honest: Vec<String>,
}

fn ex(expect: &'static str, target: &'static str) -> Expected {
    Expected { expect, target, exact: None, roles: None, child_level: false, honest: vec![] }
}
fn only(expect: &'static str, target: &'static str, exact: &[&str]) -> Expected {
    Expected { exact: Some(exact.iter().map(|s| s.to_string()).collect()), ..ex(expect, target) }
}
fn roles(mut e: Expected, r: &[&str]) -> Expected {
    e.roles = Some(r.iter().map(|s| s.to_string()).collect());
    e
}
fn child_only(target: &'static str, exact: &[&str], r: Option<&[&str]>) -> Expected {
    let mut e = Expected { child_level: true, ..only("reject", target, exact) };
    if let Some(r) = r {
        e = roles(e, r);
    }
    e
}

pub fn expected(variant: &str) -> Expected {
    match variant {
        "P" => only("accept", "-", &[]),
        "A" => ex("reject", "merkle.link"),
        "B" => ex("reject", "merkle.cap"),
        "C" => ex("reject", "transcript.iv"),
        "claim_write" => ex("reject", "claim.write"),
        "seed_constant" => ex("reject", "transcript.const"),
        "prefix_vk_digest" => ex("reject", "transcript.const"),
        "prefix_omitted" => ex("reject", "transcript.const"),
        "statement_public_value" => only("reject", "transcript.public", &["transcript.public"]),
        "final_coeff_read" => roles(only("reject", "bus.balance", &["alu.eq", "bus.balance"]), &["fri.final"]),
        "program_input_read" => roles(only("reject", "bus.balance", &["alu.eq", "bus.balance"]), &["eval.identity"]),
        "program_pre_read" => roles(only("reject", "bus.balance", &["alu.eq", "bus.balance"]), &["eval.identity"]),
        "public_value_unpack" => ex("reject", "alu.unpack"),
        "cap_entry_read" => ex("reject", "merkle.cap"),
        "index_high_bit" => ex("reject", "index.end_recompose"),
        "deep_pass" => ex("reject", "deep.pass"),
        "corpus_b_invalid" => child_only("alu.eq:eval.identity", &["alu.eq"], Some(&["eval.identity"])),
        _ => panic!("unknown variant {variant}"),
    }
}

pub fn exact_met(e: &Expected, names: &[String], roles: &BTreeMap<String, BTreeSet<String>>) -> bool {
    match &e.exact {
        None => true,
        Some(list) => {
            let mut a = names.to_vec();
            a.sort();
            let mut b = list.clone();
            b.sort();
            let allowed: Option<Vec<String>> = e.roles.clone().or_else(|| e.target.split_once(':').map(|(_, r)| vec![r.to_string()]));
            let roles_ok = match allowed {
                None => true,
                Some(al) => roles.values().all(|rs| rs.iter().all(|r| al.contains(r))),
            };
            a == b && roles_ok
        }
    }
}

pub fn target_met(e: &Expected, names: &[String], roles: &BTreeMap<String, BTreeSet<String>>) -> bool {
    let hit = match e.target {
        "-" => true,
        t => match t.split_once(':') {
            Some((g, role)) => names.iter().any(|n| n == g) && roles.get(g).is_some_and(|r| r.contains(role)),
            None => names.iter().any(|n| n == t),
        },
    };
    hit && exact_met(e, names, roles)
}

fn instr(s: &Schedule, role: &str, q: usize, r: Option<usize>, nth: usize) -> usize {
    s.program
        .iter()
        .enumerate()
        .filter(|(_, i)| i.role == role && i.query == Some(q) && i.round == r)
        .nth(nth)
        .map(|(k, _)| k)
        .unwrap_or_else(|| panic!("no instruction {role} q{q} r{r:?} #{nth}"))
}
fn writer_of(s: &Schedule, v: Val) -> usize {
    s.program.iter().position(|i| i.r == Some(v)).unwrap_or_else(|| panic!("no instruction writes {v:?}"))
}
fn reader_of(s: &Schedule, v: Val, role: Option<&str>) -> (usize, usize) {
    s.program
        .iter()
        .enumerate()
        .find_map(|(i, ins)| {
            if role.is_some_and(|r| r != ins.role) {
                return None;
            }
            [ins.a, ins.b, ins.c].iter().position(|o| *o == Some(v)).map(|slot| (i, slot))
        })
        .unwrap_or_else(|| panic!("no instruction ({role:?}) reads {v:?}"))
}

/// Query elements as the kernel reads them, accumulators from them (bits unchanged), everything derived.
fn rebind(kt: &mut KTrace, s: &Schedule) -> Vec<F> {
    let xs = kernel_query_elements(kt, s);
    set_all_acc(kt, s, &xs);
    derive(kt, s, &no_hooks());
    xs
}

/// The transcript inputs from the child's values with an override per (row, lane).
fn transcript_with(s: &Schedule, d: &ChildData, pv: &[F], over: &dyn Fn(usize, usize, F) -> F) -> Vec<[F; 16]> {
    let pre = crate::ftracegen::pre_cap_override(s, &d.pre_cap);
    let mut prev = d.init;
    let mut rows = Vec::with_capacity(s.trows.len());
    for (r, row) in s.trows.iter().enumerate() {
        let mut x = prev;
        if row.k > 0 {
            for l in 0..8 {
                let v = match row.lanes[l].unwrap() {
                    Src::Const(v) => pre.get(&(r, l)).copied().unwrap_or(v),
                    Src::Pub(j) => pv[j],
                    Src::Wit(i) => d.wit[i],
                };
                x[l] = over(r, l, v);
            }
            x[8] += F::from_usize(row.k);
        }
        rows.push(x);
        prev = crate::ftracegen::perm(x);
    }
    rows
}

/// Apply a variant; returns the description of the edit. `pv` is the statement the prover claims.
pub fn apply(variant: &str, kt: &mut KTrace, s: &Schedule, d: &ChildData, x: &[F], pv: &mut [F]) -> Value {
    let mem0 = memory(kt, s, &|_, _| {});
    let mut honest_mem = mem0.clone();
    {
        let mut kc = kt.clone();
        run_alu(&mut kc, s, &mut honest_mem, &no_hooks());
    }
    let quot_t = s.trees.iter().position(|t| t.kind == TreeKind::Input(1)).unwrap();
    let main_t = s.canon();
    let p = &s.child.program;
    match variant {
        // ---- U6's three bindings (G1's variants A, B, C, as B2 ported them) ----
        "A" => {
            let t = &s.trees[main_t];
            let g0 = s.group_row(VQ, main_t, 0);
            let w = t.groups[0].leaf_len - s.child.salt;
            for e in 0..w {
                kt.inp[g0 + e / 8][e % 8] = F::from_u32(777_000 + e as u32);
            }
            kt.rechain(s, g0 + 1..g0 + t.groups[0].lh_rows);
            derive(kt, s, &no_hooks());
            json!({"edit": format!("U6 A (leaf link): query 5, B's main tree: the opened row ({w} values with the random codewords) replaced by 777000 + i in the leaf-hash rows, the leaf sponge rechained; the compression rows unchanged (the genuine path from the genuine leaf digest); the DEEP lane, the claims' reduction and the ALU follow the changed rows"),
                "first_leaf_row": g0, "leaf_rows": t.groups[0].lh_rows})
        }
        "B" => {
            let q2 = (0..s.q).find(|&q| q != VQ && d.idx[quot_t][q] != d.idx[quot_t][VQ]).unwrap();
            let (b5, b6) = (s.block_start[VQ][quot_t], s.block_start[q2][quot_t]);
            for j in 0..s.trees[quot_t].block_len {
                kt.inp[b5 + j] = kt.inp[b6 + j];
                kt.bit[b5 + j] = kt.bit[b6 + j];
            }
            set_all_acc(kt, s, x);
            derive(kt, s, &no_hooks());
            json!({"edit": format!("U6 B (position): query 5, B's quotient tree: every row of the block (the leaf rows, the compressions) and the direction bits copied from query {q2} (the genuine opening of index {} under B's quotient cap); the accumulator from query 5's element", d.idx[quot_t][q2]),
                "transcript_index_query5": d.idx[quot_t][VQ], "block_rows": [b5, b5 + s.trees[quot_t].block_len]})
        }
        "C" => {
            kt.inp[0][8] = F::from_u32(1 + s.air.k0 as u32);
            for l in 9..16 {
                kt.inp[0][l] = F::from_u32((l - 7) as u32);
            }
            kt.rechain(s, 1..s.t_rows);
            let x2 = rebind(kt, s);
            json!({"edit": "U6 C (transcript IV): transcript row 0's capacity (1, 2, ..., 8) plus the length tag; the transcript rechained from it; query elements, accumulators, challenges, the DEEP lane and the ALU follow it; openings unchanged",
                "query_elements_changed": x2.iter().zip(x).filter(|(a, b)| a != b).count()})
        }
        // ---- a wrong claim (G1's), through B1's write port ----
        "claim_write" => {
            let rp = move |v: Val, e: &mut E8| {
                if v == Val::Claim(VCLAIM) {
                    e[0] += F::ONE;
                }
            };
            derive(kt, s, &Hooks { rport: &rp, ..no_hooks() });
            let pp = s.claim_pos[VCLAIM];
            json!({"edit": format!("a wrong claim: claim {VCLAIM}'s write row puts the absorbed claim plus one on the bus through the write port R (every reader reads that value); the transcript is unchanged"), "row": pp.row, "lane": pp.lane})
        }
        // ---- a C3 child and B's prefix ----
        "seed_constant" => {
            let sg = s.segments.iter().find(|g| g.name == "batch.seed").expect("the batch seed's absorption");
            let pos = s.ev_pos[sg.first_event];
            let inputs = transcript_with(s, d, pv, &|r, l, v| if (r, l) == pos { v + F::ONE } else { v });
            kt.inp[..s.t_rows].copy_from_slice(&inputs);
            let x2 = rebind(kt, s);
            json!({"edit": "a C3 child's batch seed (p3_batch_stark_c3's BatchShape, no next-row bitmaps): the transcript absorbs its first element plus one (a constant the verifier pins); everything after it follows the changed transcript; openings unchanged",
                "seed_elements": sg.len, "row": pos.0, "lane": pos.1, "query_elements_changed": x2.iter().zip(x).filter(|(a, b)| a != b).count()})
        }
        "prefix_vk_digest" => {
            let sg = s.segments.iter().find(|g| g.name == "prefix.b_vk_digest").expect("B's verifier-key digest's absorption");
            // Event 0 of a byte absorption is its length; event 1 its byte 0.
            let pos = s.ev_pos[sg.first_event + 1];
            let inputs = transcript_with(s, d, pv, &|r, l, v| if (r, l) == pos { v + F::ONE } else { v });
            kt.inp[..s.t_rows].copy_from_slice(&inputs);
            let x2 = rebind(kt, s);
            json!({"edit": "B's prefix: the transcript absorbs B's verifier-key digest with its byte 0 plus one (a prefix constant the verifier pins: B's identity); everything after it follows the changed transcript; openings unchanged",
                "row": pos.0, "lane": pos.1, "query_elements_changed": x2.iter().zip(x).filter(|(a, b)| a != b).count()})
        }
        "prefix_omitted" => {
            let (ev, segs, _, _) = crate::fschedule::events(&s.child, &s.trees);
            let drop: Vec<(usize, usize)> = segs.iter().filter(|g| g.name == "prefix.b_vk_digest").map(|g| (g.first_event, g.first_event + g.len)).collect();
            assert_eq!(drop.len(), 1);
            let ev2: Vec<_> = ev.iter().enumerate().filter(|(i, _)| !drop.iter().any(|&(a, b)| *i >= a && *i < b)).map(|(_, e)| *e).collect();
            let (rows2, _) = crate::fschedule::simulate(&ev2);
            let value = |src: Src| -> F {
                match src {
                    Src::Const(v) => v,
                    Src::Pub(j) => pv[j],
                    Src::Wit(i) => d.wit[i],
                }
            };
            let inputs = crate::ftracegen::transcript_rows_from(&rows2, &value, d.init);
            let t2 = inputs.len();
            kt.inp[..t2].copy_from_slice(&inputs);
            for r in t2..s.t_rows {
                kt.inp[r] = kt.out(r - 1);
            }
            rebind(kt, s);
            json!({"edit": "the prover's transcript omits B's verifier-key digest's absorption (its length and 32 bytes): its duplex rows in rows 0.., squeeze-only rows after them; query elements, accumulators, challenges, the DEEP lane and the ALU as the kernel reads them; openings unchanged",
                "omitted_elements": drop[0].1 - drop[0].0, "malicious_transcript_rows": t2, "scheduled_transcript_rows": s.t_rows})
        }
        "statement_public_value" => {
            pv[3] = F::from_u8((pv[3].as_canonical_u32() as u8) ^ 1);
            json!({"edit": "statement: public value 3 (PI198 byte 3), bit 0 flipped; trace unchanged (B's prefix and B's batch public values absorb it, both pinned by transcript.public)"})
        }
        // ---- a final polynomial of 4 coefficients ----
        "final_coeff_read" => {
            let i = s.program.iter().position(|ins| ins.role == "fri.final_horner" && ins.query == Some(VQ)).expect("the final Horner");
            let coeff = s.program[i].a.expect("operand a");
            assert!(matches!(coeff, Val::Coeff(_)), "the first Horner step reads the top coefficient");
            let ops = move |k: usize, o: &mut [E8; 3]| {
                if k == i {
                    o[0][0] += F::ONE;
                }
            };
            derive(kt, s, &Hooks { operands: &ops, ..no_hooks() });
            json!({"edit": format!("query 5: the final polynomial's first Horner step reads {coeff:?} plus one at the coefficient's address (address column honest); the Horner chain follows it"), "instruction": i, "row": s.instr_row[i]})
        }
        // ---- B's AIR in the program ----
        "program_input_read" | "program_pre_read" => {
            let t = 0;
            let want_pre = variant == "program_pre_read";
            let (inp, (i, slot)) = p
                .inputs
                .iter()
                .filter(|(_, x)| if want_pre { matches!(x, crate::compiler::Input::PreLocal(tt, _) if *tt == t) } else { matches!(x, crate::compiler::Input::TraceLocal(tt, _) if *tt == t) })
                .find_map(|(id, x)| {
                    let v = s.input_val[id];
                    s.program.iter().enumerate().find_map(|(k, ins)| {
                        (ins.role == "eval.constraint").then(|| [ins.a, ins.b, ins.c].iter().position(|o| *o == Some(v)).map(|sl| (k, sl))).flatten()
                    }).map(|r| (*x, r))
                })
                .expect("a constraint instruction reading the input");
            let ops = move |k: usize, o: &mut [E8; 3]| {
                if k == i {
                    o[slot][0] += F::ONE;
                }
            };
            derive(kt, s, &Hooks { operands: &ops, ..no_hooks() });
            json!({"edit": format!("a wrong program input: the first constraint instruction that reads B's opened {} {inp:?} reads it plus one at its claim's address (address column honest)", if want_pre { "preprocessed value" } else { "main-trace value" }),
                "instruction": i, "row": s.instr_row[i]})
        }
        "public_value_unpack" => {
            let i = s.program.iter().position(|ins| ins.op == crate::fkernel::Op::Unpack).expect("an UNPACK of a public value");
            let res = move |k: usize, r: &mut E8| {
                if k == i {
                    r[0] += F::ONE;
                }
            };
            derive(kt, s, &Hooks { result: &res, ..no_hooks() });
            json!({"edit": format!("a wrong public value in the program: the first UNPACK ({:?}, from its transcript row's absorbed lane) writes the lane plus one; B's constraints at zeta read it", s.program[i].r), "instruction": i, "row": s.instr_row[i]})
        }
        // ---- the index lane, the caps, the DEEP chains ----
        "cap_entry_read" => {
            let cr = s.cap_read_row(VQ, quot_t);
            let cap = crate::ftracegen::cap_of(x[VQ]);
            let other = (cap + 1) % (1 << CAP_BITS);
            for k in 0..CAP_BITS {
                kt.hb[cr][k] = F::from_u32((other >> k) & 1);
            }
            derive(kt, s, &no_hooks());
            json!({"edit": format!("query 5's quotient-tree cap read takes entry {other} instead of {cap} (its cap bits HB[0..5], index bits 18..22, set to {other}; the address follows them)"), "row": cr})
        }
        "index_high_bit" => {
            let canon = s.canon();
            let end = s.end_row(VQ, canon);
            let hi = hi_of(x[VQ]) ^ (1 << 7);
            let (hb, tp) = end_columns(hi);
            kt.hb[end] = hb;
            kt.tp[end] = tp;
            derive(kt, s, &no_hooks());
            json!({"edit": "query 5's canonical end row decomposes its accumulator with bit 30 of the query element flipped (HB[7], the running products consistent with it); the high part it writes and every cap read of query 5 follow it", "row": end})
        }
        "deep_pass" => {
            let ci = s.chains.iter().position(|c| !c.pass_rows.is_empty()).expect("a joined chain");
            let ch = &s.chains[ci];
            let row = s.group_row(VQ, ch.tree, ch.group) + ch.pass_rows[0];
            derive(kt, s, &Hooks { deep: DeepEdits { pass: Some((row, F::ONE)), ..Default::default() }, ..no_hooks() });
            json!({"edit": format!("query 5, B's {} tree: the first salt row of a joined DEEP chain (matrices {:?}) passes the next row's sum plus one instead of the sum", s.trees[ch.tree].name, ch.matrices), "row": row})
        }
        other => panic!("unknown variant {other}"),
    }
}
