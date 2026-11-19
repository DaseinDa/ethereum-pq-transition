//! B2's negatives (L5 layer B2, 2026-11-01): B1's trace-level negatives (one or more per interface that L0' v2 needs
//! and G1's child did not have, on the g1b child and at full scale on L0' v2) re-run on B2's layout; new ones for B2's
//! mechanisms (the second write slot W2, the injection read slot RI); and the variants B2 also proves at full scale
//! (U6's A leaf link, B position and C transcript IV, a wrong claim, a natively invalid L0' v2 child). Each variant starts from the honest
//! B trace of a g1b child (or uses a child proven for it) and edits it, and where stated the statement; the Poseidon2Air
//! columns are regenerated from the edited inputs, so every row is a correct permutation; the base lane, the payloads,
//! the DEEP lane, the bus memory, the ALU, the write port, the reserved rows' operands and the controls are re-derived
//! from the edited rows unless the variant edits them itself. Then every constraint of B is evaluated on every row and
//! the bus is counted exactly (`kernel::check`); a variant is rejected by constraints when a constraint group fails or
//! the bus does not balance, and its targeted group must be among the violated ones. The prove mode proves the same
//! edited trace and the kernel proof's verifier must reject it.
//! The machinery (`instr`, `writer_of`, `reader_of`, `rebind`, `transcript_with`, the expectation format) and the
//! variants A, B, C, claim_write, cap_multiplicity and injection_right are G1's (code/l5-kernel-g1-20261031/g1/variants.rs),
//! ported to B2's slots.
//! Research prototype; loop-internal self-review; not independently reviewed.
use std::collections::{BTreeMap, BTreeSet};

use p3_field::{Field, PrimeCharacteristicRing, PrimeField32};
use p3_koala_bear::KoalaBear as F;
use serde_json::{Value, json};

use crate::kernel::CAP_BITS;
use crate::schedule::{Node, Schedule, Src, TreeKind, Val};
use crate::tracegen::{ChildData, DeepEdits, E8, Hooks, KTrace, derive, end_columns, hi_of, kernel_query_elements, memory, no_hooks, run_alu, set_all_acc};

/// The query the single-path variants edit.
pub const VQ: usize = 5;
/// The claim the claim variants edit (G1's).
pub const VCLAIM: usize = 40;

pub const ALL: &[&str] = &[
    "P",
    // L0' v2's kind of prefix (constants only) and the statement as the tables' public values
    "prefix_constant", "prefix_omitted", "statement_public_value",
    // the constant final polynomial
    "final_constant_read",
    // roll-ins after arity-2 rounds
    "rollin_power_arity2", "rollin_read_arity2",
    // joined DEEP chains through their salt rows (the lever)
    "deep_pass",
    // several LogUp buses
    "lookup_bus_prefix", "lookup_bus_read",
    // the 23-bit index lane
    "cap_entry_read", "per_tree_index_width", "index_high_bit",
    // a program input of the table with the most constraints (on L0' v2: the Keccak table)
    "program_input_read",
    // child level: the terminal check over two buses; the identity of the 2^16 table
    "corpus_lookup_unbalanced", "corpus_cell_c",
    // B2: U6's three bindings, a wrong claim, and B2's new slots (W2: claims, DEEP sums, high parts, cap multiplicities;
    // RI: the injected digest)
    "A", "B", "C", "claim_write", "w2_deep_write", "w2_hi_write", "cap_multiplicity", "injection_right",
];

/// The same edits at full scale on B's own trace for L0' v2 (trace level; L0' v2 has no input tree lower than 2^23, so
/// no shifted path start, and no natively invalid child).
pub const ALL_L0P2: &[&str] = &[
    "prefix_constant", "prefix_omitted", "statement_public_value", "final_constant_read", "rollin_power_arity2", "rollin_read_arity2",
    "deep_pass", "lookup_bus_prefix", "lookup_bus_read", "cap_entry_read", "index_high_bit", "program_input_read",
    // B2
    "A", "B", "C", "claim_write", "w2_deep_write", "w2_hi_write", "cap_multiplicity", "injection_right",
];

/// The variants B2 proves at full scale on L0' v2 (each edit made on B's trace for L0' v2 before the unmodified prover
/// commits; the child-level one is the natively invalid L0' v2 child's honest B trace).
pub const PROVE_L0P2: &[&str] = &["P", "A", "B", "C", "claim_write", "corpus_l0p2_cell"];

/// The children the children stage proves: (directory, arguments of `b1 g1b-child`).
pub const CHILDREN: &[(&str, &str)] = &[("child", ""), ("corpus-lookup-unbalanced", "--unbalanced 5"), ("corpus-cell-c", "--cell 2,30000,1")];

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
        "prefix_constant" => ex("reject", "transcript.const"),
        "prefix_omitted" => ex("reject", "transcript.const"),
        "statement_public_value" => only("reject", "transcript.public", &["transcript.public"]),
        "final_constant_read" => roles(only("reject", "alu.eq:fri.final", &["alu.eq", "bus.balance"]), &["fri.final"]),
        "rollin_power_arity2" => ex("reject", "alu.mul:fri.rollin_power"),
        "rollin_read_arity2" => ex("reject", "bus.balance"),
        "deep_pass" => ex("reject", "deep.pass"),
        "lookup_bus_prefix" => ex("reject", "alu.lin:eval.lookup_challenge"),
        "lookup_bus_read" => roles(only("reject", "bus.balance", &["alu.eq", "bus.balance"]), &["eval.identity"]),
        "cap_entry_read" => ex("reject", "merkle.cap"),
        "per_tree_index_width" => ex("reject", "bus.balance"),
        "index_high_bit" => ex("reject", "index.end_recompose"),
        "program_input_read" => roles(only("reject", "bus.balance", &["alu.eq", "bus.balance"]), &["eval.identity"]),
        "corpus_lookup_unbalanced" => child_only("alu.eq:eval.terminal_sum", &["alu.eq"], Some(&["eval.terminal_sum"])),
        "corpus_cell_c" => child_only("alu.eq:eval.identity", &["alu.eq"], Some(&["eval.identity"])),
        // B2
        "A" => ex("reject", "merkle.link"),
        "B" => ex("reject", "merkle.cap"),
        "C" => ex("reject", "transcript.iv"),
        "claim_write" => ex("reject", "claim.write"),
        "w2_deep_write" => ex("reject", "deep.write"),
        "w2_hi_write" => ex("reject", "index.hi_write"),
        "cap_multiplicity" => only("reject", "bus.balance", &["bus.balance"]),
        "injection_right" => only("reject", "bus.balance", &["bus.balance"]),
        "corpus_l0p2_cell" => child_only("alu.eq:eval.identity", &["alu.eq"], Some(&["eval.identity"])),
        _ => panic!("unknown variant {variant}"),
    }
}

pub fn child_dir(variant: &str) -> &'static str {
    match variant {
        "corpus_lookup_unbalanced" => "corpus-lookup-unbalanced",
        "corpus_cell_c" => "corpus-cell-c",
        "corpus_l0p2_cell" => "l0p2-cell",
        _ => "child",
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
    let pre = crate::tracegen::pre_cap_override(s, &d.pre_cap);
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
        prev = crate::tracegen::perm(x);
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
    let main_t = s.canon();
    let quot_t = s.trees.iter().position(|t| t.kind == TreeKind::Input(1)).unwrap();
    let perm_t = s.trees.iter().position(|t| t.kind == TreeKind::Input(3)).unwrap();
    let p = &s.child.program;
    match variant {
        // ---- B2: U6's three bindings (G1's variants A, B, C), on B's layout ----
        "A" => {
            let t = &s.trees[main_t];
            let g0 = s.group_row(VQ, main_t, 0);
            let w = t.groups[0].leaf_len - s.child.salt;
            for e in 0..w {
                kt.inp[g0 + e / 8][e % 8] = F::from_u32(777_000 + e as u32);
            }
            kt.rechain(s, g0 + 1..g0 + t.groups[0].lh_rows);
            derive(kt, s, &no_hooks());
            json!({"edit": format!("U6 A (leaf link): query 5, main tree: the tallest group's opened row ({w} values) replaced by 777000 + i in the leaf-hash rows, the leaf sponge rechained; the compression rows unchanged (the genuine path from the genuine leaf digest); the DEEP lane, the claims' reduction and the ALU follow the changed rows"),
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
            json!({"edit": format!("U6 B (position): query 5, quotient tree: every row of the block (the groups' leaf rows, the compressions, the injections) and the direction bits copied from query {q2} (the genuine opening of index {} under the quotient cap); the accumulator from query 5's element", d.idx[quot_t][q2]),
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
        // ---- B2: a wrong claim; the second write slot W2 and the injection read slot RI ----
        "claim_write" => {
            let rp = move |v: Val, e: &mut E8| {
                if v == Val::Claim(VCLAIM) {
                    e[0] += F::ONE;
                }
            };
            derive(kt, s, &Hooks { w2: &rp, ..no_hooks() });
            let pp = s.claim_pos[VCLAIM];
            json!({"edit": format!("a wrong claim: claim {VCLAIM}'s write row puts the absorbed claim plus one on the bus through W2 (every reader reads that value); the transcript is unchanged"), "row": pp.row, "lane": pp.lane})
        }
        "w2_deep_write" => {
            let rp = move |v: Val, e: &mut E8| {
                if v == Val::SD(VQ, 0) {
                    e[0] += F::ONE;
                }
            };
            derive(kt, s, &Hooks { w2: &rp, ..no_hooks() });
            let row = s.w2port.iter().find(|(_, v)| *v == Val::SD(VQ, 0)).unwrap().0;
            json!({"edit": "W2: query 5's first DEEP chain sum written through W2 as the lane's sum plus one (its reader reads that value)", "row": row})
        }
        "w2_hi_write" => {
            let rp = move |v: Val, e: &mut E8| {
                if v == Val::Hi(VQ) {
                    e[0] += F::ONE;
                }
            };
            derive(kt, s, &Hooks { w2: &rp, ..no_hooks() });
            let row = s.w2port.iter().find(|(_, v)| *v == Val::Hi(VQ)).unwrap().0;
            json!({"edit": "W2: query 5's high part written through W2 as the decomposed value plus one (every cap read of query 5 reads that value)", "row": row})
        }
        "cap_multiplicity" => {
            derive(kt, s, &no_hooks());
            let (row, v) = s.w2port.iter().find(|(r, v)| matches!(v, Val::Cap(t, _) if *t == quot_t) && kt.mw[*r] != F::ZERO).copied().unwrap();
            kt.mw[row] += F::ONE;
            json!({"edit": format!("a wrong cap multiplicity: {v:?} written through W2 with its read count plus one (the prover's free multiplicity, main column MW)"), "row": row})
        }
        "injection_right" => {
            let t = &s.trees[main_t];
            let b0 = s.block_start[VQ][main_t];
            let (o, _) = t.nodes.iter().find(|(_, n)| matches!(n, Node::Inj(_))).copied().expect("an injection in the main tree");
            let r = b0 + o;
            kt.inp[r][8] += F::ONE;
            kt.rechain(s, r + 1..b0 + t.cap_read + 1);
            derive(kt, s, &no_hooks());
            json!({"edit": "RI: query 5, main tree, first injection row: the injected digest's element 0 (input lane 8) plus one, the read through RI follows the lanes; later nodes rechained (the cap read reads the path's node)", "row": r})
        }
        "prefix_constant" => {
            let sg = s.segments.iter().find(|g| g.name == "prefix.air_digest").expect("the AIR digest's absorption");
            // Event 0 of a byte absorption is its length; event 1 its byte 0.
            let pos = s.ev_pos[sg.first_event + 1];
            let inputs = transcript_with(s, d, pv, &|r, l, v| if (r, l) == pos { v + F::ONE } else { v });
            kt.inp[..s.t_rows].copy_from_slice(&inputs);
            let x2 = rebind(kt, s);
            json!({"edit": "the transcript absorbs the child's AIR digest with its byte 0 plus one (a prefix constant the verifier pins); everything after it follows the changed transcript; openings unchanged",
                "row": pos.0, "lane": pos.1, "query_elements_changed": x2.iter().zip(x).filter(|(a, b)| a != b).count()})
        }
        "prefix_omitted" => {
            let (ev, segs, _, _) = crate::schedule::events(&s.child, &s.trees);
            let drop: Vec<(usize, usize)> = segs.iter().filter(|g| g.name == "prefix.descriptor").map(|g| (g.first_event, g.first_event + g.len)).collect();
            assert_eq!(drop.len(), 1);
            let ev2: Vec<_> = ev.iter().enumerate().filter(|(i, _)| !drop.iter().any(|&(a, b)| *i >= a && *i < b)).map(|(_, e)| *e).collect();
            let (rows2, _) = crate::schedule::simulate(&ev2);
            let value = |src: Src| -> F {
                match src {
                    Src::Const(v) => v,
                    Src::Pub(j) => pv[j],
                    Src::Wit(i) => d.wit[i],
                }
            };
            let inputs = crate::tracegen::transcript_rows_from(&rows2, &value, d.init);
            let t2 = inputs.len();
            kt.inp[..t2].copy_from_slice(&inputs);
            for r in t2..s.t_rows {
                kt.inp[r] = kt.out(r - 1);
            }
            rebind(kt, s);
            json!({"edit": "the prover's transcript omits the descriptor's absorption (its length and entries): its duplex rows in rows 0.., squeeze-only rows after them; query elements, accumulators, challenges, the DEEP lane and the ALU as the kernel reads them; openings unchanged",
                "omitted_elements": drop[0].1 - drop[0].0, "malicious_transcript_rows": t2, "scheduled_transcript_rows": s.t_rows})
        }
        "statement_public_value" => {
            pv[3] = F::from_u8((pv[3].as_canonical_u32() as u8) ^ 1);
            json!({"edit": "statement: table B's public value 3 (PI198 byte 3), bit 0 flipped; trace unchanged"})
        }
        "final_constant_read" => {
            let i = s.program.iter().position(|ins| ins.role == "fri.final" && ins.query == Some(VQ)).expect("the final check");
            assert_eq!(s.program[i].a, Some(Val::Coeff(0)), "the final check reads the constant first");
            let ops = move |k: usize, o: &mut [E8; 3]| {
                if k == i {
                    o[0][0] += F::ONE;
                }
            };
            derive(kt, s, &Hooks { operands: &ops, ..no_hooks() });
            json!({"edit": "query 5: the final check (the constant final polynomial against the last fold) reads the constant plus one at the constant's address (address column honest)", "instruction": i, "row": s.instr_row[i]})
        }
        "rollin_power_arity2" => {
            let (&r0, &h) = s.rollins.iter().find(|(r, _)| s.child.fri_log_arities[**r] == 1).expect("a roll-in after an arity-2 round");
            let i = writer_of(s, Val::BetaPow(r0));
            let b = honest_mem[&Val::Beta(r0)];
            let res = move |k: usize, r: &mut E8| {
                if k == i {
                    *r = b;
                }
            };
            derive(kt, s, &Hooks { result: &res, ..no_hooks() });
            json!({"edit": format!("a wrong roll-in power after an arity-2 round: beta_{r0}^2 (the factor of the height-{h} roll-in after round {r0}) computed as beta_{r0}; every roll-in after round {r0} uses it"), "instruction": i, "row": s.instr_row[i]})
        }
        "rollin_read_arity2" => {
            let (&r0, &h) = s.rollins.iter().find(|(r, _)| s.child.fri_log_arities[**r] == 1).expect("a roll-in after an arity-2 round");
            let i = instr(s, "fri.rollin_add", VQ, Some(r0 + 1), 0);
            let h_other = *s.rollins.values().find(|&&hh| hh != h).unwrap();
            let other = honest_mem[&Val::RO(VQ, h_other, s.hz.iter().filter(|x| x.0 == h_other).count() - 1)];
            let ops = move |k: usize, o: &mut [E8; 3]| {
                if k == i {
                    o[1] = other;
                }
            };
            derive(kt, s, &Hooks { operands: &ops, ..no_hooks() });
            json!({"edit": format!("query 5: the height-{h} roll-in after the arity-2 round {r0} reads the height-{h_other} reduced opening's value at the height-{h} one's address (address column honest)"), "instruction": i, "row": s.instr_row[i]})
        }
        "deep_pass" => {
            let ci = s.chains.iter().position(|c| !c.pass_rows.is_empty()).expect("a joined chain");
            let ch = &s.chains[ci];
            let row = s.group_row(VQ, ch.tree, ch.group) + ch.pass_rows[0];
            derive(kt, s, &Hooks { deep: DeepEdits { pass: Some((row, F::ONE)), ..Default::default() }, ..no_hooks() });
            json!({"edit": format!("query 5, {} tree: the first salt row of a joined DEEP chain (matrices {:?}) passes the next row's sum plus one instead of the sum", s.trees[ch.tree].name, ch.matrices), "row": row})
        }
        "lookup_bus_prefix" => {
            assert!(p.prefixes.len() >= 2, "two buses");
            let i = writer_of(s, Val::Ev(p.prefixes[1]));
            let p0 = honest_mem[&Val::Ev(p.prefixes[0])];
            let res = move |k: usize, r: &mut E8| {
                if k == i {
                    *r = p0;
                }
            };
            derive(kt, s, &Hooks { result: &res, ..no_hooks() });
            json!({"edit": "a wrong bus prefix: bus 1's prefix alpha_L + 2 gamma computed as bus 0's alpha_L + gamma; every LogUp term of bus 1 reads it", "instruction": i, "row": s.instr_row[i]})
        }
        "lookup_bus_read" => {
            assert!(p.prefixes.len() >= 2, "two buses");
            let v1 = Val::Ev(p.prefixes[1]);
            let (i, slot) = reader_of(s, v1, Some("eval.constraint"));
            let p0 = honest_mem[&Val::Ev(p.prefixes[0])];
            let ops = move |k: usize, o: &mut [E8; 3]| {
                if k == i {
                    o[slot] = p0;
                }
            };
            derive(kt, s, &Hooks { operands: &ops, ..no_hooks() });
            json!({"edit": "a lookup on the wrong bus: the first constraint instruction that reads bus 1's prefix reads bus 0's prefix value at bus 1's address (address column honest)", "instruction": i, "row": s.instr_row[i]})
        }
        "cap_entry_read" => {
            let cr = s.cap_read_row(VQ, quot_t);
            let cap = crate::tracegen::cap_of(x[VQ]);
            let other = (cap + 1) % (1 << CAP_BITS);
            for k in 0..CAP_BITS {
                kt.hb[cr][k] = F::from_u32((other >> k) & 1);
            }
            derive(kt, s, &no_hooks());
            json!({"edit": format!("23-bit indices: query 5's quotient-tree cap read takes entry {other} instead of {cap} (its cap bits HB[0..5], index bits 18..22, set to {other}; the address follows them)"), "row": cr})
        }
        "per_tree_index_width" => {
            let ps = s.path_start(VQ, perm_t);
            let full = x[VQ];
            let skip = s.trees[perm_t].skip;
            let cons = s.air.pidx.cons;
            let end = s.end_row(VQ, perm_t);
            let mut a = full;
            for r in ps..=end {
                kt.acc[r] = a;
                kt.xq[r] = full;
                if s.air.pre[cons][r] == F::ONE {
                    a = (a - kt.bit[r]) * F::TWO.inverse();
                }
            }
            derive(kt, s, &no_hooks());
            json!({"edit": format!("23-bit indices, a wrong per-tree index width: query 5's permutation-tree path (height 2^{}, index = query element >> {skip}) starts its accumulator at the query element itself (bits unchanged)", s.trees[perm_t].log_height), "row": ps})
        }
        "index_high_bit" => {
            let canon = s.canon();
            let end = s.end_row(VQ, canon);
            let hi = hi_of(x[VQ]) ^ (1 << 7);
            let (hb, tp) = end_columns(hi);
            kt.hb[end] = hb;
            kt.tp[end] = tp;
            derive(kt, s, &no_hooks());
            json!({"edit": "23-bit indices: query 5's canonical end row decomposes its accumulator with bit 30 of the query element flipped (HB[7], the running products consistent with it); the high part it writes and every cap read of query 5 follow it", "row": end})
        }
        "program_input_read" => {
            // The table with the most constraints; its first main-trace input that a constraint instruction reads.
            let t = (0..p.tables.len()).max_by_key(|&t| p.tables[t].constraints.len()).unwrap();
            let (inp, (i, slot)) = p
                .inputs
                .iter()
                .filter(|(_, x)| matches!(x, crate::compiler::Input::TraceLocal(tt, _) if *tt == t))
                .find_map(|(id, x)| {
                    let v = s.input_val[id];
                    s.program.iter().enumerate().find_map(|(k, ins)| {
                        (ins.role == "eval.constraint").then(|| [ins.a, ins.b, ins.c].iter().position(|o| *o == Some(v)).map(|sl| (k, sl))).flatten()
                    }).map(|r| (*x, r))
                })
                .expect("a constraint instruction reading a main-trace input");
            let ops = move |k: usize, o: &mut [E8; 3]| {
                if k == i {
                    o[slot][0] += F::ONE;
                }
            };
            derive(kt, s, &Hooks { operands: &ops, ..no_hooks() });
            json!({"edit": format!("a wrong program input: the first constraint instruction that reads table {}'s opened value {inp:?} reads it plus one at its claim's address (address column honest)", s.child.tables[t].name),
                "instruction": i, "row": s.instr_row[i]})
        }
        other => panic!("unknown variant {other}"),
    }
}
