//! The B2 trace generator (L5, 2026-11-01; B1's, itself G1's generalized to L0' v2's layout; B2: the second write slot
//! W2, the injection read slot RI, the bus control read from the preprocessed columns).
//!
//! Honest mode replays the native verifier of the child proof (the batch transcript's rows and every tree's paths,
//! each checked against the native challenger's duplexings and the native MMCS multi-openings with their caps), then
//! fills the lanes: the base lane's coset points (FRI rounds and the canonical tree's x), the base-value payloads, the
//! DEEP lane (B1: through the pass rows of joined chains) and the batching challenge's power columns, the bus memory
//! (B2: W2's claims, cap entries, terminals, DEEP sums and the query's high part) and the ALU program (the compiled
//! batch constraint program included), the cap-read rows' operands, the dynamic cap-read addresses (main column AA) and
//! the cap entries' multiplicities (main column MW). It checks every value against the native verifier's own functions:
//! p3-fri's `fold_row` and roll-ins (verifier.rs l. 1035-1046), the final polynomial (B1: a constant one too),
//! `open_inputs` per height, `selectors_at_point` per table, the AIR's own evaluation of every constraint (base and
//! LogUp) at zeta, the native folder with lookups, `recompose_quotient_from_chunks` and the terminal sum. The generator
//! is never a source of trust: every value it writes is checked by the kernel's constraints or by the bus, and the
//! malicious variants edit this trace before the constraint check.
//! Research prototype; loop-internal self-review; not independently reviewed.
use std::collections::{BTreeMap, HashMap};

use p3_field::{BasedVectorSpace, Field, PrimeCharacteristicRing, PrimeField32, TwoAdicField};
use p3_fri::{FriFoldingStrategy, TwoAdicFriFolding};
use p3_koala_bear::{GenericPoseidon2LinearLayersKoalaBear, KoalaBear as F};
use p3_matrix::dense::RowMajorMatrix;
use p3_poseidon2_air::generate_trace_rows;
use p3_symmetric::Permutation;

use crate::EF;
use crate::compiler::{CVal, Input, Sel};
use crate::kernel::{A, AA, ACC, ADDR_A, B, BIT, C, CAP_BITS, DL, HB, HI_BITS, LOW_BITS, MULT_W, MW, OUT, Op, P2W, PW, R, TP, TP_N, V, W2, WIDTH, X, XQ, constants, ef_mul};
use crate::schedule::{Instr, Node, Schedule, Sq, Src, Start, TRow, Val, Writer};

pub type E8 = [F; 8];

pub fn perm(x: [F; 16]) -> [F; 16] {
    p3_koala_bear::default_koalabear_poseidon2_16().permute(x)
}
pub fn to_ef(v: &E8) -> EF {
    EF::from_basis_coefficients_slice(v).unwrap()
}
pub fn from_ef(e: EF) -> E8 {
    e.as_basis_coefficients_slice().try_into().unwrap()
}
pub fn base(v: F) -> E8 {
    let mut e = [F::ZERO; 8];
    e[0] = v;
    e
}
pub fn rev_bits(x: usize, bits: usize) -> usize {
    if bits == 0 { 0 } else { x.reverse_bits() >> (usize::BITS as usize - bits) }
}

/// Child-side values the generator needs, all taken from the native verifier's replay.
pub struct ChildData {
    pub pv: Vec<F>,
    pub wit: Vec<F>,
    /// The constants the transcript absorbs where the schedule has the pinned preprocessed cap: the pinned cap for a
    /// genuine child; the attacker's key's cap for the recomputed-key child.
    pub pre_cap: Vec<[F; 8]>,
    /// `leaves[t][q][k]`: the leaf-hash input of tree t's group k at query q (rows, each followed by its salt).
    pub leaves: Vec<Vec<Vec<Vec<F>>>>,
    /// `sibs[t][q]`: the siblings of the walked levels.
    pub sibs: Vec<Vec<Vec<[F; 8]>>>,
    /// `idx[t][q]`: the leaf index the native multi-opening checked.
    pub idx: Vec<Vec<usize>>,
    /// `caps[t]`: the commitment's cap as the native verifier checked it.
    pub caps: Vec<Vec<[F; 8]>>,
    pub perm_log: Vec<([F; 16], [F; 16])>,
    pub init: [F; 16],
    /// Per query, the reduced openings p3-fri's own `open_inputs` computes, per log height.
    pub native_ro: Vec<BTreeMap<usize, EF>>,
    pub native: NativeG1,
}

/// The native verifier's values of every table's constraint identity at zeta and of the terminal check (main.rs
/// computes them on the child proof with p3_batch_stark_c3n's and p3-commit's functions).
#[derive(Clone)]
pub struct NativeTable {
    pub trace_local: Vec<EF>,
    pub trace_next: Vec<EF>,
    pub pre_local: Vec<EF>,
    pub perm_local: Vec<EF>,
    pub perm_next: Vec<EF>,
    /// The permutation trace's claimed base columns at zeta and (expanded to the full width) at zeta * g.
    pub perm_local_flat: Vec<EF>,
    pub perm_next_flat: Vec<EF>,
    pub chunks: Vec<Vec<EF>>,
    pub public: Vec<F>,
    pub challenges: Vec<EF>,
    pub terminal: Option<EF>,
    /// selectors_at_point: is_first_row, is_last_row, is_transition, inv_vanishing; Z_H(zeta).
    pub sels: [EF; 4],
    pub z_h: EF,
    pub constraints: Vec<EF>,
    pub folded: EF,
    pub chunk_vanishing: Vec<EF>,
    pub zps: Vec<EF>,
    pub chunk_values: Vec<EF>,
    pub quotient: EF,
    pub identity_holds: bool,
    pub verify_constraints: String,
}

#[derive(Clone)]
pub struct NativeG1 {
    pub alpha: EF,
    pub zeta: EF,
    pub lookup_alpha: EF,
    pub lookup_beta: EF,
    pub tables: Vec<NativeTable>,
    pub terminal_sum_zero: bool,
}

#[derive(Clone)]
pub struct KTrace {
    pub n: usize,
    pub inp: Vec<[F; 16]>,
    pub bit: Vec<F>,
    pub acc: Vec<F>,
    pub hb: Vec<[F; HI_BITS]>,
    pub tp: Vec<[F; TP_N]>,
    pub xq: Vec<F>,
    pub x: Vec<F>,
    pub v: Vec<F>,
    pub alu: Vec<[E8; 4]>,
    /// B2: the RA address (main), the W2 multiplicity (main) and the W2 value.
    pub aa: Vec<F>,
    pub mw: Vec<F>,
    pub w2: Vec<E8>,
    pub d: Vec<E8>,
    pub pw: Vec<[E8; 4]>,
}

impl KTrace {
    pub fn new(n: usize) -> Self {
        KTrace {
            n,
            inp: vec![[F::ZERO; 16]; n],
            bit: vec![F::ZERO; n],
            acc: vec![F::ZERO; n],
            hb: vec![[F::ZERO; HI_BITS]; n],
            tp: vec![[F::ZERO; TP_N]; n],
            xq: vec![F::ZERO; n],
            x: vec![F::ZERO; n],
            v: vec![F::ZERO; n],
            alu: vec![[[F::ZERO; 8]; 4]; n],
            aa: vec![F::ZERO; n],
            mw: vec![F::ZERO; n],
            w2: vec![[F::ZERO; 8]; n],
            d: vec![[F::ZERO; 8]; n],
            pw: vec![[[F::ZERO; 8]; 4]; n],
        }
    }
    pub fn out(&self, r: usize) -> [F; 16] {
        perm(self.inp[r])
    }

    /// The main trace: Poseidon2Air columns regenerated from the inputs, then the kernel columns.
    pub fn finalize(&self) -> RowMajorMatrix<F> {
        let p2 = generate_trace_rows::<F, GenericPoseidon2LinearLayersKoalaBear, 16, 3, 0, 4, 20>(self.inp.clone(), &constants(), 0);
        assert_eq!(p2.width, P2W);
        let w = WIDTH;
        let mut v = vec![F::ZERO; self.n * w];
        for r in 0..self.n {
            let row = &mut v[r * w..(r + 1) * w];
            row[..P2W].copy_from_slice(&p2.values[r * P2W..(r + 1) * P2W]);
            row[BIT] = self.bit[r];
            row[ACC] = self.acc[r];
            row[HB..HB + HI_BITS].copy_from_slice(&self.hb[r]);
            row[TP..TP + TP_N].copy_from_slice(&self.tp[r]);
            row[XQ] = self.xq[r];
            row[X] = self.x[r];
            row[V] = self.v[r];
            for (k, col) in [A, B, C, R].into_iter().enumerate() {
                row[col..col + 8].copy_from_slice(&self.alu[r][k]);
            }
            row[AA] = self.aa[r];
            row[MW] = self.mw[r];
            row[W2..W2 + 8].copy_from_slice(&self.w2[r]);
            row[DL..DL + 8].copy_from_slice(&self.d[r]);
            for i in 0..4 {
                row[PW + 8 * i..PW + 8 * i + 8].copy_from_slice(&self.pw[r][i]);
            }
        }
        for r in [0usize, self.n / 2, self.n - 1] {
            assert_eq!(&v[r * w + OUT..r * w + OUT + 16], &self.out(r)[..], "Poseidon2Air output differs");
        }
        RowMajorMatrix::new(v, w)
    }

    /// Re-apply the schedule's chaining rules (flags of row r - 1 into row r) over a row range (K1's).
    pub fn rechain(&mut self, s: &Schedule, rows: std::ops::Range<usize>) {
        let a = &s.air;
        let p = &a.pidx;
        for r in rows {
            assert!(r > 0);
            let f = |col: usize| a.pre[col][r - 1] == F::ONE;
            let o = self.out(r - 1);
            if f(p.kc) {
                self.inp[r][8] = o[8] + a.pre[p.tag][r - 1];
                self.inp[r][9..16].copy_from_slice(&o[9..16]);
            }
            for l in 0..8 {
                if f(p.kr[l]) {
                    self.inp[r][l] = o[l];
                }
            }
            if f(p.lnk) {
                if self.bit[r] == F::ZERO {
                    self.inp[r][..8].copy_from_slice(&o[..8]);
                } else {
                    self.inp[r][8..].copy_from_slice(&o[..8]);
                }
            }
        }
    }
}

/// The transcript rows' inputs for given lane values (the native duplexing rule) from a chosen initial state.
pub fn transcript_rows_from(trows: &[TRow], value: &dyn Fn(Src) -> F, init: [F; 16]) -> Vec<[F; 16]> {
    let mut prev = init;
    let mut rows = Vec::with_capacity(trows.len());
    for row in trows {
        let mut x = if row.k == 17 { [F::ZERO; 16] } else { prev };
        if row.k > 0 {
            for l in 0..8 {
                x[l] = value(row.lanes[l].expect("absorbing row lane"));
            }
            if row.k <= 8 { x[8] += F::from_usize(row.k); }
        }
        rows.push(x);
        prev = perm(x);
    }
    rows
}

pub fn sampled(trows: &[TRow], inputs: &[[F; 16]]) -> Vec<(Sq, F)> {
    let mut v = vec![];
    for (r, row) in trows.iter().enumerate() {
        let o = perm(inputs[r]);
        for &(lane, sq) in &row.samples {
            v.push((sq, o[lane]));
        }
    }
    v
}
pub fn query_elements(trows: &[TRow], inputs: &[[F; 16]], q: usize) -> Vec<F> {
    let mut x = vec![F::ZERO; q];
    for (sq, v) in sampled(trows, inputs) {
        if let Sq::Query(i) = sq {
            x[i] = v;
        }
    }
    x
}
pub fn betas(trows: &[TRow], inputs: &[[F; 16]], rounds: usize) -> Vec<EF> {
    let mut b = vec![[F::ZERO; 8]; rounds];
    for (sq, v) in sampled(trows, inputs) {
        if let Sq::Beta(r, i) = sq {
            b[r][i] = v;
        }
    }
    b.iter().map(to_ef).collect()
}
/// The extension-field challenges of a transcript: (lookup alpha, lookup beta, alpha, zeta, PCS alpha).
pub fn challenges(trows: &[TRow], inputs: &[[F; 16]]) -> [EF; 5] {
    let mut c = [[F::ZERO; 8]; 5];
    for (sq, v) in sampled(trows, inputs) {
        match sq {
            Sq::LookupAlpha(i) => c[0][i] = v,
            Sq::LookupBeta(i) => c[1][i] = v,
            Sq::Alpha(i) => c[2][i] = v,
            Sq::Zeta(i) => c[3][i] = v,
            Sq::PcsAlpha(i) => c[4][i] = v,
            _ => {}
        }
    }
    c.map(|x| to_ef(&x))
}

pub fn kernel_query_elements(kt: &KTrace, s: &Schedule) -> Vec<F> {
    let mut x = vec![F::ZERO; s.q];
    for (r, row) in s.trows.iter().enumerate() {
        let o = kt.out(r);
        for &(lane, sq) in &row.samples {
            if let Sq::Query(i) = sq {
                x[i] = o[lane];
            }
        }
    }
    x
}

pub fn end_columns(hi: u32) -> ([F; HI_BITS], [F; TP_N]) {
    let hb: [F; HI_BITS] = core::array::from_fn(|i| F::from_u32((hi >> i) & 1));
    let top = 24 - LOW_BITS;
    let mut tp = [F::ZERO; TP_N];
    tp[0] = hb[top] * hb[top + 1];
    for k in 1..TP_N {
        tp[k] = tp[k - 1] * hb[top + 1 + k];
    }
    (hb, tp)
}
pub fn hi_of(x: F) -> u32 {
    x.as_canonical_u32() >> LOW_BITS
}
pub fn low_of(x: F) -> u32 {
    x.as_canonical_u32() & ((1u32 << LOW_BITS) - 1)
}
/// The cap index of a query (the index bits LOW_BITS - CAP_BITS .. LOW_BITS, common to every tree).
pub fn cap_of(x: F) -> u32 {
    (x.as_canonical_u32() >> (LOW_BITS - CAP_BITS)) & ((1u32 << CAP_BITS) - 1)
}

/// Hash one group's leaf from the zero state into its rows; returns the digest (the last row's output).
pub fn fill_group_rows(kt: &mut KTrace, start: usize, lh_rows: usize, leaf: &[F]) -> [F; 8] {
    let mut prev = [F::ZERO; 16];
    for j in 0..lh_rows {
        let r = start + j;
        let mut xin = prev;
        if j == 0 {
            xin = [F::ZERO; 16];
        }
        let chunk = &leaf[8 * j..(8 * j + 8).min(leaf.len())];
        xin[..chunk.len()].copy_from_slice(chunk);
        kt.inp[r] = xin;
        kt.bit[r] = F::ZERO;
        prev = perm(xin);
    }
    prev[..8].try_into().unwrap()
}

/// Fill one tree's block at one query: every group's leaf rows, the nodes (a compression with the sibling on the side
/// the index bit gives; an injection with the group's digest on the right), the cap rows (free inputs), and the bits
/// of the path (`bits_of` is the path's start value's integer: its bit j is consumed on the path's j-th bit row).
pub fn fill_tree_rows(kt: &mut KTrace, s: &Schedule, ti: usize, qq: usize, leaves: &[Vec<F>], sibs: &[[F; 8]], bits_of: u32) {
    let t = &s.trees[ti];
    let b0 = s.block_start[qq][ti];
    let mut digests = vec![[F::ZERO; 8]; t.groups.len()];
    for (k, g) in t.groups.iter().enumerate() {
        assert_eq!(leaves[k].len(), g.leaf_len, "tree {} group {k}: leaf length", t.name);
        digests[k] = fill_group_rows(kt, b0 + t.group_start[k], g.lh_rows, &leaves[k]);
    }
    for j in 0..t.consume_lh {
        kt.bit[b0 + t.path_start + j] = F::from_u32((bits_of >> j) & 1);
    }
    assert_eq!(sibs.len(), t.mc);
    let mut cur = digests[0];
    for &(o, nd) in &t.nodes {
        let r = b0 + o;
        let mut xin = [F::ZERO; 16];
        match nd {
            Node::Comp(level) => {
                let b = (bits_of >> (t.consume_lh + level)) & 1;
                if b == 0 {
                    xin[..8].copy_from_slice(&cur);
                    xin[8..].copy_from_slice(&sibs[level]);
                } else {
                    xin[..8].copy_from_slice(&sibs[level]);
                    xin[8..].copy_from_slice(&cur);
                }
                kt.bit[r] = F::from_u32(b);
            }
            Node::Inj(k) => {
                xin[..8].copy_from_slice(&cur);
                xin[8..].copy_from_slice(&digests[k]);
                kt.bit[r] = F::ZERO;
            }
        }
        kt.inp[r] = xin;
        cur = perm(xin)[..8].try_into().unwrap();
    }
    for j in 0..t.cap_rows {
        let r = b0 + t.cap_read + 1 + j;
        kt.inp[r] = [F::ZERO; 16];
        let level = t.mc + j;
        kt.bit[r] = F::from_u32((bits_of >> (t.consume_lh + level)) & 1);
    }
}

/// The accumulator and the query-element copy along one path from `x0`, consuming the bits as written in `kt.bit`;
/// the cap-read row's cap bits and the end row's high bits from `xq` (the query element).
pub fn set_acc(kt: &mut KTrace, s: &Schedule, ti: usize, qq: usize, x0: F, xq: F) {
    let t = &s.trees[ti];
    let cons = s.air.pidx.cons;
    let ps = s.path_start(qq, ti);
    let end = s.end_row(qq, ti);
    let half = F::TWO.inverse();
    let mut a = x0;
    for r in ps..=end {
        kt.acc[r] = a;
        kt.xq[r] = x0;
        if s.air.pre[cons][r] == F::ONE {
            a = (a - kt.bit[r]) * half;
        }
    }
    let cr = s.cap_read_row(qq, ti);
    let cap = cap_of(xq);
    let mut hb = [F::ZERO; HI_BITS];
    for k in 0..CAP_BITS {
        hb[k] = F::from_u32((cap >> k) & 1);
    }
    kt.hb[cr] = hb;
    if t.canonical || matches!(t.kind, crate::schedule::TreeKind::Fri(_)) {
        let (hb, tp) = end_columns(hi_of(xq));
        kt.hb[end] = hb;
        kt.tp[end] = tp;
    }
}

/// The start value of a tree's path from the query element (honest: the element shifted by the tree's skip).
pub fn start_of(s: &Schedule, ti: usize, x: F) -> F {
    F::from_u32(x.as_canonical_u32() >> s.trees[ti].skip)
}

/// Every path's accumulator from the query elements `xs`, chained as the kernel chains it: the canonical tree, FRI
/// round 0 and the full-height input trees from the element, the lower input trees from the canonical path's
/// accumulator after their shift, FRI round r >= 1 from round r - 1's leaf row after its coset bits.
pub fn set_all_acc(kt: &mut KTrace, s: &Schedule, xs: &[F]) {
    let canon = s.canon();
    for (qq, &xv) in xs.iter().enumerate() {
        set_acc(kt, s, canon, qq, xv, xv);
        for ti in 0..s.trees.len() {
            if ti == canon {
                continue;
            }
            let x0 = match s.trees[ti].start {
                Start::Load | Start::Xq => xv,
                Start::Shift(d) => kt.acc[s.block_start[qq][canon] + s.trees[canon].bit_rows()[d]],
                Start::Chain(r) => {
                    let prev = s.fri_tree(r - 1);
                    kt.acc[s.path_start(qq, prev) + s.trees[prev].consume_lh]
                }
            };
            set_acc(kt, s, ti, qq, x0, xv);
        }
    }
}

/// A malicious change of one base-lane path (query, tree): another start value.
#[derive(Clone, Copy)]
pub enum XEdit {
    Start(usize, usize, F),
}

/// The twiddles of a base-lane tree (the canonical tree and the FRI rounds).
pub fn twiddles(s: &Schedule, ti: usize) -> Vec<F> {
    let t = &s.trees[ti];
    let h = t.log_height + t.consume_lh;
    let lh = t.log_height;
    (0..lh).map(|i| F::two_adic_generator(h).exp_u64(1u64 << (lh - 1 - i))).collect()
}

/// The base lane along every scheduled path: X = start on the path's first row, X' = X (1 + (c_i - 1) bit) on the
/// rows consuming the tree's own bits.
pub fn fill_x(kt: &mut KTrace, s: &Schedule, edit: Option<XEdit>) {
    for qq in 0..s.q {
        for ti in 0..s.trees.len() {
            let t = &s.trees[ti];
            if !t.canonical && !matches!(t.kind, crate::schedule::TreeKind::Fri(_)) {
                continue;
            }
            let b0 = s.block_start[qq][ti];
            let tw = twiddles(s, ti);
            let mut xv = if t.canonical { F::GENERATOR } else { F::ONE };
            if let Some(XEdit::Start(oq, ot, v)) = edit {
                if oq == qq && ot == ti {
                    xv = v;
                }
            }
            let bits: Vec<usize> = t.tree_bit_rows().iter().map(|o| b0 + o).collect();
            let mut next_bit = 0;
            for r in b0 + t.path_start..=b0 + t.end {
                kt.x[r] = xv;
                if next_bit < bits.len() && bits[next_bit] == r {
                    if next_bit + 1 < bits.len() && kt.bit[r] == F::ONE {
                        xv *= tw[next_bit];
                    }
                    next_bit += 1;
                }
            }
        }
    }
}

/// The coset point a path's end row writes (the last bit applied): x[end] (1 + xce bit).
pub fn coset_point(kt: &KTrace, s: &Schedule, qq: usize, ti: usize) -> F {
    let end = s.end_row(qq, ti);
    let xce = s.air.pre[s.air.pidx.xce][end];
    kt.x[end] + xce * kt.x[end] * kt.bit[end]
}

/// The base-value payloads on their writer rows, from the rows' contents.
pub fn fill_v(kt: &mut KTrace, s: &Schedule) {
    let canon = s.canon();
    for (v, w) in &s.writer {
        if let Writer::V(row) = *w {
            kt.v[row] = match v {
                Val::Xq(_) | Val::Chain(..) | Val::Shift(..) => kt.acc[row],
                Val::Sigma(..) => F::ONE.halve() - kt.bit[row],
                Val::S(qq, r) => coset_point(kt, s, *qq, s.fri_tree(*r)),
                Val::XI(qq, _) => coset_point(kt, s, *qq, canon),
                other => panic!("unexpected {other:?}"),
            };
        }
    }
}

/// The batching challenge as the kernel's transcript row squeezes it (output lanes 7..0 of its row).
pub fn kernel_pcs_alpha(kt: &KTrace, s: &Schedule) -> EF {
    let o = kt.out(s.pcs_alpha_row);
    to_ef(&core::array::from_fn(|k| o[7 - k]))
}

/// Edits a malicious variant makes to the DEEP lane.
#[derive(Clone, Copy, Default)]
pub struct DeepEdits {
    pub coef: Option<(usize, usize, F)>,
    pub powers: Option<[E8; 4]>,
    pub power_row: Option<(usize, [E8; 4])>,
    /// A pass row's sum plus delta (coordinate 0) instead of the next row's.
    pub pass: Option<(usize, F)>,
}

/// The DEEP lane: the power columns (alpha^1..alpha^4 of the kernel's batching challenge), and per query and chain the
/// backward Horner over the chain's value rows exactly as the constraints state it: D = D' alpha^8 + sum_l IN_l alpha^l
/// (D' only when the chain continues).
pub fn fill_deep(kt: &mut KTrace, s: &Schedule, e: &DeepEdits) {
    let a = kernel_pcs_alpha(kt, s);
    let pw: [E8; 4] = e.powers.unwrap_or([from_ef(a), from_ef(a * a), from_ef(a * a * a), from_ef(a * a * a * a)]);
    for r in 0..kt.n {
        kt.pw[r] = pw;
    }
    if let Some((row, p)) = e.power_row {
        kt.pw[row] = p;
    }
    let coefs_of = |pw: &[E8; 4]| -> ([EF; 8], EF) {
        let p: [EF; 4] = pw.map(|x| to_ef(&x));
        ([EF::ONE, p[0], p[1], p[2], p[3], p[3] * p[0], p[3] * p[1], p[3] * p[2]], p[3] * p[3])
    };
    for row in kt.d.iter_mut() {
        *row = [F::ZERO; 8];
    }
    for qq in 0..s.q {
        for ch in &s.chains {
            let s0 = s.group_row(qq, ch.tree, ch.group);
            // The chain's rows from its last to its first: a value row adds its lanes to the next row's sum times
            // alpha^8 (except the chain's last value row); a pass row (B1, between joined matrices) passes it through.
            let mut rows: Vec<(usize, Option<&Vec<usize>>)> = ch.value_rows.iter().map(|(r, l)| (*r, Some(l))).collect();
            rows.extend(ch.pass_rows.iter().map(|&r| (r, None)));
            rows.sort_by_key(|x| x.0);
            let last_value = ch.value_rows.last().unwrap().0;
            for &(r, lanes) in rows.iter().rev() {
                let row = s0 + r;
                let Some(lanes) = lanes else {
                    let mut pass = kt.d[row + 1];
                    if let Some((pr, delta)) = e.pass {
                        if pr == row {
                            pass[0] += delta;
                        }
                    }
                    kt.d[row] = pass;
                    continue;
                };
                let (coefs, a8) = coefs_of(&kt.pw[row]);
                let mut sum = if r != last_value { to_ef(&kt.d[row + 1]) * a8 } else { EF::ZERO };
                for &l in lanes {
                    let mut v = kt.inp[row][l];
                    if let Some((cr, cl, delta)) = e.coef {
                        if cr == row && cl == l {
                            v += delta;
                        }
                    }
                    sum += coefs[l] * v;
                }
                kt.d[row] = from_ef(sum);
            }
        }
    }
}

/// The value a W2 row writes, from the row's sources (B1: the R port's).
pub fn w2_value(kt: &KTrace, s: &Schedule, v: Val, row: usize) -> E8 {
    let at = |p: crate::schedule::ClaimPos| -> E8 {
        assert_eq!(p.row, row);
        core::array::from_fn(|j| if p.lane + j < 8 { kt.inp[row][p.lane + j] } else { kt.inp[row + 1][p.lane + j - 8] })
    };
    match v {
        Val::Advice(_) => kt.inp[row][..8].try_into().unwrap(),
        Val::Claim(k) => at(s.claim_pos[k]),
        Val::Cap(t, j) => at(s.cap_pos[&(t, j)]),
        Val::Terminal(t) => at(s.terminal_pos[&t]),
        Val::SD(..) => kt.d[row],
        Val::Hi(_) => {
            let mut hi = F::ZERO;
            for i in 0..HI_BITS {
                hi += kt.hb[row][i] * F::from_u32(1 << i);
            }
            base(hi)
        }
        other => panic!("not a W2 value: {other:?}"),
    }
}

/// The bus memory of the non-ALU writers, from the trace rows; `w2` may change a W2 value.
pub fn memory(kt: &KTrace, s: &Schedule, w2: &dyn Fn(Val, &mut E8)) -> HashMap<Val, E8> {
    let mut m = HashMap::new();
    for (v, w) in &s.writer {
        let e = match *w {
            Writer::Alu(_) => continue,
            Writer::W2(row) => {
                let mut e = w2_value(kt, s, *v, row);
                w2(*v, &mut e);
                e
            }
            Writer::H(row) => kt.inp[row][..8].try_into().unwrap(),
            Writer::O(row) => {
                let o = kt.out(row);
                core::array::from_fn(|k| o[7 - k])
            }
            Writer::V(row) => base(kt.v[row]),
        };
        m.insert(*v, e);
    }
    m
}

/// Hooks a malicious variant uses to change what the trace holds.
pub struct Hooks<'a> {
    pub operands: &'a dyn Fn(usize, &mut [E8; 3]),
    pub result: &'a dyn Fn(usize, &mut E8),
    pub opcode: &'a dyn Fn(usize) -> Option<Op>,
    pub w2: &'a dyn Fn(Val, &mut E8),
    pub deep: DeepEdits,
}
pub fn no_hooks() -> Hooks<'static> {
    Hooks { operands: &|_, _| {}, result: &|_, _| {}, opcode: &|_| None, w2: &|_, _| {}, deep: DeepEdits::default() }
}

pub fn compute(op: Op, a: &E8, b: &E8, c: &E8, ins: &Instr) -> E8 {
    let (ea, eb, ec) = (to_ef(a), to_ef(b), to_ef(c));
    match op {
        Op::Mul => from_ef(ea * eb),
        Op::Mac => from_ef(ea * eb + ec),
        Op::Bfly => from_ef((ea + eb).halve() + ec * (ea - eb)),
        Op::Inv2 => from_ef(ea.double().inverse()),
        Op::Const => {
            let mut r = base(ins.kappa);
            r[1] = ins.kappa_x;
            r
        }
        Op::Lin => from_ef(ea + eb * ins.kappa),
        Op::Inv => ea.try_inverse().map(from_ef).unwrap_or([F::ZERO; 8]),
        Op::Unpack => base(a[ins.lane]),
        Op::Eq | Op::Load => [F::ZERO; 8],
    }
}

/// Run the ALU program over the memory (non-ALU writers already in it), filling a, b, c, r. The bus does not order
/// the instructions; the generator evaluates them in program order, deferring one whose operand is not yet computed
/// (a FRI roll-in reads a reduced opening the DEEP part computes later in program order).
pub fn run_alu(kt: &mut KTrace, s: &Schedule, mem: &mut HashMap<Val, E8>, h: &Hooks) {
    let n = s.program.len();
    let mut done = vec![false; n];
    let mut left = n;
    while left > 0 {
        let before = left;
        for (i, ins) in s.program.iter().enumerate() {
            if done[i] {
                continue;
            }
            if [ins.a, ins.b, ins.c].into_iter().flatten().any(|v| !mem.contains_key(&v)) {
                continue;
            }
            let row = s.instr_row[i];
            let mut ops = [[F::ZERO; 8]; 3];
            for (slot, v) in [ins.a, ins.b, ins.c].into_iter().enumerate() {
                if let Some(v) = v {
                    ops[slot] = mem[&v];
                }
            }
            (h.operands)(i, &mut ops);
            let op = (h.opcode)(i).unwrap_or(ins.op);
            let mut r = compute(op, &ops[0], &ops[1], &ops[2], ins);
            (h.result)(i, &mut r);
            if let Some(v) = ins.r {
                mem.insert(v, r);
            }
            kt.alu[row] = [ops[0], ops[1], ops[2], if ins.r.is_some() { r } else { [F::ZERO; 8] }];
            done[i] = true;
            left -= 1;
        }
        if left == before {
            let i = (0..n).find(|&i| !done[i]).unwrap();
            let ins = &s.program[i];
            let missing: Vec<Val> = [ins.a, ins.b, ins.c].into_iter().flatten().filter(|v| !mem.contains_key(v)).collect();
            panic!("instruction {i} ({}) reads {missing:?}, which nothing computes", ins.role);
        }
    }
}

/// B2: the second write slot: W2 on every W2 row is the value the row writes (B1: R on the write port's rows).
pub fn fill_w2(kt: &mut KTrace, s: &Schedule, mem: &HashMap<Val, E8>) {
    for r in kt.w2.iter_mut() {
        *r = [F::ZERO; 8];
    }
    for &(row, v) in &s.w2port {
        kt.w2[row] = mem[&v];
    }
}

/// The reserved rows' operands: a cap-read row's a is its node and b the query's high part. B2: an injection row
/// needs no operand (its digest is read into the input lanes 15..8 by RI; B1 read it into operand a).
pub fn fill_reserved(kt: &mut KTrace, s: &Schedule, mem: &HashMap<Val, E8>) {
    for qq in 0..s.q {
        for (ti, t) in s.trees.iter().enumerate() {
            let cr = s.block_start[qq][ti] + t.cap_read;
            let o = kt.out(cr);
            kt.alu[cr][0] = o[..8].try_into().unwrap();
            kt.alu[cr][1] = mem[&Val::Hi(qq)];
        }
    }
}

/// B2: the two main bus columns the prover supplies: AA, the RA address (the schedule's, plus the cap bits on a cap
/// read), and MW, the W2 multiplicity (the schedule's, a cap entry's read count on its write row). Every other address
/// and count is a preprocessed column (B1: 16 main copies of the periodic control).
pub fn fill_bus_main(kt: &mut KTrace, s: &Schedule) {
    let p = &s.air.pidx;
    for r in 0..kt.n {
        kt.aa[r] = s.air.pre[p.ctrl[ADDR_A]][r];
        kt.mw[r] = s.air.pre[p.ctrl[MULT_W]][r];
    }
    let mut count: HashMap<u32, u32> = HashMap::new();
    for &(row, _) in &s.cap_reads {
        let mut idx = 0u32;
        for k in 0..CAP_BITS {
            idx += kt.hb[row][k].as_canonical_u32() << k;
        }
        kt.aa[row] += F::from_u32(idx);
        *count.entry(kt.aa[row].as_canonical_u32()).or_default() += 1;
    }
    for (v, w) in &s.writer {
        if let (Val::Cap(..), Writer::W2(row)) = (v, w) {
            kt.mw[*row] = F::from_u32(count.get(&s.addr[v]).copied().unwrap_or(0));
        }
    }
}

/// Everything derived from the rows and bits: the base lane, the payloads, the DEEP lane, the memory and the ALU,
/// the W2 slot, the reserved rows' operands, the main bus columns.
pub fn derive(kt: &mut KTrace, s: &Schedule, h: &Hooks) -> HashMap<Val, E8> {
    fill_x(kt, s, None);
    fill_v(kt, s);
    fill_deep(kt, s, &h.deep);
    let mut mem = memory(kt, s, h.w2);
    run_alu(kt, s, &mut mem, h);
    fill_w2(kt, s, &mem);
    fill_reserved(kt, s, &mem);
    fill_bus_main(kt, s);
    mem
}

/// The native FRI verifier's own functions on the values the kernel's trace holds: `fold_row` per query and round,
/// the roll-ins of the lower heights' reduced openings with beta^arity (verifier.rs l. 1035-1046), the subgroup start,
/// the final point and Horner. Panics on any difference.
pub fn native_fri_check(s: &Schedule, xs: &[F], mem: &HashMap<Val, E8>, betas: &[EF], final_poly: &[EF], native_ro: &[BTreeMap<usize, EF>]) -> serde_json::Value {
    let folding = TwoAdicFriFolding::<Vec<()>, ()>(core::marker::PhantomData);
    let arities = &s.child.fri_log_arities;
    let (mut folds, mut points, mut chains, mut finals, mut rollins) = (0, 0, 0, 0, 0);
    for (qq, &xv) in xs.iter().enumerate() {
        let index = low_of(xv) as usize;
        let mut idx = index;
        let mut h = s.child.index_bits;
        let mut folded = native_ro[qq][&h];
        for (r, &la) in arities.iter().enumerate() {
            let arity = 1usize << la;
            let evals: Vec<EF> = (0..arity).map(|j| to_ef(&mem[&Val::E(qq, r, j)])).collect();
            let pos = idx % arity;
            assert_eq!(evals[pos], folded, "query {qq} round {r}: the opened coset value at the position is not the running fold");
            chains += 1;
            idx >>= la;
            let lf = h - la;
            let mut native = FriFoldingStrategy::<F, EF>::fold_row(&folding, idx, lf, la, betas[r], evals.iter().copied());
            assert_eq!(to_ef(&mem[&Val::U(qq, r)]), native, "query {qq} round {r}: the kernel's fold differs from fold_row");
            folds += 1;
            let s_native = F::two_adic_generator(h).exp_u64(rev_bits(idx, lf) as u64);
            assert_eq!(mem[&Val::S(qq, r)], base(s_native), "query {qq} round {r}: coset point differs");
            points += 1;
            if let Some(&rh) = s.rollins.get(&r) {
                assert_eq!(rh, lf);
                native += betas[r].exp_power_of_2(la) * native_ro[qq][&lf];
                if r + 1 < arities.len() {
                    assert_eq!(to_ef(&mem[&Val::UR(qq, r + 1)]), native, "query {qq} after round {r}: the roll-in differs");
                }
                rollins += 1;
            }
            folded = native;
            h = lf;
        }
        let x = F::two_adic_generator(s.child.index_bits).exp_u64(rev_bits(idx, s.child.index_bits) as u64);
        if final_poly.len() > 1 {
            assert_eq!(mem[&Val::XF(qq)], base(x), "query {qq}: final point differs");
        } else {
            assert!(!mem.contains_key(&Val::XF(qq)), "a constant final polynomial has no final point");
        }
        let eval = final_poly.iter().rev().fold(EF::ZERO, |acc, &c| acc * x + c);
        assert_eq!(eval, folded, "query {qq}: the final polynomial at x is not the last fold");
        finals += 1;
    }
    serde_json::json!({"folds_equal_fold_row": folds, "coset_points_equal_native": points,
        "selected_values_equal_running_fold": chains, "rollins_equal_beta_pow_times_reduced_opening": rollins,
        "final_evaluations_equal_last_fold": finals})
}

/// The native verifier's DEEP computation on the values the kernel's trace holds, per height and point: x per height
/// as verifier.rs l. 1244-1248 computes it, the claims' sum (l. 1309-1322) and the opened rows' sum (l. 1396-1399) per
/// (height, point), the reduced opening per height equal to p3-fri's own `open_inputs`, and round 0's opened coset
/// value at the query's position equal to the tallest one. Panics on any difference.
pub fn native_deep_check(s: &Schedule, xs: &[F], mem: &HashMap<Val, E8>, d: &ChildData, zeta: EF, alpha: EF) -> serde_json::Value {
    assert_eq!(to_ef(&mem[&Val::Zeta]), zeta, "zeta on the bus differs from the transcript's");
    assert_eq!(to_ef(&mem[&Val::PcsAlpha]), alpha, "the batching challenge on the bus differs from the transcript's");
    let nc = s.n_claims();
    let claim_wit: Vec<usize> = s.wit_segments.iter().filter(|w| w.0.starts_with("pcs.claims.")).flat_map(|w| w.1..w.1 + w.2).collect();
    let claim = |k: usize| -> EF { to_ef(&core::array::from_fn(|j| d.wit[claim_wit[8 * k + j]])) };
    for k in 0..nc {
        assert_eq!(to_ef(&mem[&Val::Claim(k)]), claim(k), "claim {k} on the bus differs from the absorbed claim");
    }
    let ladder_len = s.claim_blocks.iter().map(|b| b.ladder_off + b.width).max().unwrap();
    let powers: Vec<EF> = alpha.powers().collect_n(ladder_len);
    let mut c_native: BTreeMap<(usize, usize), EF> = BTreeMap::new();
    for b in &s.claim_blocks {
        let ps: Vec<EF> = (0..b.width).map(|i| claim(b.first_claim + i)).collect();
        *c_native.entry((b.log_height, b.point)).or_insert(EF::ZERO) +=
            p3_field::dot_product::<EF, _, _>(powers[b.ladder_off..b.ladder_off + b.width].iter().copied(), ps.into_iter());
    }
    for (k, v) in &c_native {
        assert_eq!(to_ef(&mem[&s.c_vals[k]]), *v, "{k:?}: the claims' sum differs from the native dot product");
    }
    let (mut xs_ok, mut u_ok, mut ro_ok) = (0, 0, 0);
    for (qq, &xv) in xs.iter().enumerate() {
        let index = low_of(xv) as usize;
        for &h in &s.heights {
            let bits_reduced = s.child.index_bits - h;
            let x = F::GENERATOR * F::two_adic_generator(h).exp_u64(rev_bits(index >> bits_reduced, h) as u64);
            assert_eq!(mem[&Val::XI(qq, h)], base(x), "query {qq}: the input coset point at height {h} differs from the native x");
            xs_ok += 1;
        }
        let mut u_native: BTreeMap<(usize, usize), EF> = BTreeMap::new();
        for b in &s.claim_blocks {
            let tree = &s.trees[b.tree];
            let (k, g) = tree.groups.iter().enumerate().find(|(_, g)| g.mats.contains(&b.matrix)).unwrap();
            let start: usize = g.mats.iter().take_while(|&&m| m != b.matrix).map(|&m| tree.mats[m].width + s.child.salt).sum();
            let row = &d.leaves[b.tree][qq][k][start..start + b.width];
            *u_native.entry((b.log_height, b.point)).or_insert(EF::ZERO) +=
                <EF as p3_field::Algebra<F>>::batched_linear_combination(&powers[b.ladder_off..b.ladder_off + b.width], row);
        }
        for (key, v) in &u_native {
            assert_eq!(to_ef(&mem[&s.u_vals[qq][key]]), *v, "query {qq} {key:?}: the opened rows' sum differs from batched_linear_combination");
            u_ok += 1;
        }
        for &h in &s.heights {
            let last = s.hz.iter().filter(|x| x.0 == h).count() - 1;
            assert_eq!(to_ef(&mem[&Val::RO(qq, h, last)]), d.native_ro[qq][&h], "query {qq}: the reduced opening at height {h} differs from open_inputs");
            ro_ok += 1;
        }
        let pos = index % (1usize << s.child.fri_log_arities[0]);
        assert_eq!(to_ef(&mem[&Val::E(qq, 0, pos)]), d.native_ro[qq][&s.child.index_bits], "query {qq}: round 0's opened value at the position is not the reduced opening");
    }
    serde_json::json!({"zeta_and_batching_challenge_on_the_bus_equal_the_transcript": true,
        "claims_on_the_bus_equal_the_absorbed_claims": nc, "claims_sums_equal_dot_product_per_height_and_point": c_native.len(),
        "input_coset_points_equal_native_x_per_height": xs_ok, "opened_row_sums_equal_batched_linear_combination": u_ok,
        "reduced_openings_equal_open_inputs_per_height": ro_ok})
}

/// Every table's constraint identity at zeta and the terminal check against the native verifier's values: every
/// program input on the bus equals the native value; per table the selectors, every constraint (base and LogUp), the
/// permutation values, the folded sum, the chunk domains' vanishing values, the factors, the chunk values, the quotient
/// and the identity's verdict; the terminal sum. Panics on any difference.
pub fn native_g1_check(s: &Schedule, mem: &HashMap<Val, E8>, d: &ChildData) -> serde_json::Value {
    let nk = &d.native;
    let p = &s.child.program;
    let ev = |id: usize| -> EF {
        let v = s.input_val.get(&id).copied().unwrap_or(Val::Ev(id));
        to_ef(mem.get(&v).unwrap_or_else(|| panic!("program value {id} ({v:?}) not on the bus")))
    };
    let mut inputs = 0;
    for &(id, inp) in &p.inputs {
        let want = match inp {
            Input::TraceLocal(t, i) => nk.tables[t].trace_local[i],
            Input::TraceNext(t, i) => nk.tables[t].trace_next[i],
            Input::PreLocal(t, i) => nk.tables[t].pre_local[i],
            Input::PreNext(..) => panic!("no preprocessed next-row input in this child"),
            Input::PermLocal(t, j, k) => nk.tables[t].perm_local_flat[8 * j + k],
            Input::PermNext(t, j, k) => nk.tables[t].perm_next_flat[8 * j + k],
            Input::Chunk(t, c, k) => nk.tables[t].chunks[c][k],
            Input::Public(t, i) => EF::from(nk.tables[t].public[i]),
            Input::Alpha => nk.alpha,
            Input::Zeta => nk.zeta,
            Input::LookupAlpha => nk.lookup_alpha,
            Input::LookupBeta => nk.lookup_beta,
            Input::Periodic(..) => panic!("periodic advice requires the aggregation binding path"),
            Input::Terminal(t) => nk.tables[t].terminal.expect("terminal"),
        };
        assert_eq!(ev(id), want, "program input {inp:?} on the bus differs from the native value");
        inputs += 1;
    }
    let mut per_table = vec![];
    let mut all_identity_kernel = vec![];
    for (t, o) in p.tables.iter().enumerate() {
        let nt = &nk.tables[t];
        assert_eq!(ev(o.z_h), nt.z_h, "table {t}: Z_H(zeta) differs");
        let sels = [ev(o.is_first_row), ev(o.is_last_row), ev(o.is_transition), ev(o.inv_vanishing)];
        assert_eq!(sels, nt.sels, "table {t}: the selectors at zeta differ from selectors_at_point");
        for &(j, off, v) in &o.perm_values {
            let want = if off == 0 { nt.perm_local[j] } else { nt.perm_next[j] };
            assert_eq!(ev(v), want, "table {t}: permutation column {j} at offset {off} differs from from_ext_basis_coefficients");
        }
        let sel_of = |sl: Sel| match sl {
            Sel::First => sels[0],
            Sel::Last => sels[1],
            Sel::Transition => sels[2],
        };
        assert_eq!(o.constraints.len(), nt.constraints.len(), "table {t}: constraint count");
        for (k, cv) in o.constraints.iter().enumerate() {
            let v = match cv.expect("every constraint compiled") {
                CVal::Plain(id) => ev(id),
                CVal::Factored(sl, id) => sel_of(sl) * ev(id),
            };
            assert_eq!(v, nt.constraints[k], "table {t} constraint {k}: the program's value differs from the AIR's evaluation at zeta");
        }
        assert_eq!(ev(o.folded), nt.folded, "table {t}: the folded constraints differ from the native folder's accumulator");
        for (j, &id) in o.chunk_vanishing.iter().enumerate() {
            assert_eq!(ev(id), nt.chunk_vanishing[j], "table {t} chunk domain {j}: Z(zeta) differs");
        }
        for (i, &id) in o.zps.iter().enumerate() {
            assert_eq!(ev(id), nt.zps[i], "table {t} chunk {i}: the factor zp differs");
        }
        for (i, &id) in o.chunk_values.iter().enumerate() {
            assert_eq!(ev(id), nt.chunk_values[i], "table {t} chunk {i}: the chunk value differs");
        }
        assert_eq!(ev(o.quotient), nt.quotient, "table {t}: the recomposed quotient differs from recompose_quotient_from_chunks");
        let lhs = ev(o.identity_lhs);
        assert_eq!(lhs, nt.folded * nt.sels[3], "table {t}: folded * inv_vanishing differs");
        let kernel_identity = lhs == ev(o.quotient);
        assert_eq!(kernel_identity, nt.identity_holds, "table {t}: the kernel's identity verdict differs from the native one");
        all_identity_kernel.push(kernel_identity);
        per_table.push(serde_json::json!({"table": t, "constraints_equal_the_air_at_zeta": nt.constraints.len(),
            "permutation_values_equal_native": o.perm_values.len(), "chunks": o.chunk_values.len(),
            "identity_holds_kernel": kernel_identity, "identity_holds_native": nt.identity_holds, "native_verify_constraints": nt.verify_constraints}));
    }
    let terminal_kernel = match p.terminal_sum {
        Some(sum) => ev(sum) == EF::ZERO,
        None => true,
    };
    assert_eq!(terminal_kernel, nk.terminal_sum_zero, "the kernel's terminal-sum verdict differs from the native one");
    serde_json::json!({"program_inputs_equal_native": inputs, "tables": per_table,
        "terminal_sum_zero_kernel": terminal_kernel, "terminal_sum_zero_native": nk.terminal_sum_zero})
}


/// The honest trace: returns the trace, the query elements and the check results against the native replay.
pub fn honest(s: &Schedule, d: &ChildData) -> (KTrace, Vec<F>, serde_json::Value) {
    let mut kt = KTrace::new(s.n);
    // The constants of the preprocessed cap come from the child's key (the pinned one for a genuine child).
    let pre_override = pre_cap_override(s, &d.pre_cap);
    let rows_owned = {
        let value_at = |row: usize, lane: usize, src: Src| -> F {
            match src {
                Src::Const(v) => pre_override.get(&(row, lane)).copied().unwrap_or(v),
                Src::Pub(j) => d.pv[j],
                Src::Wit(i) => d.wit[i],
            }
        };
        let mut prev = d.init;
        let mut rows = Vec::with_capacity(s.trows.len());
        for (r, row) in s.trows.iter().enumerate() {
            let mut x = prev;
            if row.k > 0 {
                for l in 0..8 {
                    x[l] = value_at(r, l, row.lanes[l].expect("absorbing row lane"));
                }
                x[8] += F::from_usize(row.k);
            }
            rows.push(x);
            prev = perm(x);
        }
        rows
    };
    let rows = rows_owned;
    // The query indices are the native transcript's last samples: no duplexing follows them.
    assert_eq!(d.perm_log.len(), rows.len(), "native duplexing count differs from the schedule's");
    for (r, x) in rows.iter().enumerate() {
        assert_eq!(&d.perm_log[r].0, x, "transcript row {r}: input differs from the native duplexing");
        assert_eq!(d.perm_log[r].1, perm(*x), "transcript row {r}: output differs");
    }
    kt.inp[..rows.len()].copy_from_slice(&rows);
    let xs = query_elements(&s.trows, &rows, s.q);
    assert_eq!(xs, kernel_query_elements(&kt, s));
    let mut paths = 0;
    let mut caps_ok = 0;
    for (qq, &xv) in xs.iter().enumerate() {
        let index = low_of(xv);
        for ti in 0..s.trees.len() {
            let t = &s.trees[ti];
            let bits_of = index >> t.skip;
            assert_eq!(d.idx[ti][qq], (bits_of >> t.consume_lh) as usize, "query {qq} tree {}: index differs from the native check", t.name);
            fill_tree_rows(&mut kt, s, ti, qq, &d.leaves[ti][qq], &d.sibs[ti][qq], bits_of);
            let node = kt.out(s.cap_read_row(qq, ti));
            assert_eq!(node[..8], d.caps[ti][cap_of(xv) as usize][..], "query {qq} tree {}: the path does not end at its cap entry", t.name);
            caps_ok += 1;
            paths += 1;
        }
    }
    set_all_acc(&mut kt, s, &xs);
    for (qq, &xv) in xs.iter().enumerate() {
        for ti in 0..s.trees.len() {
            assert_eq!(kt.acc[s.path_start(qq, ti)], start_of(s, ti, xv), "query {qq} tree {ti}: chained start differs from the shifted element");
        }
    }
    let mem = derive(&mut kt, s, &no_hooks());
    // The caps the kernel's write port puts on the bus are the caps the native verifier checked.
    for ti in 0..s.trees.len() {
        for (j, c) in d.caps[ti].iter().enumerate() {
            assert_eq!(&mem[&Val::Cap(ti, j)][..], &c[..], "tree {ti} cap entry {j}: the bus value differs from the native cap");
        }
    }
    let bs = betas(&s.trows, &rows, s.child.fri_log_arities.len());
    for (r, b) in bs.iter().enumerate() {
        assert_eq!(to_ef(&mem[&Val::Beta(r)]), *b, "beta {r} on the bus differs from the transcript's");
    }
    let (_, fp_first, fp_len) = s.wit_segments.iter().find(|w| w.0 == "fri.final_poly").cloned().unwrap();
    let final_poly: Vec<EF> = d.wit[fp_first..fp_first + fp_len].chunks(8).map(|c| to_ef(c.try_into().unwrap())).collect();
    let fri = native_fri_check(s, &xs, &mem, &bs, &final_poly, &d.native_ro);
    let [_, _, _, zeta, pcs_alpha] = challenges(&s.trows, &rows);
    let deep = native_deep_check(s, &xs, &mem, d, zeta, pcs_alpha);
    assert_eq!(zeta, d.native.zeta, "zeta differs from the native replay's");
    let g1 = native_g1_check(s, &mem, d);
    let report = serde_json::json!({
        "transcript_rows_equal_native_duplexings": rows.len(),
        "native_duplexings": d.perm_log.len(),
        "transcript_initial_capacity_is_zero": d.init.iter().all(|v| *v == F::ZERO),
        "paths_ending_at_their_cap_entries": caps_ok,
        "paths": paths,
        "query_elements": xs.iter().map(|v| v.as_canonical_u32()).collect::<Vec<_>>(),
        "query_indices": xs.iter().map(|v| low_of(*v)).collect::<Vec<_>>(),
        "cap_indices": xs.iter().map(|v| cap_of(*v)).collect::<Vec<_>>(),
        "native_fri_checks": fri,
        "native_deep_checks": deep,
        "native_identity_checks": g1,
    });
    (kt, xs, report)
}

/// The transcript positions of the preprocessed cap's constants with the values of a given cap (the attacker's key's
/// cap for the recomputed-key child; the pinned cap otherwise, where it changes nothing).
pub fn pre_cap_override(s: &Schedule, cap: &[[F; 8]]) -> HashMap<(usize, usize), F> {
    let mut m = HashMap::new();
    if let Some(g) = s.segments.iter().find(|g| g.name == "batch.preprocessed_commitment") {
        let flat: Vec<F> = cap.iter().flatten().copied().collect();
        assert_eq!(flat.len(), g.len);
        for (k, e) in (g.first_event..g.first_event + g.len).enumerate() {
            assert!(matches!(s.events[e], crate::schedule::Ev::Abs(Src::Const(_))));
            m.insert(s.ev_pos[e], flat[k]);
        }
    }
    m
}

/// Self-test of the constraint-side EF8 product (X^8 = 3) against the field's multiplication.
pub fn ef_selftest() {
    use rand::{RngExt, SeedableRng};
    let mut rng = rand::rngs::StdRng::seed_from_u64(0x4b32);
    for _ in 0..64 {
        let a: E8 = core::array::from_fn(|_| rng.random());
        let b: E8 = core::array::from_fn(|_| rng.random());
        let m = ef_mul(&a, &b);
        assert_eq!(m.as_slice(), from_ef(to_ef(&a) * to_ef(&b)).as_slice(), "EF8 product rule differs");
    }
}

