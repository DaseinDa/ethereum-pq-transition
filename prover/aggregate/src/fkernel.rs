//! F2's AIR (L5 layer F2, 2026-11-01): the B1 kernel (code/l5-layer-b1-20261031/b1/kernel.rs, F1's `fkernel.rs`) with
//! one change, the periodic bus control: the bus messages and counts read the 14 bus-control schedule columns that were
//! pure copies (F1: main columns pinned to their periodic columns by `bus.control`) directly from the periodic
//! columns, which F2's prover can now give the permutation-trace generation (p3_batch_stark_c3np, C3n with
//! `periodic_logup`; p3-lookup's own generation reads no periodic column). Two bus-control columns stay in the main
//! trace because they carry prover data, not copies: a cap read's address (the schedule's base plus the cap bits, RA)
//! and a cap entry's write multiplicity (free on a cap entry's write row, WR). Main width 271 - 14 = 257; every other
//! column, constraint and message is B1's, in B1's order; the bus messages and counts take the same values on every
//! row. F1's description of B1's kernel follows.
//!
//! The B1 kernel AIR (L5, 2026-10-31): G1's kernel at 23-bit query indices, the kernel of the layer B that verifies
//! the leaf L0' v2. One table of a batch-STARK proof, one Poseidon2-16 permutation per row, an EF8 arithmetic logic
//! unit (ALU) in parallel columns, a base-field lane, a DEEP Horner lane, and one LogUp memory bus (a named bus,
//! p3-lookup's global kind, over this one instance: its terminal must be zero). G1's kernel (K3b's, generalized to a
//! multi-table batch child: several tables of different heights, a preprocessed round, LogUp, next-row subset openings,
//! cap height 5, roll-ins) with two changes only: the index lane holds 23-bit query indices (`HB` 8 high bits, the
//! canonical check's top bits at `HB[1..8]`), and the bus is named `b-memory`. Every constraint group is G1's; K3a's
//! `deep.pass` rows are used again (the DEEP chains of consecutive single-point matrices joined through their salt rows).
//!
//! The table verifies, entirely by constraints,
//! (K1, ported) the child verifier's Fiat-Shamir transcript from its all-zero state and every Merkle opening of the
//!     child (leaf hash from the zero state, leaf link, position from the transcript's query element);
//! (G1) mixed-height trees: a shorter matrix group's leaf hash is injected into the path by one compression of
//!     (node, group hash) on an injection row (`merkle.inject`: the node on the left, the group hash read from the bus
//!     where the group's last leaf row wrote it); Merkle caps: the path's node after the walked levels is read against
//!     the cap entry its index selects, at a bus address the row computes from the index's cap bits (`merkle.cap`,
//!     `bus.control`), the cap entries being written by the transcript rows that absorb them with a multiplicity the
//!     prover supplies (the read count depends on the query indices); per-tree index widths: a tree of a lower
//!     height starts from the query element shifted right by the difference, read from the bus;
//! (K2, with roll-ins) for every query and every FRI round, the fold of the opened coset with the round's folding
//!     challenge at the coset point the query index fixes, the selection of the coset value at the query's position
//!     and its equality with the previous fold plus, where an input height is reached, beta^arity times that
//!     height's reduced opening; the final polynomial (B1: also a constant one, checked against every last fold);
//! (K3a, per height) the DEEP reduction of the input trees per log height and opening point (zeta and each table's
//!     zeta * g), the input coset point of each height from the tallest one's;
//! (K3b, per table) every table's constraint identity at zeta over its own domain, the LogUp terms in the
//!     constraints, and the global lookup terminal check, as one compiled straight-line program on the ALU.
//!
//! Main columns (F2: width 257; B1: 271):
//! - `0..164` `Poseidon2Air` (KoalaBear width 16, S-box x^3 without registers, 4 + 4 full and 20 partial rounds),
//!   evaluated unchanged through `SubAirBuilder`; inputs `0..16`, outputs `148..164`;
//! - `BIT`, `ACC`, `HB` (8 high bits), `TP` (6 running products): the index lane at 23-bit query indices; on a cap-read
//!   row `HB[0..5]` hold the cap bits;
//! - `XQ`, `X`, `V`, `A`, `B`, `C`, `R`, `CTRL` (F2: 2, the RA address and the WR count; B1: 16), `D` (8), `PW` (32):
//!   K3b's.
//!
//! Control is periodic (period N): the verifier builds it from the child's shape, and the kernel's verifier-key digest
//! covers every value. The bus (`b-memory`) carries messages (address, 8 coordinates) in eight slots per row: RA, RB,
//! RC (ALU operand reads), WR (ALU result or write-port write), WH (Poseidon2 input lanes 0..8), WO (Poseidon2 output
//! lanes 7..0), WV (the base value V), RS (a path's starting accumulator). Every address is written once; its
//! multiplicity is fixed by the schedule, except on a cap entry's write row, where the prover supplies it.
//! Research prototype, trace-level checks without proving; loop-internal self-review; not independently reviewed.
use std::borrow::Cow;
use std::cell::Cell;
use std::collections::HashMap;

use p3_air::{Air, AirBuilder, BaseAir, RowWindow, WindowAccess};
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_koala_bear::{
    GenericPoseidon2LinearLayersKoalaBear, KOALABEAR_POSEIDON2_RC_16_EXTERNAL_FINAL,
    KOALABEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL, KOALABEAR_POSEIDON2_RC_16_INTERNAL, KoalaBear as F,
};
use p3_lookup::{Count, InteractionBuilder, LookupBus};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_poseidon2_air::{Poseidon2Air, RoundConstants, num_cols};
use p3_uni_stark::SubAirBuilder;

pub type P2Air = Poseidon2Air<F, GenericPoseidon2LinearLayersKoalaBear, 16, 3, 0, 4, 20>;
pub const P2W: usize = num_cols::<16, 3, 0, 4, 20>();
pub const IN: usize = 0;
pub const OUT: usize = P2W - 16;
pub const BIT: usize = P2W;
pub const ACC: usize = P2W + 1;
pub const HB: usize = P2W + 2;
/// Bits of the query index (the child's `log_global_max_height`).
pub const LOW_BITS: usize = 23;
pub const HI_BITS: usize = 31 - LOW_BITS;
/// The child's Merkle cap height: every tree's walked path ends `CAP_BITS` levels below the root.
pub const CAP_BITS: usize = 5;
pub const TP: usize = HB + HI_BITS;
pub const TP_N: usize = 6;
pub const XQ: usize = TP + TP_N;
pub const X: usize = XQ + 1;
pub const V: usize = X + 1;
pub const A: usize = V + 1;
pub const B: usize = A + 8;
pub const C: usize = B + 8;
pub const R: usize = C + 8;
pub const CTRL: usize = R + 8;
/// The bus-control schedule columns (periodic), in `CTRL_NAMES` order.
pub const NCTRL: usize = 16;
/// F2: the bus-control columns kept in the main trace, in `CTRL_MAIN_NAMES` order: a cap read's address (the
/// schedule's RA address plus the cap bits) and the WR count (the schedule's, or the prover's on a cap entry's write
/// row). The other 14 bus-control values are read from their periodic columns.
pub const NCTRL_MAIN: usize = 2;
pub const CTRL_MAIN_NAMES: [&str; NCTRL_MAIN] = ["addr_a", "mult_r"];
/// Main column `CTRL + CM_ADDR_A`: slot RA's address.
pub const CM_ADDR_A: usize = 0;
/// Main column `CTRL + CM_MULT_R`: slot WR's count.
pub const CM_MULT_R: usize = 1;
/// The DEEP Horner accumulator (EF8).
pub const DL: usize = CTRL + NCTRL_MAIN;
/// The batching challenge's powers alpha^1..alpha^4 (EF8 each).
pub const PW: usize = DL + 8;
pub const WIDTH: usize = PW + 32;
/// The bus-control schedule columns (periodic), in order (F2: B1's order; only `addr_a` and `mult_r` have a main column).
pub const CTRL_NAMES: [&str; NCTRL] = [
    "addr_a", "rd_a", "addr_b", "rd_b", "addr_c", "rd_c", "addr_r", "mult_r", "addr_h", "mult_h", "addr_o", "mult_o",
    "addr_v", "mult_v", "addr_s", "rd_s",
];
pub const ADDR_A: usize = 0;
pub const RD_A: usize = 1;
pub const ADDR_B: usize = 2;
pub const RD_B: usize = 3;
pub const ADDR_C: usize = 4;
pub const RD_C: usize = 5;
pub const ADDR_R: usize = 6;
pub const MULT_R: usize = 7;
pub const ADDR_H: usize = 8;
pub const MULT_H: usize = 9;
pub const ADDR_O: usize = 10;
pub const MULT_O: usize = 11;
pub const ADDR_V: usize = 12;
pub const MULT_V: usize = 13;
pub const ADDR_S: usize = 14;
pub const RD_S: usize = 15;
pub const BUS: &str = "b-memory";
/// The interaction slots, in emission order.
pub const SLOTS: [&str; 8] = ["RA", "RB", "RC", "WR", "WH", "WO", "WV", "RS"];
/// The binomial extension's X^8 = W for KoalaBear EF8.
pub const EF_W: u32 = 3;

pub fn constants() -> RoundConstants<F, 16, 4, 20> {
    RoundConstants::new(
        KOALABEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL,
        KOALABEAR_POSEIDON2_RC_16_INTERNAL,
        KOALABEAR_POSEIDON2_RC_16_EXTERNAL_FINAL,
    )
}

thread_local! {
    static TAG: Cell<&'static str> = const { Cell::new("") };
}
pub fn tag(t: &'static str) {
    TAG.with(|c| c.set(t));
}
fn current_tag() -> &'static str {
    TAG.with(|c| c.get())
}

/// The ALU opcodes. `Load` only reads operand a (a path start takes its query element from it); `Unpack` is gated
/// by its eight one-hot lane columns; the others are gated by one periodic selector each.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Op {
    Mul,
    Mac,
    Bfly,
    Inv2,
    Eq,
    /// r = kappa + kappa_x X (an EF8 constant; X the basis element 1).
    Const,
    /// r = a + kappa b (kappa the instruction's immediate; kappa = -1 is a subtraction).
    Lin,
    /// a r = 1: the inverse, and a constraint that a is nonzero.
    Inv,
    Load,
    /// r = (a[lane], 0, ..., 0): one coordinate of a bus value (a public value from its transcript row).
    Unpack,
}
pub const OPS: [Op; 8] = [Op::Mul, Op::Mac, Op::Bfly, Op::Inv2, Op::Eq, Op::Const, Op::Lin, Op::Inv];
impl Op {
    pub fn name(self) -> &'static str {
        match self {
            Op::Mul => "mul",
            Op::Mac => "mac",
            Op::Bfly => "bfly",
            Op::Inv2 => "inv2",
            Op::Eq => "eq",
            Op::Const => "const",
            Op::Lin => "lin",
            Op::Inv => "inv",
            Op::Load => "load",
            Op::Unpack => "unpack",
        }
    }
    pub fn group(self) -> &'static str {
        match self {
            Op::Mul => "alu.mul",
            Op::Mac => "alu.mac",
            Op::Bfly => "alu.bfly",
            Op::Inv2 => "alu.inv2",
            Op::Eq => "alu.eq",
            Op::Const => "alu.const",
            Op::Lin => "alu.lin",
            Op::Inv => "alu.inv",
            Op::Load => "alu.load",
            Op::Unpack => "alu.unpack",
        }
    }
}

/// Indices of the periodic control columns.
#[derive(Clone, Debug)]
pub struct PIdx {
    pub cf: [usize; 8],
    pub cv: [usize; 8],
    pub kc: usize,
    pub tag: usize,
    pub kr: [usize; 8],
    pub ivf: usize,
    pub lnk: usize,
    pub cons: usize,
    pub path_t: usize,
    pub start: usize,
    pub pend: usize,
    pub pend_canon: usize,
    pub lsel: [usize; 8],
    pub xs: usize,
    /// The base lane's start value on a path's first row (1 for a FRI round, the coset shift g for the canonical
    /// input tree).
    pub x0: usize,
    pub xp: usize,
    pub xc: usize,
    pub vs: usize,
    pub xce: usize,
    pub vacc: usize,
    pub vsig: usize,
    /// One selector per opcode in `OPS` order.
    pub op: [usize; 8],
    pub kappa: usize,
    /// The CONST instruction's coefficient of X (an EF8 constant kappa + kappa_x X).
    pub kx: usize,
    /// UNPACK's one-hot lane selectors (the coordinate of operand a that the result takes).
    pub unp: [usize; 8],
    /// The schedule of each control column, in `CTRL_NAMES` order.
    pub ctrl: [usize; NCTRL],
    /// DEEP lane: a value row of a chain; the row's accumulator continues into the next row (times alpha^8); the
    /// lanes holding a value; a pass row (D = D'); the row that writes the chain's sum through R.
    pub dv: usize,
    pub dc: usize,
    pub dl: [usize; 8],
    pub dp: usize,
    pub dw: usize,
    /// Claim write rows (claims, cap entries, lookup terminals): the lane holding coordinate 0 (one-hot);
    /// coordinates j >= 1 follow it on this row and continue at lane 0 of the next row.
    pub cs: [usize; 8],
    /// The rows of the ALU instructions that compute alpha^2 (binds PW1 = A, PW2 = R), alpha^3 and alpha^4.
    pub bind: [usize; 3],
    // ---- G1 ----
    /// An injection row: the left input is the previous row's node (BIT = 0), the right input the injected group's
    /// leaf hash read through RA.
    pub inj: usize,
    /// A cap-read row: the last walked node of a path, read through RA at the address of its cap entry (the
    /// schedule's base plus the cap bits HB[0..5]); the cap bits and the query's high part (read through RB) decompose
    /// the accumulator.
    pub capr: usize,
    /// A cap entry's write row (through the write port): its multiplicity is the prover's (free).
    pub capw: usize,
    /// The canonical path's end row: R = (the query's high part, 0, ..., 0) for the cap reads.
    pub hiw: usize,
}

#[derive(Clone)]
pub struct KernelAir {
    pub p2: P2Air,
    pub log_n: usize,
    pub num_public: usize,
    pub periodic: Vec<Vec<F>>,
    pub periodic_names: Vec<String>,
    pub pidx: PIdx,
    pub pub_terms: Vec<Vec<(usize, usize)>>,
    pub k0: usize,
}

impl BaseAir<F> for KernelAir {
    fn width(&self) -> usize {
        WIDTH
    }
    fn num_public_values(&self) -> usize {
        self.num_public
    }
    fn num_periodic_columns(&self) -> usize {
        self.periodic.len()
    }
    fn periodic_columns(&self) -> Cow<'_, [Vec<F>]> {
        Cow::Borrowed(&self.periodic)
    }
}

/// EF8 product of two coordinate vectors (X^8 = 3), over any ring.
pub fn ef_mul<E: PrimeCharacteristicRing + Clone>(a: &[E], b: &[E]) -> Vec<E> {
    let w = E::from_u32(EF_W);
    let mut r = vec![E::ZERO; 8];
    for i in 0..8 {
        for j in 0..8 {
            let p = a[i].clone() * b[j].clone();
            if i + j < 8 {
                r[i + j] = r[i + j].clone() + p;
            } else {
                r[i + j - 8] = r[i + j - 8].clone() + p * w.clone();
            }
        }
    }
    r
}

impl<AB: InteractionBuilder<F = F>> Air<AB> for KernelAir {
    fn eval(&self, b: &mut AB) {
        tag("poseidon2.permutation");
        {
            let mut sub = SubAirBuilder::<AB, P2Air, AB::Var>::new(b, 0..P2W);
            self.p2.eval(&mut sub);
        }
        let main = b.main();
        let lo: Vec<AB::Expr> = main.current_slice().iter().map(|&v| v.into()).collect();
        let nx: Vec<AB::Expr> = main.next_slice().iter().map(|&v| v.into()).collect();
        let per: Vec<AB::Expr> = b.periodic_values().iter().map(|&v| v.into()).collect();
        let pv: Vec<AB::Expr> = b.public_values().iter().map(|&v| v.into()).collect();
        let p = &self.pidx;
        let one = AB::Expr::ONE;
        let c = |v: u64| AB::Expr::from(F::from_u64(v));
        let half = AB::Expr::from(F::ONE.halve());

        // ---- K1, ported: the transcript ----
        tag("transcript.iv");
        b.when_first_row().assert_zero(lo[IN + 8].clone() - c(self.k0 as u64));
        for l in 9..16 {
            b.when_first_row().assert_zero(lo[IN + l].clone());
        }
        for l in self.k0..8 {
            b.when_first_row().assert_zero(lo[IN + l].clone());
        }
        tag("transcript.const");
        for l in 0..8 {
            b.assert_zero(per[p.cf[l]].clone() * (lo[IN + l].clone() - per[p.cv[l]].clone()));
        }
        tag("transcript.public");
        for l in 0..8 {
            let mut e = AB::Expr::ZERO;
            for &(sel, j) in &self.pub_terms[l] {
                e += per[sel].clone() * (lo[IN + l].clone() - pv[j].clone());
            }
            b.assert_zero(e);
        }
        tag("sponge.capacity_chain");
        b.when_transition().assert_zero(per[p.kc].clone() * (nx[IN + 8].clone() - lo[OUT + 8].clone() - per[p.tag].clone()));
        for l in 9..16 {
            b.when_transition().assert_zero(per[p.kc].clone() * (nx[IN + l].clone() - lo[OUT + l].clone()));
        }
        tag("sponge.rate_keep");
        for l in 0..8 {
            b.when_transition().assert_zero(per[p.kr[l]].clone() * (nx[IN + l].clone() - lo[OUT + l].clone()));
        }

        // ---- K1, ported: the Merkle openings ----
        tag("leaf.iv");
        for l in 8..16 {
            b.assert_zero(per[p.ivf].clone() * lo[IN + l].clone());
        }
        tag("merkle.link");
        for l in 0..8 {
            let bit = nx[BIT].clone();
            let left = nx[IN + l].clone() - lo[OUT + l].clone();
            let right = nx[IN + 8 + l].clone() - lo[OUT + l].clone();
            b.when_transition().assert_zero(per[p.lnk].clone() * ((one.clone() - bit.clone()) * left + bit * right));
        }
        // G1: an injection row compresses (node, group hash): the node arrives on the left (BIT = 0 on this row, so
        // `merkle.link` puts the previous row's output there), the group hash is operand a of the row's RA read, in
        // the order the group's last leaf row wrote it (WO: output lanes 7..0).
        tag("merkle.inject");
        b.assert_zero(per[p.inj].clone() * lo[BIT].clone());
        for j in 0..8 {
            b.assert_zero(per[p.inj].clone() * (lo[IN + 8 + j].clone() - lo[A + 7 - j].clone()));
        }
        // G1: a cap-read row (the path's last walked node): operand a is the row's output (the node), read at the
        // address of the cap entry its index selects (`bus.control` adds the cap bits to the schedule's base); the
        // accumulator before this row's bit is BIT + 2 (cap index + 32 HI), with the cap bits boolean and HI the
        // query's high part (operand b, read where the canonical path's end row wrote it).
        tag("merkle.cap");
        let mut cap_idx = AB::Expr::ZERO;
        for k in 0..CAP_BITS {
            cap_idx += lo[HB + k].clone() * c(1 << k);
        }
        for k in 0..8 {
            b.assert_zero(per[p.capr].clone() * (lo[A + k].clone() - lo[OUT + k].clone()));
        }
        for k in 0..CAP_BITS {
            b.assert_zero(per[p.capr].clone() * lo[HB + k].clone() * (lo[HB + k].clone() - one.clone()));
        }
        b.assert_zero(
            per[p.capr].clone()
                * (lo[ACC].clone() - lo[BIT].clone() - cap_idx.clone() * c(2) - lo[B].clone() * c(1 << (CAP_BITS + 1))),
        );
        tag("index.bit_bool");
        b.assert_zero(per[p.cons].clone() * lo[BIT].clone() * (lo[BIT].clone() - one.clone()));
        tag("index.acc_step");
        b.when_transition().assert_zero(
            per[p.path_t].clone() * (nx[ACC].clone() - lo[ACC].clone() + per[p.cons].clone() * (nx[ACC].clone() + lo[BIT].clone())),
        );
        // The path that starts from the transcript's query element reads it from the squeezed vector (operand a of a
        // LOAD on the same row) at the lane the schedule names.
        tag("index.start_lane");
        let mut lane = AB::Expr::ZERO;
        for k in 0..8 {
            lane += per[p.lsel[k]].clone() * (lo[ACC].clone() - lo[A + k].clone());
        }
        b.assert_zero(lane);
        tag("index.xq");
        b.assert_zero(per[p.start].clone() * (lo[XQ].clone() - lo[ACC].clone()));
        b.when_transition().assert_zero(per[p.path_t].clone() * (nx[XQ].clone() - lo[XQ].clone()));
        tag("index.end_recompose");
        let mut hi = AB::Expr::ZERO;
        for i in 0..HI_BITS {
            hi += lo[HB + i].clone() * c(1 << i);
        }
        b.assert_zero(per[p.pend].clone() * (lo[ACC].clone() - lo[BIT].clone() - hi.clone() * c(2)));
        tag("index.end_hi_bool");
        for i in 0..HI_BITS {
            b.assert_zero(per[p.pend].clone() * lo[HB + i].clone() * (lo[HB + i].clone() - one.clone()));
        }
        // Bits 24..30 of the 31-bit value are HB[24 - LOW_BITS ..].
        let top = 24 - LOW_BITS;
        tag("index.end_products");
        b.assert_zero(per[p.pend].clone() * (lo[TP].clone() - lo[HB + top].clone() * lo[HB + top + 1].clone()));
        for k in 1..TP_N {
            b.assert_zero(per[p.pend].clone() * (lo[TP + k].clone() - lo[TP + k - 1].clone() * lo[HB + top + 1 + k].clone()));
        }
        tag("index.end_canonical");
        b.assert_zero(per[p.pend_canon].clone() * lo[TP + TP_N - 1].clone() * (lo[XQ].clone() + one.clone()));
        // G1: the canonical path's end row writes the query's high part through the write port, for the cap reads.
        tag("index.hi_write");
        b.assert_zero(per[p.hiw].clone() * (lo[R].clone() - hi));
        for k in 1..8 {
            b.assert_zero(per[p.hiw].clone() * lo[R + k].clone());
        }

        // ---- K2 and K3a: the base lane (FRI coset points s; the input coset point x = g s) ----
        tag("base.x");
        b.assert_zero(per[p.xs].clone() * lo[X].clone() - per[p.x0].clone());
        b.when_transition().assert_zero(
            per[p.xp].clone() * (nx[X].clone() - lo[X].clone()) - per[p.xc].clone() * lo[X].clone() * lo[BIT].clone(),
        );
        // ---- the base-value slot's payload, per row type ----
        tag("bus.v");
        b.assert_zero(per[p.vacc].clone() * (lo[V].clone() - lo[ACC].clone()));
        b.assert_zero(per[p.vsig].clone() * (lo[V].clone() - half.clone() + lo[BIT].clone()));
        b.assert_zero(per[p.vs].clone() * (lo[V].clone() - lo[X].clone()) - per[p.xce].clone() * lo[X].clone() * lo[BIT].clone());
        // ---- the bus control (G1: a cap read's address adds the cap bits; a cap entry's write multiplicity is free).
        // F2: only these two are main columns; the other 14 bus-control values are the periodic columns themselves,
        // read directly by the bus messages below (B1: 14 main copies, each pinned to its periodic column here). ----
        tag("bus.control");
        b.assert_zero(lo[CTRL + CM_ADDR_A].clone() - per[p.ctrl[ADDR_A]].clone() - per[p.capr].clone() * cap_idx.clone());
        b.assert_zero((one.clone() - per[p.capw].clone()) * (lo[CTRL + CM_MULT_R].clone() - per[p.ctrl[MULT_R]].clone()));

        // ---- the ALU (EF8), gated by the periodic opcode selectors ----
        let a: Vec<AB::Expr> = lo[A..A + 8].to_vec();
        let bb: Vec<AB::Expr> = lo[B..B + 8].to_vec();
        let cc: Vec<AB::Expr> = lo[C..C + 8].to_vec();
        let r: Vec<AB::Expr> = lo[R..R + 8].to_vec();
        let ab = ef_mul(&a, &bb);
        let diff: Vec<AB::Expr> = (0..8).map(|k| a[k].clone() - bb[k].clone()).collect();
        let cd = ef_mul(&cc, &diff);
        let ar = ef_mul(&a, &r);
        let sel = |o: usize| per[p.op[o]].clone();
        tag("alu.mul");
        for k in 0..8 {
            b.assert_zero(sel(0) * (r[k].clone() - ab[k].clone()));
        }
        tag("alu.mac");
        for k in 0..8 {
            b.assert_zero(sel(1) * (r[k].clone() - ab[k].clone() - cc[k].clone()));
        }
        tag("alu.bfly");
        for k in 0..8 {
            b.assert_zero(sel(2) * (r[k].clone() - (a[k].clone() + bb[k].clone()) * half.clone() - cd[k].clone()));
        }
        tag("alu.inv2");
        for k in 0..8 {
            let unit = if k == 0 { one.clone() } else { AB::Expr::ZERO };
            b.assert_zero(sel(3) * (ar[k].clone() * c(2) - unit));
        }
        tag("alu.eq");
        for k in 0..8 {
            b.assert_zero(sel(4) * (a[k].clone() - bb[k].clone()));
        }
        tag("alu.const");
        for k in 0..8 {
            let kv = match k {
                0 => per[p.kappa].clone(),
                1 => per[p.kx].clone(),
                _ => AB::Expr::ZERO,
            };
            b.assert_zero(sel(5) * (r[k].clone() - kv));
        }
        tag("alu.lin");
        for k in 0..8 {
            b.assert_zero(sel(6) * (r[k].clone() - a[k].clone()) - per[p.kappa].clone() * bb[k].clone() * sel(6));
        }
        // a r = 1 (EF8): the inverse exists only for a nonzero a, so a zero denominator z - x cannot be inverted.
        tag("alu.inv");
        for k in 0..8 {
            let unit = if k == 0 { one.clone() } else { AB::Expr::ZERO };
            b.assert_zero(sel(7) * (ar[k].clone() - unit));
        }
        // r = (a[lane], 0, ..., 0) on an UNPACK row (one lane selector is 1; on every other row all are 0).
        tag("alu.unpack");
        let mut on = AB::Expr::ZERO;
        let mut pick = AB::Expr::ZERO;
        for k in 0..8 {
            on += per[p.unp[k]].clone();
            pick += per[p.unp[k]].clone() * a[k].clone();
        }
        b.assert_zero(on.clone() * r[0].clone() - pick);
        for k in 1..8 {
            b.assert_zero(on.clone() * r[k].clone());
        }

        // ---- K3a: the batching challenge's powers, constant over the trace and bound to the ALU ----
        let pw: Vec<Vec<AB::Expr>> = (0..4).map(|i| lo[PW + 8 * i..PW + 8 * i + 8].to_vec()).collect();
        tag("deep.const");
        for k in 0..32 {
            b.when_transition().assert_zero(nx[PW + k].clone() - lo[PW + k].clone());
        }
        tag("deep.bind");
        for k in 0..8 {
            b.assert_zero(per[p.bind[0]].clone() * (pw[0][k].clone() - a[k].clone()));
            b.assert_zero(per[p.bind[0]].clone() * (pw[1][k].clone() - r[k].clone()));
            b.assert_zero(per[p.bind[1]].clone() * (pw[2][k].clone() - r[k].clone()));
            b.assert_zero(per[p.bind[2]].clone() * (pw[3][k].clone() - r[k].clone()));
        }
        // ---- K3a: the DEEP Horner lane on the input trees' leaf rows ----
        // On a value row: D = D' alpha^8 + sum_l IN_l alpha^l over the lanes that hold a value of the chain (D' only
        // when the chain continues on the next row); on a pass row: D = D'.
        let d: Vec<AB::Expr> = lo[DL..DL + 8].to_vec();
        let dn: Vec<AB::Expr> = nx[DL..DL + 8].to_vec();
        let a8 = ef_mul(&ef_mul(&dn, &pw[3]), &pw[3]);
        let mut coef: Vec<Vec<AB::Expr>> = vec![];
        coef.push((0..8).map(|k| if k == 0 { one.clone() } else { AB::Expr::ZERO }).collect());
        for i in 0..4 {
            coef.push(pw[i].clone());
        }
        for i in 0..3 {
            coef.push(ef_mul(&pw[3], &pw[i]));
        }
        tag("deep.lane");
        for k in 0..8 {
            let mut e = per[p.dv].clone() * d[k].clone() - per[p.dc].clone() * a8[k].clone();
            for l in 0..8 {
                e -= per[p.dl[l]].clone() * lo[IN + l].clone() * coef[l][k].clone();
            }
            b.when_transition().assert_zero(e);
        }
        tag("deep.pass");
        for k in 0..8 {
            b.when_transition().assert_zero(per[p.dp].clone() * (d[k].clone() - dn[k].clone()));
        }
        tag("deep.write");
        for k in 0..8 {
            b.assert_zero(per[p.dw].clone() * (r[k].clone() - d[k].clone()));
        }
        // ---- K3a: a claim's write row (claims, cap entries, terminals): R = the eight absorbed coordinates ----
        tag("claim.write");
        for j in 0..8 {
            let mut e = AB::Expr::ZERO;
            for s in 0..8 {
                let src = if s + j < 8 { lo[IN + s + j].clone() } else { nx[IN + s + j - 8].clone() };
                e += per[p.cs[s]].clone() * (r[j].clone() - src);
            }
            b.when_transition().assert_zero(e);
        }

        // ---- the LogUp memory bus (named, global kind, one instance): messages (address, 8 coordinates) ----
        tag("bus.logup");
        let bus = LookupBus::new(BUS);
        // F2: the schedule's bus control read from its periodic column (B1: `lo[CTRL + k]`, a main copy of it).
        let pc = |k: usize| per[p.ctrl[k]].clone();
        let msg = |addr: AB::Expr, vals: Vec<AB::Expr>| -> Vec<AB::Expr> { std::iter::once(addr).chain(vals).collect() };
        let base = |v: AB::Expr| -> Vec<AB::Expr> { std::iter::once(v).chain((1..8).map(|_| AB::Expr::ZERO)).collect() };
        bus.lookup_key(b, msg(lo[CTRL + CM_ADDR_A].clone(), a.clone()), Count::bounded(pc(RD_A), 1));
        bus.lookup_key(b, msg(pc(ADDR_B), bb.clone()), Count::bounded(pc(RD_B), 1));
        bus.lookup_key(b, msg(pc(ADDR_C), cc.clone()), Count::bounded(pc(RD_C), 1));
        bus.table_entry(b, msg(pc(ADDR_R), r.clone()), lo[CTRL + CM_MULT_R].clone());
        bus.table_entry(b, msg(pc(ADDR_H), lo[IN..IN + 8].to_vec()), pc(MULT_H));
        bus.table_entry(b, msg(pc(ADDR_O), (0..8).map(|k| lo[OUT + 7 - k].clone()).collect()), pc(MULT_O));
        bus.table_entry(b, msg(pc(ADDR_V), base(lo[V].clone())), pc(MULT_V));
        bus.lookup_key(b, msg(pc(ADDR_S), base(lo[ACC].clone())), Count::bounded(pc(RD_S), 1));
    }
}

/// A row-by-row evaluation of every constraint (the same `eval` as the prover and the verifier), recording the
/// failing ones with their group name, and every bus message with its signed count.
pub struct CheckBuilder<'a> {
    local: &'a [F],
    next: &'a [F],
    empty: RowWindow<'a, F>,
    per: &'a [F],
    pv: &'a [F],
    first: F,
    last: F,
    trans: F,
    idx: usize,
    pub fails: Vec<(usize, &'static str)>,
    pub msgs: Vec<(usize, Vec<F>, F)>,
    /// Record every constraint (its group), not only the failing ones.
    all: bool,
}

/// The group of every base constraint, in evaluation order (the order of the symbolic constraints).
pub fn constraint_tags(air: &KernelAir, num_public: usize) -> Vec<&'static str> {
    let zeros = vec![F::ZERO; WIDTH];
    let per = vec![F::ZERO; air.periodic.len()];
    let pv = vec![F::ZERO; num_public];
    let empty: [F; 0] = [];
    let mut b = CheckBuilder {
        local: &zeros,
        next: &zeros,
        empty: RowWindow::from_two_rows(&empty, &empty),
        per: &per,
        pv: &pv,
        first: F::ONE,
        last: F::ZERO,
        trans: F::ONE,
        idx: 0,
        fails: vec![],
        msgs: vec![],
        all: true,
    };
    air.eval(&mut b);
    b.fails.into_iter().map(|(_, t)| t).collect()
}

impl<'a> AirBuilder for CheckBuilder<'a> {
    type F = F;
    type Expr = F;
    type Var = F;
    type PreprocessedWindow = RowWindow<'a, F>;
    type MainWindow = RowWindow<'a, F>;
    type PublicVar = F;
    type PeriodicVar = F;

    fn main(&self) -> Self::MainWindow {
        RowWindow::from_two_rows(self.local, self.next)
    }
    fn preprocessed(&self) -> &Self::PreprocessedWindow {
        &self.empty
    }
    fn is_first_row(&self) -> F {
        self.first
    }
    fn is_last_row(&self) -> F {
        self.last
    }
    fn is_transition(&self) -> F {
        self.trans
    }
    fn assert_zero<I: Into<F>>(&mut self, x: I) {
        if self.all || x.into() != F::ZERO {
            self.fails.push((self.idx, current_tag()));
        }
        self.idx += 1;
    }
    fn public_values(&self) -> &[F] {
        self.pv
    }
    fn periodic_values(&self) -> &[F] {
        self.per
    }
}

impl<'a> InteractionBuilder for CheckBuilder<'a> {
    fn push_interaction<E: Into<F>>(&mut self, _bus: &str, fields: impl IntoIterator<Item = E>, count: impl Into<Count<F>>) {
        let slot = self.msgs.len();
        let (cnt, _) = count.into().into_parts();
        self.msgs.push((slot, fields.into_iter().map(Into::into).collect(), cnt));
    }
    fn push_local_interaction(&mut self, tuples: impl IntoIterator<Item = (Vec<F>, Count<F>)>) {
        tuples.into_iter().for_each(drop);
    }
    fn num_global_interactions(&self) -> usize {
        self.msgs.len()
    }
}

#[derive(Clone, Debug)]
pub struct Failure {
    pub row: usize,
    pub constraint: usize,
    pub group: &'static str,
}

/// One unbalanced bus tuple: (address, coordinates), net signed count, rows that carry it.
#[derive(Clone, Debug)]
pub struct Unbalanced {
    pub address: u32,
    pub values: Vec<u32>,
    pub net: i64,
    pub rows: Vec<(usize, &'static str, i64)>,
}

fn signed(v: F) -> i64 {
    let x = v.as_canonical_u32() as i64;
    if x > (F::ORDER_U32 as i64) / 2 { x - F::ORDER_U32 as i64 } else { x }
}

/// Evaluate every constraint on every row (the next row of the last row is row 0) and count every bus tuple exactly.
/// Returns (constraints per row, failures, unbalanced tuples, messages with a nonzero count).
pub fn check(air: &KernelAir, trace: &RowMajorMatrix<F>, pv: &[F]) -> (usize, Vec<Failure>, Vec<Unbalanced>, usize) {
    let n = trace.height();
    let w = trace.width();
    assert_eq!(w, WIDTH);
    let empty: [F; 0] = [];
    let mut fails = vec![];
    let mut per_row = vec![F::ZERO; air.periodic.len()];
    let mut constraints = 0;
    let mut tuples: HashMap<Vec<u32>, (i64, Vec<(usize, &'static str, i64)>)> = HashMap::new();
    let mut live = 0;
    for i in 0..n {
        let j = (i + 1) % n;
        for (k, col) in air.periodic.iter().enumerate() {
            per_row[k] = col[i % col.len()];
        }
        let mut b = CheckBuilder {
            local: &trace.values[i * w..(i + 1) * w],
            next: &trace.values[j * w..(j + 1) * w],
            empty: RowWindow::from_two_rows(&empty, &empty),
            per: &per_row,
            pv,
            first: if i == 0 { F::ONE } else { F::ZERO },
            last: if i == n - 1 { F::ONE } else { F::ZERO },
            trans: if i == n - 1 { F::ZERO } else { F::ONE },
            idx: 0,
            fails: vec![],
            msgs: vec![],
            all: false,
        };
        air.eval(&mut b);
        constraints = b.idx;
        for (k, g) in b.fails {
            fails.push(Failure { row: i, constraint: k, group: g });
        }
        for (slot, fields, cnt) in b.msgs {
            if cnt == F::ZERO {
                continue;
            }
            live += 1;
            let key: Vec<u32> = fields.iter().map(|v| v.as_canonical_u32()).collect();
            let e = tuples.entry(key).or_default();
            e.0 += signed(cnt);
            e.1.push((i, SLOTS[slot], signed(cnt)));
        }
    }
    let mut unbalanced: Vec<Unbalanced> = tuples
        .into_iter()
        .filter(|(_, (net, _))| *net != 0)
        .map(|(k, (net, rows))| Unbalanced { address: k[0], values: k[1..].to_vec(), net, rows })
        .collect();
    unbalanced.sort_by_key(|u| (u.address, u.rows.first().map(|r| r.0)));
    (constraints, fails, unbalanced, live)
}
