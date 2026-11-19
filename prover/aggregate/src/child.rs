//! The g1b child (L5 layer B1, 2026-10-31): G1's small synthetic batch-STARK child in B's configuration, the
//! small-scale child of B1's negatives. G1's three tables, proven with `p3_batch_stark_c3n` (L0' v2's C3n copy of
//! p3-batch-stark), with the changes that put the interfaces L0' v2 needs and G1's child did not have into a small child:
//! - heights 2^8 (A), 2^11 (B) and 2^16 (C) (G1: 2^8, 2^10, 2^12): LDE heights 2^15, 2^18 and 2^23, so 23-bit query
//!   indices and L0' v2's fold schedule [4, 4, 2, 4, 2, 4, 4, 4, 4, 2], with the lower heights rolled in after the
//!   arity-2 rounds 2 and 4;
//! - a second global LogUp bus `g1b-second`: A looks up (a0), B provides (b0) with multiplicity b2 (two buses with
//!   tuples of widths 2 and 1, two lookups in A and in B);
//! - (main.rs) a constant final polynomial (log_final_poly_len 0) and L0' v2's kind of prefix: four constant
//!   absorptions (domain, AIR digest, descriptor, program digest), the statement being the tables' public values.
//!
//! - **A** (2^8 rows, 4 main columns, 3 preprocessed columns P0 = r, P1 = r^2, P2 = 5 r + 1 under the seeded, pinned
//!   key commitment): a0 = P0, a1 = a0 P1 (= r^3), a2 a running sum (a2 = 0 on the first row, a2' = a2 + a1 on every
//!   transition: the only column read at the next row, so the main trace is committed as two matrices), a3 = a1 + P2;
//!   it looks up (a0, a1) on `g1-child` and (a0) on `g1b-second` once per row.
//! - **B** (2^11 rows, 11 main columns): b1 = b0^3 (degree 3), b2 boolean; it provides (b0, b1) on `g1-child` and
//!   (b0) on `g1b-second` with multiplicity b2 (the honest trace: b0 = k, b2 = 1 for k < 256); columns 3..11 hold its 8
//!   public values on the first row (bytes 0..8 of PI198). It reads nothing at the next row (one main matrix at zeta).
//! - **C** (2^16 rows, 8 main columns): a Fibonacci pair, a product and four running sums, every column read at the
//!   next row (one main matrix at zeta and zeta * g); its 8 public values (bytes 8..16 of PI198) are the first row.
//!
//! Every table's permutation trace (A and B: the LogUp accumulator and two fraction columns) is read at the next row in
//! its accumulator only, so it is committed as two matrices. Research prototype, trace-level checks without proving;
//! loop-internal self-review; not independently reviewed.
use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::{Dup, PrimeCharacteristicRing, PrimeField64};
use p3_koala_bear::KoalaBear as F;
use p3_lookup::{InteractionBuilder, LookupBus};
use p3_matrix::dense::RowMajorMatrix;

pub const BUS_NAME: &str = "g1-child";
pub const BUS2_NAME: &str = "g1b-second";
pub const LOG_A: usize = 8;
pub const LOG_B: usize = 11;
pub const LOG_C: usize = 16;
pub const WIDTH_A: usize = 4;
pub const WIDTH_B: usize = 11;
pub const WIDTH_C: usize = 8;
pub const PRE_A: usize = 3;
pub const PUB_B: usize = 8;
pub const PUB_C: usize = 8;
/// The statement bytes each table binds as its public values: B bytes 0..8, C bytes 8..16 of PI198.
pub const PUB_B_FIRST: usize = 0;
pub const PUB_C_FIRST: usize = 8;
pub const TABLE_NAMES: [&str; 3] = ["A", "B", "C"];
pub const LOGS: [usize; 3] = [LOG_A, LOG_B, LOG_C];
pub const WIDTHS: [usize; 3] = [WIDTH_A, WIDTH_B, WIDTH_C];

#[derive(Clone, Debug)]
pub struct TableA {
    /// The preprocessed program: P0 = r, P1 = r^2, P2 = 5 r + 1 (or a tampered copy, for the attacker's key only).
    pub program: Vec<Vec<u64>>,
}
#[derive(Clone, Debug)]
pub struct TableB;
#[derive(Clone, Debug)]
pub struct TableC {
    /// The constant added in the transition c3' = c3 + c0 + k (0 for the child; another AIR of the same shape uses 1).
    pub k: u64,
}

#[derive(Clone, Debug)]
pub enum G1Air {
    A(TableA),
    B(TableB),
    C(TableC),
}

pub fn program_a() -> Vec<Vec<u64>> {
    let n = 1u64 << LOG_A;
    vec![(0..n).collect(), (0..n).map(|r| r * r).collect(), (0..n).map(|r| 5 * r + 1).collect()]
}

pub fn airs() -> Vec<G1Air> {
    vec![G1Air::A(TableA { program: program_a() }), G1Air::B(TableB), G1Air::C(TableC { k: 0 })]
}

fn program_matrix<V: PrimeCharacteristicRing + Send + Sync + Clone>(cols: &[Vec<u64>]) -> RowMajorMatrix<V> {
    let height = cols[0].len();
    let values = (0..height).flat_map(|r| cols.iter().map(move |c| V::from_u64(c[r]))).collect();
    RowMajorMatrix::new(values, cols.len())
}

impl<V: PrimeField64> BaseAir<V> for G1Air {
    fn width(&self) -> usize {
        match self {
            Self::A(_) => WIDTH_A,
            Self::B(_) => WIDTH_B,
            Self::C(_) => WIDTH_C,
        }
    }
    fn num_public_values(&self) -> usize {
        match self {
            Self::A(_) => 0,
            Self::B(_) => PUB_B,
            Self::C(_) => PUB_C,
        }
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<V>> {
        match self {
            Self::A(a) => Some(program_matrix(&a.program)),
            _ => None,
        }
    }
    fn preprocessed_width(&self) -> usize {
        match self {
            Self::A(a) => a.program.len(),
            _ => 0,
        }
    }
    fn num_periodic_columns(&self) -> usize {
        0
    }
    fn periodic_columns(&self) -> std::borrow::Cow<'_, [Vec<V>]> {
        std::borrow::Cow::Owned(vec![])
    }
    fn periodic_periods(&self) -> Vec<usize> {
        vec![]
    }
    fn max_constraint_degree(&self) -> Option<usize> {
        None
    }
}

impl<AB: InteractionBuilder> Air<AB> for G1Air
where
    AB::F: PrimeField64,
{
    fn eval(&self, b: &mut AB) {
        let main = b.main();
        let l: Vec<AB::Expr> = main.current_slice().iter().map(|&v| v.into()).collect();
        let n: Vec<AB::Expr> = main.next_slice().iter().map(|&v| v.into()).collect();
        let bus = LookupBus::new(BUS_NAME);
        let bus2 = LookupBus::new(BUS2_NAME);
        match self {
            Self::A(_) => {
                let pre: Vec<AB::Expr> = b.preprocessed().current_slice().iter().map(|&p| p.into()).collect();
                assert_eq!(pre.len(), PRE_A);
                b.assert_zero(l[0].dup() - pre[0].dup());
                b.assert_zero(l[1].dup() - l[0].dup() * pre[1].dup());
                b.when_first_row().assert_zero(l[2].dup());
                b.when_transition().assert_zero(n[2].dup() - l[2].dup() - l[1].dup());
                b.assert_zero(l[3].dup() - l[1].dup() - pre[2].dup());
                bus.lookup_key(b, [l[0].dup(), l[1].dup()], 1);
                bus2.lookup_key(b, [l[0].dup()], 1);
            }
            Self::B(_) => {
                let pv: Vec<AB::Expr> = b.public_values().iter().map(|&p| p.into()).collect();
                b.assert_zero(l[1].dup() - l[0].dup() * l[0].dup() * l[0].dup());
                b.assert_zero(l[2].dup() * (l[2].dup() - AB::Expr::ONE));
                for j in 0..PUB_B {
                    b.when_first_row().assert_zero(l[3 + j].dup() - pv[j].dup());
                }
                bus.table_entry(b, [l[0].dup(), l[1].dup()], l[2].dup());
                bus2.table_entry(b, [l[0].dup()], l[2].dup());
            }
            Self::C(c) => {
                let pv: Vec<AB::Expr> = b.public_values().iter().map(|&p| p.into()).collect();
                for j in 0..PUB_C {
                    b.when_first_row().assert_zero(l[j].dup() - pv[j].dup());
                }
                let k = AB::Expr::from_u64(c.k);
                b.when_transition().assert_zero(n[0].dup() - l[1].dup());
                b.when_transition().assert_zero(n[1].dup() - l[0].dup() - l[1].dup());
                b.when_transition().assert_zero(n[2].dup() - l[2].dup() * l[3].dup());
                b.when_transition().assert_zero(n[3].dup() - l[3].dup() - l[0].dup() - k);
                for j in 0..4 {
                    b.when_transition().assert_zero(n[4 + j].dup() - l[4 + j].dup() - l[j].dup());
                }
            }
        }
    }
}

/// What a child's prover does differently from the honest one (the trace side; the proof side is in main.rs).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fault {
    /// One cell (table, row, column) plus one after generation.
    Cell(usize, usize, usize),
    /// B's multiplicity of key `k` set to 0 (b2 stays boolean): the lookups of (k, k^3) and (k) by A have no provider.
    Unbalanced(usize),
    /// A's preprocessed column P2 at row `r` plus one, the main trace consistent with it (a3); the key recomputed.
    Pre(usize),
}

/// The three traces of the child for the statement `pi` (198 bytes), with an optional fault; `c_k` is table C's
/// transition constant (0 for the child).
pub fn traces(pi: &[u8], fault: Option<Fault>, c_k: u64) -> [RowMajorMatrix<F>; 3] {
    let mut prog = program_a();
    if let Some(Fault::Pre(r)) = fault {
        prog[2][r] += 1;
    }
    let na = 1usize << LOG_A;
    let mut a = vec![F::ZERO; na * WIDTH_A];
    let mut run = F::ZERO;
    for r in 0..na {
        let a0 = F::from_u64(prog[0][r]);
        let a1 = a0 * F::from_u64(prog[1][r]);
        let row = &mut a[r * WIDTH_A..(r + 1) * WIDTH_A];
        row[0] = a0;
        row[1] = a1;
        row[2] = run;
        row[3] = a1 + F::from_u64(prog[2][r]);
        run += a1;
    }
    let nb = 1usize << LOG_B;
    let mut bt = vec![F::ZERO; nb * WIDTH_B];
    for k in 0..nb {
        let row = &mut bt[k * WIDTH_B..(k + 1) * WIDTH_B];
        let b0 = F::from_usize(k);
        row[0] = b0;
        row[1] = b0 * b0 * b0;
        row[2] = if k < na { F::ONE } else { F::ZERO };
        for j in 0..PUB_B {
            row[3 + j] = if k == 0 { F::from_u8(pi[PUB_B_FIRST + j]) } else { F::from_usize((k * (j + 3)) % 251) };
        }
    }
    if let Some(Fault::Unbalanced(k)) = fault {
        bt[k * WIDTH_B + 2] = F::ZERO;
    }
    let nc = 1usize << LOG_C;
    let mut ct = vec![F::ZERO; nc * WIDTH_C];
    for j in 0..PUB_C {
        ct[j] = F::from_u8(pi[PUB_C_FIRST + j]);
    }
    for r in 1..nc {
        let (prev, cur) = ct.split_at_mut(r * WIDTH_C);
        let p = &prev[(r - 1) * WIDTH_C..r * WIDTH_C];
        let c = &mut cur[..WIDTH_C];
        c[0] = p[1];
        c[1] = p[0] + p[1];
        c[2] = p[2] * p[3];
        c[3] = p[3] + p[0] + F::from_u64(c_k);
        for j in 0..4 {
            c[4 + j] = p[4 + j] + p[j];
        }
    }
    let mut out = [RowMajorMatrix::new(a, WIDTH_A), RowMajorMatrix::new(bt, WIDTH_B), RowMajorMatrix::new(ct, WIDTH_C)];
    if let Some(Fault::Cell(t, r, c)) = fault {
        let w = WIDTHS[t];
        out[t].values[r * w + c] += F::ONE;
    }
    out
}

/// The tables' public values for a statement: A none, B bytes 0..8, C bytes 8..16 of PI198.
pub fn public_values(pi: &[u8]) -> Vec<Vec<F>> {
    vec![
        vec![],
        pi[PUB_B_FIRST..PUB_B_FIRST + PUB_B].iter().map(|&v| F::from_u8(v)).collect(),
        pi[PUB_C_FIRST..PUB_C_FIRST + PUB_C].iter().map(|&v| F::from_u8(v)).collect(),
    ]
}

/// The constraints each table has by construction (base constraints of the AIR, before the lookups' extension
/// constraints): A 5, B 2 + 8, C 8 + 4 + 4.
pub fn base_constraints_by_construction(t: usize) -> usize {
    [5, 2 + PUB_B, PUB_C + 8][t]
}
