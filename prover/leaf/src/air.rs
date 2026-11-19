//! Three tables of one batch-STARK:
//! - the field-operation table (one operation modulo the secp256k1 field prime p, or modulo the group
//!   order n where the modulus selector is set, per row; 291 main columns), whose program (operation
//!   kinds, memory ids, moduli, constants, public-value selectors) is periodic, i.e. public and
//!   computed by the verifier, never committed;
//! - the byte-pair table (65,536 rows, one multiplicity column), the range table of every byte limb;
//! - the Keccak table (S4b): `p3-keccak-air` unchanged, plus a wrapper keyed by its `export` flag.
//! Buses: `mem` (write-once memory: a producing row provides (id, 32 limbs) with its read count,
//! each read looks it up), `range` (each (byte, byte) pair of q, r and the carries is looked up) and
//! `keccak-in` (the 64-byte message x || y of k5's point as 32 little-endian byte pairs: looked up by
//! the field-operation table's Keccak input row, provided by the Keccak table's export row).
//!
//! L5 leaf L0' (2026-10-31), change C4a and nothing else: the field-operation table's program, the 51
//! columns of 16,384 rows that S5 declared periodic (`program::periodic`, `program::per`), is now the
//! table's preprocessed trace. The verifier no longer interpolates it; the PCS commits it once, at key
//! generation, and the commitment is part of the verifying key. Every constraint reads the same program
//! value on the same row as in S5. The byte-pair and SHA-512 tables keep their periodic columns.
//!
//! L5 leaf L0' v2 (2026-10-31), C4a for every periodic column and nothing else: the byte-pair table's 2
//! columns (period 65,536, its height) and the SHA-512 table's 123 columns (period 2,048, its height) are
//! now those tables' preprocessed traces, committed with the field-operation program under the one key
//! commitment. A periodic column whose period is the table's height is the full column, so each
//! preprocessed column holds exactly the values the periodic column took on every row, and every
//! constraint reads the same value on the same row as in S5 and L0'. No periodic column remains.
use std::sync::Arc;

use p3_air::{Air, BaseAir, WindowAccess};
use p3_field::{Dup, PrimeCharacteristicRing, PrimeField64};
use p3_keccak_air::{KeccakAir, NUM_KECCAK_COLS, output_limb};
use p3_lookup::{Count, InteractionBuilder, LookupBus};
use p3_matrix::dense::RowMajorMatrix;

use crate::keccak::{ADDRESS_BYTES, ADDRESS_OFFSET, EXPORT, MESSAGE_PAIRS, PI_BYTES, padding_limb, preimage_col};
use crate::program::{CARRIES, CARRY_OFFSET, LIMBS, PUBLIC_BLOCKS, col, pair_col, per};

pub const MEM: &str = "mem";
pub const RANGE: &str = "range";
pub const KECCAK_IN: &str = "keccak-in";

#[derive(Clone, Debug)]
pub struct FieldOpAir {
    /// The program: `per::NUM` (51) columns of `program::HEIGHT` rows, as `program::periodic` builds them.
    /// C4a: committed as this table's preprocessed trace instead of being declared periodic.
    pub program: Arc<Vec<Vec<u64>>>,
    pub p_limbs: [u64; LIMBS],
    pub n_limbs: [u64; LIMBS],
    /// Scalar bits must be the integers 0 or 1. Off only in the unsound variant of one control.
    pub canonical_bits: bool,
}

#[derive(Clone, Debug)]
pub struct BytePairAir {
    /// The (low, high) byte columns, `program::pair_periodic` (2 columns of `program::PAIR_HEIGHT` rows).
    /// v2: committed as this table's preprocessed trace instead of being declared periodic.
    pub program: Arc<Vec<Vec<u64>>>,
}

/// `p3-keccak-air` with the wrapper of S4b; its public values are the 198 bytes of `PI_bytes` (S4d).
#[derive(Clone, Debug)]
pub struct KeccakTableAir;

/// The SHA-512 table of S4c (`sha.rs`); its program is the program's SHA part, `sha::periodic` (123 columns
/// of `sha::HEIGHT` rows). v2: committed as this table's preprocessed trace instead of being declared periodic.
#[derive(Clone, Debug)]
pub struct ShaAir {
    pub program: Arc<Vec<Vec<u64>>>,
}

#[derive(Clone, Debug)]
pub enum Ag1Air {
    FieldOp(FieldOpAir),
    BytePair(BytePairAir),
    Keccak(KeccakTableAir),
    Sha(ShaAir),
}

/// C4a: the program columns as a row-major matrix (row r holds every column's value at row r).
fn program_matrix<F: PrimeCharacteristicRing + Send + Sync + Clone>(cols: &[Vec<u64>]) -> RowMajorMatrix<F> {
    let height = cols[0].len();
    assert!(cols.iter().all(|c| c.len() == height), "program columns of one height");
    let values = (0..height).flat_map(|r| cols.iter().map(move |c| F::from_u64(c[r]))).collect();
    RowMajorMatrix::new(values, cols.len())
}

impl<F: PrimeField64> BaseAir<F> for Ag1Air {
    fn width(&self) -> usize {
        match self { Self::FieldOp(_) => col::WIDTH, Self::BytePair(_) => pair_col::WIDTH, Self::Keccak(_) => NUM_KECCAK_COLS, Self::Sha(_) => crate::sha::WIDTH }
    }
    fn num_public_values(&self) -> usize {
        match self { Self::FieldOp(_) => PUBLIC_BLOCKS * LIMBS, Self::BytePair(_) => 0, Self::Keccak(_) => PI_BYTES, Self::Sha(_) => 0 }
    }
    /// C4a: the field-operation table's program is its preprocessed trace; v2: so are the byte-pair table's and the
    /// SHA-512 table's. The Keccak table has none.
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        match self {
            Self::FieldOp(a) => Some(program_matrix(&a.program)),
            Self::BytePair(a) => Some(program_matrix(&a.program)),
            Self::Keccak(_) => None,
            Self::Sha(a) => Some(program_matrix(&a.program)),
        }
    }
    fn preprocessed_width(&self) -> usize {
        match self { Self::FieldOp(a) => a.program.len(), Self::BytePair(a) => a.program.len(), Self::Keccak(_) => 0, Self::Sha(a) => a.program.len() }
    }
    /// v2: no table declares a periodic column.
    fn num_periodic_columns(&self) -> usize {
        0
    }
    fn periodic_columns(&self) -> std::borrow::Cow<'_, [Vec<F>]> {
        std::borrow::Cow::Owned(vec![])
    }
    fn periodic_periods(&self) -> Vec<usize> {
        vec![]
    }
    fn max_constraint_degree(&self) -> Option<usize> { None }
}

impl<AB: InteractionBuilder> Air<AB> for Ag1Air
where
    AB::F: PrimeField64,
{
    fn eval(&self, b: &mut AB) {
        match self {
            Self::FieldOp(a) => eval_field_op(a, b),
            Self::BytePair(_) => {
                let main = b.main();
                let l = main.current_slice().to_vec();
                let x = |c: usize| -> AB::Expr { l[c].into() };
                // v2: the (low, high) bytes are read from the preprocessed trace (S5 and L0': from the periodic values).
                let per: Vec<AB::Expr> = b.preprocessed().current_slice().iter().map(|&p| p.into()).collect();
                assert_eq!(per.len(), 2);
                b.assert_zero(x(pair_col::LO) - per[0].dup());
                b.assert_zero(x(pair_col::HI) - per[1].dup());
                LookupBus::new(RANGE).table_entry(b, [x(pair_col::LO), x(pair_col::HI)], x(pair_col::MULT));
            }
            Self::Keccak(_) => eval_keccak(b),
            Self::Sha(_) => crate::sha::eval(b),
        }
    }
}

/// `p3-keccak-air` unchanged, then the wrapper on rows whose `export` flag is set (the AIR allows it only
/// on a final-round row, boolean): the block padding after the 64-byte message and a zero capacity, the
/// output bytes 12..32 equal to `legacy_address` in the public `PI_bytes`, and the message's 32 byte
/// pairs provided to the `keccak-in` bus with multiplicity `export`. The bus has one consumer, so exactly
/// one export row carries the message.
fn eval_keccak<AB: InteractionBuilder>(b: &mut AB)
where
    AB::F: PrimeField64,
{
    <KeccakAir as Air<AB>>::eval(&KeccakAir {}, b);
    let main = b.main();
    let l = main.current_slice().to_vec();
    let x = |c: usize| -> AB::Expr { l[c].into() };
    // The public values are the 198 bytes of PI_bytes (S4d); the transcript absorbs all of them, and the
    // address is read from its legacy_address field.
    let pv: Vec<AB::Expr> = b.public_values().iter().map(|&p| p.into()).collect();
    assert_eq!(pv.len(), PI_BYTES);
    let export = x(EXPORT);
    for t in MESSAGE_PAIRS..100 {
        b.assert_zero(export.dup() * (x(preimage_col(t)) - AB::Expr::from_u64(padding_limb(t))));
    }
    let k256 = AB::Expr::from_u64(256);
    for t in 0..ADDRESS_BYTES / 2 {
        let pair = pv[ADDRESS_OFFSET + 2 * t].dup() + pv[ADDRESS_OFFSET + 2 * t + 1].dup() * k256.dup();
        b.assert_zero(export.dup() * (x(output_limb(6 + t)) - pair));
    }
    let message: Vec<AB::Expr> = (0..MESSAGE_PAIRS).map(|t| x(preimage_col(t))).collect();
    LookupBus::new(KECCAK_IN).table_entry(b, message, export);
}

fn eval_field_op<AB: InteractionBuilder>(air: &FieldOpAir, b: &mut AB)
where
    AB::F: PrimeField64,
{
    let main = b.main();
    let l = main.current_slice().to_vec();
    // C4a: the program row is read from the preprocessed trace (S5: from the periodic values).
    let per: Vec<AB::Expr> = b.preprocessed().current_slice().iter().map(|&p| p.into()).collect();
    let pv: Vec<AB::Expr> = b.public_values().iter().map(|&p| p.into()).collect();
    assert_eq!(per.len(), per::NUM);
    assert_eq!(pv.len(), PUBLIC_BLOCKS * LIMBS);
    let x = |c: usize| -> AB::Expr { l[c].into() };
    let k256 = AB::Expr::from_u64(256);
    let arith = per[per::ARITH].dup();
    let sub = per[per::SUB].dup();
    let sigma = AB::Expr::ONE - sub.double();
    let carry = |k: usize| -> AB::Expr {
        if k >= CARRIES { AB::Expr::ZERO } else { x(col::CL + k) + x(col::CH + k) * AB::Expr::from_u64(256) - AB::Expr::from_u64(CARRY_OFFSET as u64) }
    };
    // Modulus limbs of the row: p, or n where the modulus selector is set.
    let modn = per[per::MODN].dup();
    let m: Vec<AB::Expr> = (0..LIMBS)
        .map(|j| AB::Expr::from_u64(air.p_limbs[j]) + modn.dup() * (AB::Expr::from_u64(air.n_limbs[j]) - AB::Expr::from_u64(air.p_limbs[j])))
        .collect();

    // a*b + sigma*c + tau*m = q*m + r, column by column with signed carries (tau = sub).
    for k in 0..2 * LIMBS - 1 {
        let mut s = AB::Expr::ZERO;
        for i in k.saturating_sub(LIMBS - 1)..=k.min(LIMBS - 1) {
            let j = k - i;
            s += x(col::A + i) * x(col::B + j) - x(col::Q + i) * m[j].dup();
        }
        if k < LIMBS {
            s += sigma.dup() * x(col::C + k) + sub.dup() * m[k].dup() - x(col::R + k);
        }
        let prev = if k == 0 { AB::Expr::ZERO } else { carry(k - 1) };
        b.assert_zero(arith.dup() * (s + prev - carry(k) * k256.dup()));
    }
    // Below-n rows: q = 0, so a*b + c = r exactly.
    for i in 0..LIMBS { b.assert_zero(per[per::QZERO].dup() * x(col::Q + i)); }
    // Scalar bits: limbs 1..31 zero, so with b*b - b = 0 mod p the bit is the integer 0 or 1 and means
    // the same under p (the multiplication) and under n (the tie to the key).
    if air.canonical_bits {
        for i in 1..LIMBS { b.assert_zero(per[per::BIT].dup() * x(col::R + i)); }
    }
    // Constant rows and below-n rows: r is the program's constant (n - 1 on a below-n row).
    for i in 0..LIMBS {
        b.assert_zero((per[per::CONST].dup() + per[per::RCONST].dup()) * (x(col::R + i) - per[per::CONST_LIMB + i].dup()));
    }
    // Check rows: r = 1 or r = 0; check and below-n rows store nothing.
    b.assert_zero(per[per::CHECK1].dup() * (x(col::R) - AB::Expr::ONE));
    for i in 1..LIMBS { b.assert_zero(per[per::CHECK1].dup() * x(col::R + i)); }
    for i in 0..LIMBS { b.assert_zero(per[per::CHECK0].dup() * x(col::R + i)); }
    b.assert_zero((per[per::CHECK1].dup() + per[per::CHECK0].dup() + per[per::RCONST].dup()) * x(col::MULT));
    // Padding rows store nothing.
    b.assert_zero((AB::Expr::ONE - arith.dup() - per[per::CONST].dup() - per[per::INPUT].dup()) * x(col::MULT));
    // Public values: on a row bound to block t, r equals block t (at most one selector per row).
    for i in (0..LIMBS).filter(|_| PUBLIC_BLOCKS > 0) {
        let mut e = AB::Expr::ZERO;
        for t in 0..PUBLIC_BLOCKS {
            e += per[per::PUB + t].dup() * (x(col::R + i) - pv[LIMBS * t + i].dup());
        }
        b.assert_zero(e);
    }
    // Main-column copies of the program values the buses use.
    for (c, p) in [(col::ID_A, per::ID_A), (col::ID_B, per::ID_B), (col::ID_C, per::ID_C), (col::ID_R, per::ID_R), (col::ARITH, per::ARITH),
                   (col::KEC, per::KEC), (col::KIL, per::KIL), (col::KD, per::KD), (col::NH, per::NH), (col::STEP, per::STEP)] {
        b.assert_zero(x(c) - per[p].dup());
    }
    // Keccak input: the KEC row's operands a = x and c = y of k5's point are the 64-byte message x || y
    // (big-endian), sent as 32 little-endian byte pairs; pair t of x is a[31 - 2t] + 256 * a[30 - 2t].
    let pair = |base: usize, t: usize| x(base + 31 - 2 * t) + x(base + 30 - 2 * t) * k256.dup();
    let message: Vec<AB::Expr> = (0..16).map(|t| pair(col::A, t)).chain((0..16).map(|t| pair(col::C, t))).collect();
    LookupBus::new(KECCAK_IN).lookup_key(b, message, Count::bounded(x(col::KEC), 1));
    // S4c. I_L rows read their value from the SHA table: limb j of SHA word w is the byte pair at
    // big-endian positions a = 8w + 7 - 2j (low) and a - 1 (high), that is r[31 - a] + 256 * r[32 - a].
    let il: Vec<AB::Expr> = std::iter::once(x(col::STEP)).chain((0..16).map(|i| {
        let a = 8 * (i / 4) + 7 - 2 * (i % 4);
        x(col::R + 31 - a) + x(col::R + 32 - a) * k256.dup()
    })).collect();
    LookupBus::new(crate::sha::IL).lookup_key(b, il, Count::bounded(x(col::KIL), 1));
    // Data rows provide the CKD message's first 34 bytes to the SHA table, as its window limbs: byte d[0]
    // is the prefix (0, or 2 + the parity bit held in c[0]), d[1..33] the 32 bytes of operand a
    // (big-endian: d[1 + m] = a[31 - m]), d[33] the index's first byte: since S4e the private IDX0,
    // range-checked below so that the limb a[0] * 256 + IDX0 splits into its bytes only one way. The SHA
    // table checks the index's shape.
    let nh = x(col::NH);
    let byte = |pos: usize| -> AB::Expr {
        match pos {
            0 => nh.dup().double() + x(col::C),
            33 => x(col::IDX0),
            _ => x(col::A + 32 - pos),
        }
    };
    let data: Vec<AB::Expr> = std::iter::once(x(col::STEP)).chain(crate::sha::data_limbs().map(|i| {
        let a = 8 * (i / 4) + 7 - 2 * (i % 4);
        byte(a) + byte(a - 1) * k256.dup()
    })).collect();
    LookupBus::new(crate::sha::DATA).table_entry(b, data, x(col::KD));
    // Memory: each arithmetic row reads a, b, c; every row provides its result with its read count.
    let mem = LookupBus::new(MEM);
    for (id, base) in [(col::ID_A, col::A), (col::ID_B, col::B), (col::ID_C, col::C)] {
        let key: Vec<AB::Expr> = std::iter::once(x(id)).chain((0..LIMBS).map(|i| x(base + i))).collect();
        mem.lookup_key(b, key, Count::bounded(x(col::ARITH), 1));
    }
    let out_key: Vec<AB::Expr> = std::iter::once(x(col::ID_R)).chain((0..LIMBS).map(|i| x(col::R + i))).collect();
    mem.table_entry(b, out_key, x(col::MULT));
    // Range: every byte of q and r, and both bytes of every offset carry, in (byte, byte) pairs.
    let range = LookupBus::new(RANGE);
    for base in [col::Q, col::R] {
        for i in 0..LIMBS / 2 {
            range.lookup_key(b, [x(base + 2 * i), x(base + 2 * i + 1)], 1);
        }
    }
    for k in 0..CARRIES {
        range.lookup_key(b, [x(col::CL + k), x(col::CH + k)], 1);
    }
    // S4e: the index's first byte on a data row, as the pair (IDX0, 0).
    range.lookup_key(b, [x(col::IDX0), AB::Expr::ZERO], Count::bounded(x(col::KD), 1));
}
