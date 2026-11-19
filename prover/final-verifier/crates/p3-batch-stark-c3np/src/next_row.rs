// Modified by the PQ-Migrate contributors; see MODIFICATIONS.md (2026-11-07 notice).
//! C3n (L5 leaf L0' v2, 2026-10-31): next-row subset openings.
//!
//! The stock and the C3 batch layers open a table's whole main trace at `zeta * g` as soon as its AIR
//! declares any next-row column (`BaseAir::main_next_row_columns`, every column by default), its
//! preprocessed trace likewise, and its permutation trace always. C3n opens at `zeta * g` only the
//! columns that the AIR's symbolic constraints, lookups included, read at the next row.
//!
//! The pinned PCS opens every column of a committed matrix at every point of that matrix (p3-commit
//! `PointOpening` holds the claimed evaluations of every column at one point; p3-fri `open_inputs`
//! rejects a point whose claims are not as wide as the matrix). So a trace whose next-row set is a
//! proper subset of its columns is committed as two matrices of the same height: the columns of the set,
//! opened at `zeta` and `zeta * g`, then the remaining columns, opened at `zeta` only. A trace whose set
//! is empty is one matrix opened at `zeta` only; a trace whose set is every column is one matrix opened
//! at both points, as before. A permutation trace is committed in base columns, so its set is the base
//! coordinates of the extension columns read at the next row.
//!
//! The prover and the verifier each derive the sets from the AIR and its lookups ([`derive`],
//! [`next_row_columns_for_batch`]), never from the proof. The verifier requires the proof's next-row
//! openings to have exactly the derived lengths, claims every committed matrix at exactly its derived
//! points, and gives the constraint folder the full next row with every omitted entry set to zero: no
//! constraint reads an omitted entry, so its value cannot change the folded constraints.

use alloc::collections::BTreeSet;
use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;
use core::ops::Deref;

use p3_air::Air;
use p3_air::symbolic::{
    AirLayout, BaseEntry, BaseLeaf, ExtEntry, ExtLeaf, SymbolicExpr, SymbolicExpression,
    SymbolicExpressionExt,
};
use p3_field::{Algebra, ExtensionField, Field, PackedValue};
use p3_lookup::logup::LogUpGadget;
use p3_lookup::{InteractionSymbolicBuilder, Lookup, LookupProtocol};
use p3_matrix::Matrix;

use crate::common::CommonData;
use crate::config::{StarkGenericConfig as SGC, Val};
use crate::symbolic::get_symbolic_constraints;

/// The columns one AIR reads at the next row, each list in increasing order, with the widths they index.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct NextRowColumns {
    /// Main-trace width.
    pub main_width: usize,
    /// Main columns read at the next row.
    pub main: Vec<usize>,
    /// Preprocessed width (zero without a preprocessed trace).
    pub preprocessed_width: usize,
    /// Preprocessed columns read at the next row.
    pub preprocessed: Vec<usize>,
    /// Permutation-trace width in extension columns (zero without lookups).
    pub permutation_width: usize,
    /// Permutation (extension) columns read at the next row.
    pub permutation: Vec<usize>,
}

/// The next-row columns of one AIR: the column of every `Main { offset: 1 }`, `Preprocessed { offset: 1 }`
/// and `Permutation { offset: 1 }` variable in its symbolic constraints, its lookups' constraints included,
/// from the same symbolic evaluation that the prover and the verifier run for the quotient degree.
///
/// A variable that the symbolic builder folded away (a product with the constant zero, for instance) is
/// absent; such a variable cannot change the constraint's value either, since every folding the builder
/// does is an identity of polynomials.
///
/// # Panics
///
/// If a constraint reads a row at an offset other than 0 or 1 (no p3 window offers one).
pub fn derive<F, EF, A, LG>(
    air: &A,
    layout: AirLayout,
    lookups: &[Lookup<F>],
    lookup_gadget: &LG,
) -> NextRowColumns
where
    F: Field,
    EF: ExtensionField<F>,
    A: Air<InteractionSymbolicBuilder<F, EF>>,
    SymbolicExpressionExt<F, EF>: Algebra<EF>,
    LG: LookupProtocol,
{
    let (base, ext) = get_symbolic_constraints::<F, EF, A, LG>(air, layout, lookups, lookup_gadget);
    let mut reads = Reads::default();
    // Every shared subexpression is visited once: nodes are keyed by the address of their `Arc`.
    let mut seen = BTreeSet::new();
    for constraint in &base {
        reads.base(constraint, &mut seen);
    }
    for constraint in &ext {
        reads.ext(constraint, &mut seen);
    }
    NextRowColumns {
        main_width: layout.main_width,
        main: reads.main.into_iter().collect(),
        preprocessed_width: layout.preprocessed_width,
        preprocessed: reads.preprocessed.into_iter().collect(),
        permutation_width: if lookups.is_empty() {
            0
        } else {
            lookups.len() + 1
        },
        permutation: reads.permutation.into_iter().collect(),
    }
}

/// The derived next-row columns of every instance of a batch: each AIR with the preprocessed width and the
/// lookups of the key (`CommonData`), exactly as the prover and the verifier lay out their constraints.
///
/// # Panics
///
/// If `common` describes another number of instances.
pub fn next_row_columns_for_batch<'a, SC, A>(
    airs: impl IntoIterator<Item = &'a A>,
    common: &CommonData<SC>,
) -> Vec<NextRowColumns>
where
    SC: SGC,
    A: Air<InteractionSymbolicBuilder<Val<SC>, SC::Challenge>> + 'a,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>: Algebra<SC::Challenge>,
{
    let gadget = LogUpGadget::new();
    let out: Vec<NextRowColumns> = airs
        .into_iter()
        .enumerate()
        .map(|(i, air)| {
            let preprocessed_width = common
                .preprocessed
                .as_ref()
                .and_then(|g| g.instances[i].as_ref().map(|m| m.width))
                .unwrap_or(0);
            let layout = AirLayout {
                preprocessed_width,
                main_width: air.width(),
                num_public_values: air.num_public_values(),
                num_periodic_columns: air.num_periodic_columns(),
                ..Default::default()
            };
            derive::<Val<SC>, SC::Challenge, A, _>(air, layout, &common.lookups[i], &gadget)
        })
        .collect();
    assert_eq!(out.len(), common.lookups.len(), "one next-row column set per instance");
    out
}

#[derive(Default)]
struct Reads {
    main: BTreeSet<usize>,
    preprocessed: BTreeSet<usize>,
    permutation: BTreeSet<usize>,
}

impl Reads {
    fn base<F>(&mut self, root: &SymbolicExpression<F>, seen: &mut BTreeSet<usize>) {
        let mut stack: Vec<&SymbolicExpression<F>> = vec![root];
        while let Some(e) = stack.pop() {
            match e {
                SymbolicExpr::Leaf(BaseLeaf::Variable(v)) => match v.entry {
                    BaseEntry::Main { offset } => {
                        assert!(offset <= 1, "main row offset {offset}");
                        if offset == 1 {
                            self.main.insert(v.index);
                        }
                    }
                    BaseEntry::Preprocessed { offset } => {
                        assert!(offset <= 1, "preprocessed row offset {offset}");
                        if offset == 1 {
                            self.preprocessed.insert(v.index);
                        }
                    }
                    BaseEntry::Periodic | BaseEntry::Public => {}
                },
                SymbolicExpr::Leaf(_) => {}
                SymbolicExpr::Add { x, y, .. }
                | SymbolicExpr::Sub { x, y, .. }
                | SymbolicExpr::Mul { x, y, .. } => {
                    for child in [x, y] {
                        if seen.insert(Arc::as_ptr(child) as usize) {
                            stack.push(child);
                        }
                    }
                }
                SymbolicExpr::Neg { x, .. } => {
                    if seen.insert(Arc::as_ptr(x) as usize) {
                        stack.push(x);
                    }
                }
            }
        }
    }

    fn ext<F, EF>(&mut self, root: &SymbolicExpressionExt<F, EF>, seen: &mut BTreeSet<usize>) {
        let mut stack: Vec<&SymbolicExpressionExt<F, EF>> = vec![root];
        while let Some(e) = stack.pop() {
            match e {
                SymbolicExpr::Leaf(ExtLeaf::Base(b)) => self.base(b, seen),
                SymbolicExpr::Leaf(ExtLeaf::ExtVariable(v)) => {
                    if let ExtEntry::Permutation { offset } = v.entry {
                        assert!(offset <= 1, "permutation row offset {offset}");
                        if offset == 1 {
                            self.permutation.insert(v.index);
                        }
                    }
                }
                SymbolicExpr::Leaf(ExtLeaf::ExtConstant(_)) => {}
                SymbolicExpr::Add { x, y, .. }
                | SymbolicExpr::Sub { x, y, .. }
                | SymbolicExpr::Mul { x, y, .. } => {
                    for child in [x, y] {
                        if seen.insert(Arc::as_ptr(child) as usize) {
                            stack.push(child);
                        }
                    }
                }
                SymbolicExpr::Neg { x, .. } => {
                    if seen.insert(Arc::as_ptr(x) as usize) {
                        stack.push(x);
                    }
                }
            }
        }
    }
}

/// How one committed trace (a main trace, a preprocessed trace, or a permutation trace in base columns) is
/// committed and opened under C3n.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TraceSplit {
    /// Base-column width of the trace.
    pub width: usize,
    /// Base columns opened at `zeta * g`, increasing.
    pub next: Vec<usize>,
}

impl TraceSplit {
    /// Strictly increasing columns, each below the width.
    #[must_use]
    pub fn is_well_formed(&self) -> bool {
        self.next.windows(2).all(|w| w[0] < w[1]) && self.next.last().is_none_or(|&c| c < self.width)
    }

    /// Whether the trace is committed as two matrices (a proper, non-empty next-row set).
    #[must_use]
    pub fn is_split(&self) -> bool {
        !self.next.is_empty() && self.next.len() < self.width
    }

    /// The committed matrices of this trace in commitment order: (trace columns, opened at `zeta * g`).
    #[must_use]
    pub fn matrices(&self) -> Vec<(Vec<usize>, bool)> {
        let all: Vec<usize> = (0..self.width).collect();
        if self.next.is_empty() {
            vec![(all, false)]
        } else if self.next.len() == self.width {
            vec![(all, true)]
        } else {
            vec![(self.next.clone(), true), (self.rest(), false)]
        }
    }

    /// The columns not opened at `zeta * g`, increasing.
    #[must_use]
    pub fn rest(&self) -> Vec<usize> {
        let set: BTreeSet<usize> = self.next.iter().copied().collect();
        (0..self.width).filter(|c| !set.contains(c)).collect()
    }

    /// The number of values the proof carries at `zeta * g`; `None` when no column is opened there.
    #[must_use]
    pub fn next_len(&self) -> Option<usize> {
        (!self.next.is_empty()).then_some(self.next.len())
    }

    /// For each trace column: (the index of its matrix among this trace's matrices, its column there).
    #[must_use]
    pub fn column_map(&self) -> Vec<(usize, usize)> {
        let mut map = vec![(0, 0); self.width];
        for (m, (cols, _)) in self.matrices().iter().enumerate() {
            for (k, &c) in cols.iter().enumerate() {
                map[c] = (m, k);
            }
        }
        map
    }

    /// Values of this trace's matrices at one point (commitment order) back in trace-column order.
    #[must_use]
    pub fn merge<T: Clone>(&self, parts: &[&[T]]) -> Vec<T> {
        self.column_map()
            .into_iter()
            .map(|(m, k)| parts[m][k].clone())
            .collect()
    }

    /// A trace-ordered row cut into this trace's matrices (commitment order).
    #[must_use]
    pub fn split<T: Clone>(&self, row: &[T]) -> Vec<Vec<T>> {
        self.matrices()
            .into_iter()
            .map(|(cols, _)| cols.iter().map(|&c| row[c].clone()).collect())
            .collect()
    }

    /// The next row at the trace's full width: the opened values at their columns, `fill(column)` elsewhere.
    #[must_use]
    pub fn expand_next<T: Clone>(&self, values: &[T], fill: impl Fn(usize) -> T) -> Vec<T> {
        let mut out: Vec<T> = (0..self.width).map(&fill).collect();
        for (&c, v) in self.next.iter().zip(values) {
            out[c] = v.clone();
        }
        out
    }
}

impl NextRowColumns {
    /// The main trace's split.
    #[must_use]
    pub fn main_split(&self) -> TraceSplit {
        TraceSplit {
            width: self.main_width,
            next: self.main.clone(),
        }
    }

    /// The preprocessed trace's split (the key commits one matrix per instance: only none or all is supported).
    #[must_use]
    pub fn preprocessed_split(&self) -> TraceSplit {
        TraceSplit {
            width: self.preprocessed_width,
            next: self.preprocessed.clone(),
        }
    }

    /// The permutation trace's split in base columns: every base coordinate of each extension column read
    /// at the next row.
    #[must_use]
    pub fn permutation_split(&self, dimension: usize) -> TraceSplit {
        TraceSplit {
            width: self.permutation_width * dimension,
            next: self
                .permutation
                .iter()
                .flat_map(|&j| j * dimension..(j + 1) * dimension)
                .collect(),
        }
    }

    /// Strictly increasing sets inside their widths.
    #[must_use]
    pub fn is_well_formed(&self) -> bool {
        self.main_split().is_well_formed()
            && self.preprocessed_split().is_well_formed()
            && self.permutation_split(1).is_well_formed()
    }
}

/// What the verifier's constraint folder reads at an omitted next-row entry.
///
/// `Zero` is the verifier's behaviour. `Pseudorandom` exists for the controls, which show on the real
/// verification path that no constraint reads an omitted entry: the honest proof must verify whatever the
/// omitted entries hold, and a set that misses a column the AIR reads makes it fail.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OmittedFill {
    /// Zero, as the library's verifier fills a next row that the AIR never reads.
    Zero,
    /// A pseudorandom value per (seed, instance, trace, column, coordinate).
    Pseudorandom(u64),
}

/// Trace tags of [`OmittedFill::coefficient`].
pub const TRACE_MAIN: u64 = 1;
/// Trace tag of the preprocessed trace.
pub const TRACE_PREPROCESSED: u64 = 2;
/// Trace tag of the permutation trace.
pub const TRACE_PERMUTATION: u64 = 3;

impl OmittedFill {
    /// The base-field coefficient `coordinate` of the fill at (instance, trace, column), as an integer that the
    /// caller reduces into the field.
    #[must_use]
    pub fn coefficient(&self, instance: usize, trace: u64, column: usize, coordinate: usize) -> u64 {
        match self {
            Self::Zero => 0,
            Self::Pseudorandom(seed) => {
                let mut z = seed
                    ^ ((instance as u64) << 52)
                    ^ (trace << 48)
                    ^ ((column as u64) << 8)
                    ^ coordinate as u64;
                // splitmix64
                z = z.wrapping_add(0x9e37_79b9_7f4a_7c15);
                z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
                z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
                z ^ (z >> 31)
            }
        }
    }
}

/// One iterator or slice type for two sources (the prover's merged trace view).
enum Either<A, B> {
    A(A),
    B(B),
}

impl<T, A: Iterator<Item = T>, B: Iterator<Item = T>> Iterator for Either<A, B> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        match self {
            Self::A(a) => a.next(),
            Self::B(b) => b.next(),
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            Self::A(a) => a.size_hint(),
            Self::B(b) => b.size_hint(),
        }
    }
}

impl<T, A: Deref<Target = [T]>, B: Deref<Target = [T]>> Deref for Either<A, B> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        match self {
            Self::A(a) => a,
            Self::B(b) => b,
        }
    }
}

/// One trace as the prover's constraint evaluation reads it on the quotient domain: one committed matrix,
/// or the two matrices of a split trace, every column at its trace position.
pub enum MergedTrace<M> {
    /// The trace is one committed matrix.
    One(M),
    /// The two matrices of a split trace and the split's column map.
    Two {
        /// The matrix of the next-row columns.
        first: M,
        /// The matrix of the other columns.
        second: M,
        /// For each trace column: (0 for `first`, 1 for `second`; its column there).
        map: Vec<(usize, usize)>,
    },
}

impl<M> MergedTrace<M> {
    /// The view of a trace from its committed matrices, in commitment order.
    ///
    /// # Panics
    ///
    /// If the number of matrices is not the split's.
    pub fn new(split: &TraceSplit, mut parts: Vec<M>) -> Self {
        if split.is_split() {
            assert_eq!(parts.len(), 2, "a split trace is two matrices");
            let second = parts.pop().expect("two matrices");
            let first = parts.pop().expect("two matrices");
            Self::Two {
                first,
                second,
                map: split.column_map(),
            }
        } else {
            assert_eq!(parts.len(), 1, "an unsplit trace is one matrix");
            Self::One(parts.pop().expect("one matrix"))
        }
    }

    /// Columns `start..end` of row `r` of a split trace, in trace order.
    ///
    /// # Safety
    ///
    /// `r < height` and `start <= end <= width`.
    unsafe fn merged_row<T: Send + Sync + Clone>(&self, r: usize, start: usize, end: usize) -> Vec<T>
    where
        M: Matrix<T>,
    {
        let Self::Two { first, second, map } = self else {
            unreachable!("merged_row is called on a split trace only")
        };
        let (a, b) = unsafe { (first.row_slice_unchecked(r), second.row_slice_unchecked(r)) };
        map[start..end]
            .iter()
            .map(|&(part, k)| if part == 0 { a[k].clone() } else { b[k].clone() })
            .collect()
    }
}

impl<T: Send + Sync + Clone, M: Matrix<T>> Matrix<T> for MergedTrace<M> {
    fn width(&self) -> usize {
        match self {
            Self::One(m) => m.width(),
            Self::Two { map, .. } => map.len(),
        }
    }

    fn height(&self) -> usize {
        match self {
            Self::One(m) => m.height(),
            Self::Two { first, .. } => first.height(),
        }
    }

    unsafe fn get_unchecked(&self, r: usize, c: usize) -> T {
        unsafe {
            match self {
                Self::One(m) => m.get_unchecked(r, c),
                Self::Two { first, second, map } => {
                    let (part, k) = map[c];
                    if part == 0 {
                        first.get_unchecked(r, k)
                    } else {
                        second.get_unchecked(r, k)
                    }
                }
            }
        }
    }

    unsafe fn row_subseq_unchecked(
        &self,
        r: usize,
        start: usize,
        end: usize,
    ) -> impl IntoIterator<Item = T, IntoIter = impl Iterator<Item = T> + Send + Sync> {
        unsafe {
            match self {
                Self::One(m) => Either::A(m.row_subseq_unchecked(r, start, end).into_iter()),
                Self::Two { .. } => Either::B(self.merged_row(r, start, end).into_iter()),
            }
        }
    }

    unsafe fn row_subslice_unchecked(
        &self,
        r: usize,
        start: usize,
        end: usize,
    ) -> impl Deref<Target = [T]> {
        unsafe {
            match self {
                Self::One(m) => Either::A(m.row_subslice_unchecked(r, start, end)),
                Self::Two { .. } => Either::B(self.merged_row(r, start, end)),
            }
        }
    }

    fn vertically_packed_row<P>(&self, r: usize) -> impl Iterator<Item = P>
    where
        T: Copy,
        P: PackedValue<Value = T>,
    {
        match self {
            Self::One(m) => Either::A(m.vertically_packed_row::<P>(r)),
            Self::Two { first, second, map } => {
                let a: Vec<P> = first.vertically_packed_row::<P>(r).collect();
                let b: Vec<P> = second.vertically_packed_row::<P>(r).collect();
                let row: Vec<P> = map
                    .iter()
                    .map(|&(part, k)| if part == 0 { a[k] } else { b[k] })
                    .collect();
                Either::B(row.into_iter())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn split_layouts() {
        let none = TraceSplit { width: 4, next: vec![] };
        assert_eq!(none.matrices(), vec![(vec![0, 1, 2, 3], false)]);
        assert_eq!(none.next_len(), None);
        let all = TraceSplit { width: 3, next: vec![0, 1, 2] };
        assert_eq!(all.matrices(), vec![(vec![0, 1, 2], true)]);
        let some = TraceSplit { width: 5, next: vec![1, 3] };
        assert!(some.is_split());
        assert_eq!(some.matrices(), vec![(vec![1, 3], true), (vec![0, 2, 4], false)]);
        let row = [10, 11, 12, 13, 14];
        let parts = some.split(&row);
        assert_eq!(parts, vec![vec![11, 13], vec![10, 12, 14]]);
        let refs: Vec<&[i32]> = parts.iter().map(Vec::as_slice).collect();
        assert_eq!(some.merge(&refs), row.to_vec());
        assert_eq!(some.expand_next(&[7, 8], |_| 0), vec![0, 7, 0, 8, 0]);
        assert!(!TraceSplit { width: 2, next: vec![1, 1] }.is_well_formed());
        assert!(!TraceSplit { width: 2, next: vec![2] }.is_well_formed());
    }
}
