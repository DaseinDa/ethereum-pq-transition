// Modified by the PQ-Migrate contributors; see MODIFICATIONS.md (2026-11-07 notice).
//! C3nP (L5 layer F2, 2026-11-01): the LogUp permutation trace of an AIR whose lookups read periodic columns.
//!
//! p3-lookup 0.9.0-rc.1 builds the permutation trace row by row through `LookupTraceBuilder` (src/traits.rs l. 7-14),
//! which carries no periodic data and inherits the empty default of p3-air's `periodic_values` (src/builder.rs
//! l. 193-195). `LogUpGadget::generate_permutation` (src/logup.rs l. 499-893) resolves every element and multiplicity of
//! every lookup with that builder (`RowEvalContext::new`, l. 684-691), so a periodic leaf indexes the empty slice and
//! panics (p3-air src/symbolic/expression.rs l. 162). The constraint side already reads periodic columns: the prover's
//! and the verifier's folders give `eval_air_and_lookups` the periodic values at every point they evaluate.
//!
//! [`generate_permutation_periodic`] is `LogUpGadget::generate_permutation`, copied, with one change: the row context
//! of row `i` also holds the AIR's periodic values at that row, `column[i % column.len()]`, the value the periodic
//! column takes at the i-th point of the trace domain (the value the folders interpolate). Everything else is
//! p3-lookup's: the challenge layout (one pair per lookup slot), the denominators and multiplicities in emission
//! order, the flag-zero skip, the exclusive columns, the chunked batch inversion, the fraction columns, the exclusive
//! prefix sum and the terminal. With no periodic column it computes exactly what p3-lookup computes; the F2 record
//! checks that it equals p3-lookup's trace for an AIR whose periodic values are copied into main columns.
//!
//! The prover (`prove_batch_with_next_row_columns`) calls it with `air.periodic_columns()` in place of the gadget's
//! method; the verifier is C3n's, unchanged.
//! loop-internal self-review; not independently reviewed.

use alloc::vec::Vec;

use p3_air::{AirBuilder, RowWindow, SymbolicExpression};
use p3_field::{ExtensionField, Field, dot_product};
use p3_lookup::{Lookup, LookupProtocol, LookupTerminal};
use p3_lookup::logup::LogUpGadget;
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_maybe_rayon::prelude::*;

/// One row's evaluation context: the main and preprocessed windows (this row and the next, wrapping), the public
/// values and this row's periodic values. Only what `SymbolicExpression::resolve` reads (an `AirBuilder` over the base
/// field); it never accepts a constraint.
struct PeriodicRow<'a, F: Field> {
    main: RowWindow<'a, F>,
    preprocessed: RowWindow<'a, F>,
    public_values: &'a [F],
    periodic: &'a [F],
    height: usize,
    row: usize,
}

impl<'a, F: Field> AirBuilder for PeriodicRow<'a, F> {
    type F = F;
    type Expr = F;
    type Var = F;
    type PreprocessedWindow = RowWindow<'a, F>;
    type MainWindow = RowWindow<'a, F>;
    type PublicVar = F;
    type PeriodicVar = F;

    fn main(&self) -> Self::MainWindow {
        self.main
    }

    fn preprocessed(&self) -> &Self::PreprocessedWindow {
        &self.preprocessed
    }

    fn is_first_row(&self) -> F {
        F::from_bool(self.row == 0)
    }

    fn is_last_row(&self) -> F {
        F::from_bool(self.row + 1 == self.height)
    }

    fn is_transition(&self) -> F {
        F::from_bool(self.row + 1 < self.height)
    }

    fn assert_zero<I: Into<F>>(&mut self, _x: I) {
        panic!("the permutation-trace row context evaluates lookup expressions only");
    }

    fn public_values(&self) -> &[F] {
        self.public_values
    }

    fn periodic_values(&self) -> &[F] {
        self.periodic
    }
}

/// p3-lookup's tuple combination (src/logup.rs l. 51-67): `sum_i e_i * beta^{k-1-i}`.
fn combine_tuple<F: Field, EF: ExtensionField<F>>(
    elts: &[SymbolicExpression<F>],
    beta_powers: &[EF],
    row_ctx: &PeriodicRow<'_, F>,
) -> EF {
    match elts.split_last() {
        None => EF::ZERO,
        Some((last, [])) => last.resolve(row_ctx).into(),
        Some((last, leading)) => {
            let high_powers = beta_powers[1..elts.len()].iter().rev().copied();
            let leading_resolved = leading.iter().map(|e| e.resolve(row_ctx));
            let lifted_last: EF = last.resolve(row_ctx).into();
            lifted_last + dot_product::<EF, _, _>(high_powers, leading_resolved)
        }
    }
}

/// `LogUpGadget::generate_permutation` with the AIR's periodic columns (`periodic[k]` of any length dividing the
/// height; the value at row `i` is `periodic[k][i % len]`).
///
/// # Panics
///
/// As p3-lookup's: a lookup slot index that is not its position; a non-boolean exclusive flag or two at once; and here
/// also a periodic column whose length is zero or does not divide the height.
#[allow(clippy::too_many_lines)]
pub fn generate_permutation_periodic<F: Field, EF: ExtensionField<F>>(
    gadget: &LogUpGadget,
    main: &RowMajorMatrix<F>,
    preprocessed: &Option<RowMajorMatrix<F>>,
    periodic: &[Vec<F>],
    public_values: &[F],
    lookups: &[Lookup<F>],
    challenges: &[EF],
) -> (RowMajorMatrix<EF>, Option<LookupTerminal<EF>>) {
    if lookups.is_empty() {
        return (RowMajorMatrix::new(Vec::new(), 0), None);
    }

    let height = main.height();
    for col in periodic {
        assert!(
            !col.is_empty() && height % col.len() == 0,
            "a periodic column's length must divide the trace height"
        );
    }
    let num_lookups = lookups.len();
    let width = num_lookups + 1;

    debug_assert_eq!(
        challenges.len(),
        lookups.len() * gadget.num_challenges(),
        "perm challenge count must be per-lookup"
    );
    for (i, lookup) in lookups.iter().enumerate() {
        assert_eq!(
            lookup.column, i,
            "lookup slot index must match slice position: lookups[{i}].column = {} (expected {i})",
            lookup.column,
        );
    }

    let num_denoms = |l: &Lookup<F>| if l.flags.is_some() { 1 } else { l.elements.len() };
    let denoms_per_row: usize = lookups.iter().map(num_denoms).sum();
    let mut lookup_denom_offsets = Vec::with_capacity(lookups.len() + 1);
    lookup_denom_offsets.push(0);
    for l in lookups {
        lookup_denom_offsets.push(lookup_denom_offsets.last().copied().unwrap() + num_denoms(l));
    }

    let lookup_challenges: Vec<(EF, EF)> = lookups
        .iter()
        .map(|lookup| {
            let base = gadget.num_challenges() * lookup.column;
            (challenges[base], challenges[base + 1])
        })
        .collect();

    let max_tuple_width = lookups
        .iter()
        .flat_map(|lookup| lookup.elements.iter())
        .map(Vec::len)
        .max()
        .unwrap_or(0);
    let beta_powers: Vec<Vec<EF>> = lookup_challenges
        .iter()
        .map(|&(_, beta)| beta.powers().collect_n(max_tuple_width))
        .collect();

    const CHUNK_SIZE: usize = 1024;
    let mut aux_trace = EF::zero_vec(height * width);
    let mut row_totals = EF::zero_vec(height);
    let num_periodic = periodic.len();

    aux_trace
        .par_chunks_mut(CHUNK_SIZE * width)
        .zip(row_totals.par_chunks_mut(CHUNK_SIZE))
        .with_min_task_bytes(5 * CHUNK_SIZE * denoms_per_row * size_of::<EF>())
        .enumerate()
        .for_each(|(chunk_idx, (chunk_aux, chunk_row_totals))| {
            let start_row = chunk_idx * CHUNK_SIZE;
            let num_rows = chunk_aux.len() / width;
            let mut local_denoms = EF::zero_vec(num_rows * denoms_per_row);
            let mut local_mults = F::zero_vec(num_rows * denoms_per_row);
            // C3nP: one buffer of this row's periodic values, refilled per row.
            let mut periodic_row = F::zero_vec(num_periodic);
            let empty: [F; 0] = [];

            for local_i in 0..num_rows {
                let i = start_row + local_i;
                let local_main_row = main.row_slice(i).unwrap();
                let next_main_row = main.row_slice((i + 1) % height).unwrap();
                let preprocessed_rows = preprocessed.as_ref().map(|prep| {
                    (prep.row_slice(i).unwrap(), prep.row_slice((i + 1) % height).unwrap())
                });
                for (k, col) in periodic.iter().enumerate() {
                    periodic_row[k] = col[i % col.len()];
                }
                let row_ctx = PeriodicRow {
                    main: RowWindow::from_two_rows(&local_main_row, &next_main_row),
                    preprocessed: match preprocessed_rows.as_ref() {
                        Some((l, n)) => RowWindow::from_two_rows(l, n),
                        None => RowWindow::from_two_rows(&empty, &empty),
                    },
                    public_values,
                    periodic: &periodic_row,
                    height,
                    row: i,
                };

                let mut offset = local_i * denoms_per_row;
                for ((lookup, &(alpha, _)), powers) in lookups.iter().zip(lookup_challenges.iter()).zip(beta_powers.iter()) {
                    match &lookup.flags {
                        None => {
                            for (j, elts) in lookup.elements.iter().enumerate() {
                                let mult = lookup.multiplicities[j].resolve(&row_ctx);
                                local_mults[offset] = mult;
                                local_denoms[offset] = if mult.is_zero() {
                                    EF::ONE
                                } else {
                                    alpha - combine_tuple::<F, EF>(elts, powers, &row_ctx)
                                };
                                offset += 1;
                            }
                        }
                        Some(flags) => {
                            debug_assert_eq!(flags.len(), lookup.elements.len(), "exclusive column must carry one flag per tuple");
                            let mut numerator = F::ZERO;
                            let mut flag_sum = F::ZERO;
                            let mut denom = EF::ZERO;
                            for (k, elts) in lookup.elements.iter().enumerate() {
                                let flag = flags[k].resolve(&row_ctx);
                                assert!(flag.is_zero() || flag == F::ONE, "exclusive flag must be boolean");
                                flag_sum += flag;
                                if flag.is_zero() {
                                    continue;
                                }
                                let mult = lookup.multiplicities[k].resolve(&row_ctx);
                                numerator += flag * mult;
                                let term = alpha - combine_tuple::<F, EF>(elts, powers, &row_ctx);
                                denom += term * flag;
                            }
                            assert!(flag_sum.is_zero() || flag_sum == F::ONE, "exclusive flags must sum to at most one per row");
                            denom += F::ONE - flag_sum;
                            local_denoms[offset] = denom;
                            local_mults[offset] = numerator;
                            offset += 1;
                        }
                    }
                }
            }

            let local_inverses = p3_field::batch_multiplicative_inverse(&local_denoms);
            drop(local_denoms);

            for (local_i, row_total_slot) in chunk_row_totals.iter_mut().enumerate() {
                let inv_base = local_i * denoms_per_row;
                let row_offset = local_i * width;
                let mut row_total = EF::ZERO;
                for lookup_idx in 0..lookups.len() {
                    let start = lookup_denom_offsets[lookup_idx];
                    let end = lookup_denom_offsets[lookup_idx + 1];
                    let inv_slice = &local_inverses[inv_base + start..inv_base + end];
                    let mult_slice = &local_mults[inv_base + start..inv_base + end];
                    let frac = EF::batched_linear_combination(inv_slice, mult_slice);
                    chunk_aux[row_offset + lookup_idx + 1] = frac;
                    row_total += frac;
                }
                *row_total_slot = row_total;
            }
        });

    // The accumulator: an exclusive prefix sum of the row totals (p3-lookup's three-phase parallel scan).
    let num_threads = current_num_threads();
    let chunk_size = height.div_ceil(num_threads).max(min_task_len(height, 2 * size_of::<EF>()));
    row_totals.par_chunks_mut(chunk_size).for_each(|chunk| {
        for i in 1..chunk.len() {
            chunk[i] += chunk[i - 1];
        }
    });
    let mut offsets = EF::zero_vec(height.div_ceil(chunk_size));
    for i in 1..offsets.len() {
        offsets[i] = offsets[i - 1] + row_totals[i * chunk_size - 1];
    }
    row_totals.par_chunks_mut(chunk_size).enumerate().for_each(|(chunk_idx, chunk)| {
        let offset = offsets[chunk_idx];
        if !offset.is_zero() {
            for val in chunk.iter_mut() {
                *val += offset;
            }
        }
    });
    let terminal = LookupTerminal(row_totals[height - 1]);
    aux_trace.par_chunks_mut(width).skip(1).enumerate().for_each(|(i, row)| {
        row[0] = row_totals[i];
    });

    (RowMajorMatrix::new(aux_trace, width), Some(terminal))
}
