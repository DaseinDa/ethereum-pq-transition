//! The check of B's full constraint system on a trace, LogUp included (L5 layer B1, 2026-10-31; B2, 2026-11-01: the
//! preprocessed control is passed to the gadget and to every row's evaluation, as the prover passes it).
//!
//! `kernel::check` evaluates B's base constraints on every row and counts the memory bus's tuples exactly. This module
//! adds what the proof system itself would check of the bus: with lookup challenges drawn at random (the prover draws
//! them from its transcript after the main commitment; any fixed pair serves a satisfiability check), p3-lookup's own
//! `LogUpGadget::generate_permutation` builds the permutation trace (the accumulator and one fraction column per packed
//! lookup) from the trace, exactly as the prover would; then every constraint of B, the base ones and the gadget's
//! (each fraction pinned to its rational value on every row, the accumulator's first row, transitions and terminal
//! binding), is evaluated on every row by `eval_air_and_lookups` (the same entry point the prover's and the verifier's
//! folders use) over EF8 values, and the single instance's terminal must be zero (the batch's global terminal check
//! for B's one table). The challenges are laid out as p3_batch_stark_c3's transcript lays them out for one global bus
//! (`[prefix(bus 0), beta]` per lookup, prefix = alpha + gamma, gamma = beta^W).
//! Research prototype; loop-internal self-review; not independently reviewed.
use p3_air::RowWindow;
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing};
use p3_koala_bear::KoalaBear as F;
use p3_lookup::{Challenges, LogUpGadget, Lookup, LookupProtocol};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_maybe_rayon::prelude::*;
use rand::{RngExt, SeedableRng, rngs::StdRng};
use serde_json::{Value, json};

use crate::EF;
use crate::kernel::{BUS, KernelAir};

/// A builder over one row (and the next) lifted to EF8: every constraint's value is recorded; nonzero ones counted.
struct RowBuilder<'a> {
    main: RowWindow<'a, EF>,
    pre: RowWindow<'a, EF>,
    perm: RowWindow<'a, EF>,
    per: &'a [EF],
    public: &'a [F],
    challenges: &'a [EF],
    perm_values: &'a [EF],
    sels: [EF; 3],
    idx: usize,
    base_constraints: usize,
    fails: Vec<(usize, bool)>,
}

impl<'a> p3_air::AirBuilder for RowBuilder<'a> {
    type F = F;
    type Expr = EF;
    type Var = EF;
    type PreprocessedWindow = RowWindow<'a, EF>;
    type MainWindow = RowWindow<'a, EF>;
    type PublicVar = F;
    type PeriodicVar = EF;
    fn main(&self) -> Self::MainWindow {
        self.main
    }
    fn preprocessed(&self) -> &Self::PreprocessedWindow {
        &self.pre
    }
    fn is_first_row(&self) -> EF {
        self.sels[0]
    }
    fn is_last_row(&self) -> EF {
        self.sels[1]
    }
    fn is_transition(&self) -> EF {
        self.sels[2]
    }
    fn assert_zero<I: Into<EF>>(&mut self, x: I) {
        if x.into() != EF::ZERO {
            self.fails.push((self.idx, false));
        }
        self.idx += 1;
        self.base_constraints += 1;
    }
    fn public_values(&self) -> &[F] {
        self.public
    }
    fn periodic_values(&self) -> &[EF] {
        self.per
    }
}
impl<'a> p3_air::ExtensionBuilder for RowBuilder<'a> {
    type EF = EF;
    type ExprEF = EF;
    type VarEF = EF;
    fn assert_zero_ext<I: Into<EF>>(&mut self, x: I) {
        if x.into() != EF::ZERO {
            self.fails.push((self.idx, true));
        }
        self.idx += 1;
    }
}
impl<'a> p3_air::PermutationAirBuilder for RowBuilder<'a> {
    type MP = RowWindow<'a, EF>;
    type RandomVar = EF;
    type PermutationVar = EF;
    fn permutation(&self) -> Self::MP {
        self.perm
    }
    fn permutation_randomness(&self) -> &[EF] {
        self.challenges
    }
    fn permutation_values(&self) -> &[EF] {
        self.perm_values
    }
}
impl<'a> p3_lookup::InteractionBuilder for RowBuilder<'a> {
    fn push_interaction<E: Into<EF>>(&mut self, _bus: &str, fields: impl IntoIterator<Item = E>, _count: impl Into<p3_lookup::Count<EF>>) {
        fields.into_iter().for_each(drop);
    }
    fn push_local_interaction(&mut self, tuples: impl IntoIterator<Item = (Vec<EF>, p3_lookup::Count<EF>)>) {
        tuples.into_iter().for_each(drop);
    }
}

/// Every constraint of B (base and LogUp) on every row of `trace`, with p3-lookup's permutation trace for random
/// challenges, and the terminal. Returns a record: constraints per row, failing evaluations (base, extension), the
/// first failing rows, the terminal and whether it is zero.
pub fn check(air: &KernelAir, trace: &RowMajorMatrix<F>, pv: &[F], lookups: &[Lookup<F>], seed: u64) -> Value {
    let gadget = LogUpGadget::new();
    let mut rng = StdRng::seed_from_u64(seed);
    let rand_ef = |rng: &mut StdRng| EF::from_basis_coefficients_fn(|_| rng.random::<F>());
    let (alpha, beta) = (rand_ef(&mut rng), rand_ef(&mut rng));
    for l in lookups {
        assert!(matches!(&l.kind, p3_lookup::Kind::Global(name) if name == BUS), "every packed lookup of B is on its one global bus");
    }
    let width = lookups.iter().map(|l| l.elements.first().map(Vec::len).unwrap_or(1)).max().unwrap_or(1);
    let ch = Challenges::new(alpha, beta, width, 1);
    let challenges: Vec<EF> = lookups.iter().flat_map(|_| [ch.bus_prefix[0], beta]).collect();
    let t = std::time::Instant::now();
    let pre_matrix = air.pre_matrix();
    let (perm, terminal) = gadget.generate_permutation::<F, EF>(trace, &Some(pre_matrix), pv, lookups, &challenges);
    let generate_ms = t.elapsed().as_secs_f64() * 1e3;
    let terminal = terminal.expect("B declares lookups").0;
    let n = trace.height();
    let w = trace.width();
    let pw = perm.width();
    let np = air.pre.len();
    let t = std::time::Instant::now();
    let tv = [terminal];
    // Rows in parallel chunks; each row: its window lifted to EF8, every constraint evaluated.
    let results: Vec<(usize, usize, usize, usize, Vec<(usize, usize, bool)>)> = (0..n)
        .into_par_iter()
        .chunks(1024)
        .map(|rows| {
            let (mut nb, mut ne, mut total, mut base_n) = (0usize, 0usize, 0usize, 0usize);
            let mut first = vec![];
            let mut lo = vec![EF::ZERO; w];
            let mut nx = vec![EF::ZERO; w];
            let mut pre = vec![EF::ZERO; np];
            for i in rows {
                let j = (i + 1) % n;
                for c in 0..w {
                    lo[c] = EF::from(trace.values[i * w + c]);
                    nx[c] = EF::from(trace.values[j * w + c]);
                }
                for (k, col) in air.pre.iter().enumerate() {
                    pre[k] = EF::from(col[i]);
                }
                let pl = &perm.values[i * pw..(i + 1) * pw];
                let pn = &perm.values[j * pw..(j + 1) * pw];
                let mut b = RowBuilder {
                    main: RowWindow::from_two_rows(&lo, &nx),
                    pre: RowWindow::from_two_rows(&pre, &pre),
                    perm: RowWindow::from_two_rows(pl, pn),
                    per: &[],
                    public: pv,
                    challenges: &challenges,
                    perm_values: &tv,
                    sels: [
                        if i == 0 { EF::ONE } else { EF::ZERO },
                        if i == n - 1 { EF::ONE } else { EF::ZERO },
                        if i == n - 1 { EF::ZERO } else { EF::ONE },
                    ],
                    idx: 0,
                    base_constraints: 0,
                    fails: vec![],
                };
                gadget.eval_air_and_lookups(air, &mut b, lookups);
                total = b.idx;
                base_n = b.base_constraints;
                for &(k, ext) in &b.fails {
                    if ext {
                        ne += 1;
                    } else {
                        nb += 1;
                    }
                    if first.len() < 8 {
                        first.push((i, k, ext));
                    }
                }
            }
            (nb, ne, total, base_n, first)
        })
        .collect();
    let eval_ms = t.elapsed().as_secs_f64() * 1e3;
    let (mut nb, mut ne, mut total, mut base_n) = (0usize, 0usize, 0usize, 0usize);
    let mut first: Vec<(usize, usize, bool)> = vec![];
    for (a, b, c, d, f) in results {
        nb += a;
        ne += b;
        total = c;
        base_n = d;
        first.extend(f);
    }
    first.sort();
    first.truncate(8);
    let zero = terminal == EF::ZERO;
    json!({"what": "p3-lookup's LogUpGadget::generate_permutation on the trace and B's preprocessed trace (random challenges, laid out as the C3 batch transcript lays them out for one global bus), then every constraint of B evaluated on every row by eval_air_and_lookups over EF8 values with the row's preprocessed values; the instance's terminal",
        "challenge_seed": format!("{seed:#x}"), "lookups": lookups.len(), "permutation_columns_ef8": pw, "max_message_width": width,
        "constraints_per_row": total, "base_constraints_per_row": base_n, "extension_constraints_per_row": total - base_n,
        "rows": n, "evaluations": total * n,
        "failing_base_evaluations": nb, "failing_extension_evaluations": ne, "first_failures_row_constraint_extension": first,
        "all_zero": nb == 0 && ne == 0,
        "terminal": <EF as BasedVectorSpace<F>>::as_basis_coefficients_slice(&terminal).iter().map(p3_field::PrimeField32::as_canonical_u32).collect::<Vec<_>>(),
        "terminal_is_zero": zero, "generate_permutation_ms": generate_ms, "evaluation_ms": eval_ms})
}
