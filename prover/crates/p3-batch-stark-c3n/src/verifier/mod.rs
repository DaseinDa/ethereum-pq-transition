// Modified by the PQ-Migrate contributors; see MODIFICATIONS.md (2026-11-02 notice).
mod data;

use alloc::vec;
use alloc::vec::Vec;

pub use data::VerifierData;
use p3_air::symbolic::{AirLayout, SymbolicExpressionExt};
use p3_air::{Air, BaseAir};
use p3_challenger::GrindingChallenger;
use p3_commit::{
    CommitmentWithOpeningPoints, Pcs, PeriodicColumns, PolynomialSpace, UnivariateStarkPcs,
};
use p3_field::{Algebra, BasedVectorSpace, ExtensionField, PrimeCharacteristicRing, PrimeField64};
use p3_lookup::logup::LogUpGadget;
use p3_lookup::{
    InteractionSymbolicBuilder, LookupError, LookupProtocol, check_multiplicity_height_bound,
};
use p3_uni_stark::{
    InvalidProofShapeError, VerificationError, recompose_quotient_from_chunks, validate_degree_bits,
};
use p3_util::checked_log_size_sum;
use p3_util::zip_eq::zip_eq;
use tracing::{info_span, instrument};

use crate::common::CommonData;
use crate::config::{Challenge, Commitment, Domain, PcsError, StarkGenericConfig as SGC, Val};
use crate::error::BatchVerificationError;
use crate::folder::VerifierConstraintFolderWithLookups;
use crate::next_row::{
    NextRowColumns, OmittedFill, TRACE_MAIN, TRACE_PERMUTATION, TRACE_PREPROCESSED, TraceSplit,
    next_row_columns_for_batch,
};
use crate::proof::{BatchCommitments, BatchOpenedValues, BatchProof};
use crate::symbolic::get_log_num_quotient_chunks_for_domain;
use crate::transcript::{BatchShape, BatchVerifierTranscript};

/// C3n: the claims of one trace's committed matrices (commitment order): each matrix at zeta with its
/// columns' values at zeta, and the next-row matrix also at `zeta_next` with the next-row values.
///
/// `local` must be as wide as the trace and `next` exactly as long as the next-row set (absent when the
/// set is empty); a mismatch is the next-row shape error of `trace`.
#[allow(clippy::too_many_arguments, clippy::type_complexity)]
fn trace_claims<EF: Clone, D: Copy, PcsErr: core::fmt::Debug>(
    air: usize,
    trace: &'static str,
    split: &TraceSplit,
    domain: D,
    zeta: EF,
    zeta_next: Option<EF>,
    local: &[EF],
    next: Option<&[EF]>,
) -> Result<Vec<(D, Vec<(EF, Vec<EF>)>)>, BatchVerificationError<PcsErr>> {
    if local.len() != split.width {
        return Err(BatchVerificationError::NextRowOpening {
            air,
            trace,
            expected: Some(split.width),
            got: Some(local.len()),
        });
    }
    if next.map(<[EF]>::len) != split.next_len() {
        return Err(BatchVerificationError::NextRowOpening {
            air,
            trace,
            expected: split.next_len(),
            got: next.map(<[EF]>::len),
        });
    }
    let parts = split.split(local);
    let mut out = Vec::with_capacity(parts.len());
    for ((_, at_next), at_zeta) in split.matrices().into_iter().zip(parts) {
        let mut points = vec![(zeta.clone(), at_zeta)];
        if at_next {
            let point = zeta_next.clone().ok_or(VerificationError::NextPointUnavailable)?;
            points.push((point, next.expect("present when the set is non-empty").to_vec()));
        }
        out.push((domain, points));
    }
    Ok(out)
}

/// C3n: a next-row column set that cannot describe instance `air` of this batch.
fn check_next_row_columns<PcsErr: core::fmt::Debug>(
    air: usize,
    columns: &NextRowColumns,
    main_width: usize,
    preprocessed_width: usize,
    permutation_width: usize,
) -> Result<(), BatchVerificationError<PcsErr>> {
    let reason = if !columns.is_well_formed() {
        Some("a set is not strictly increasing inside its width")
    } else if columns.main_width != main_width
        || columns.preprocessed_width != preprocessed_width
        || columns.permutation_width != permutation_width
    {
        Some("the set describes other widths")
    } else if columns.preprocessed_split().is_split() {
        Some("a proper subset of the preprocessed columns (the key commits one matrix per instance)")
    } else {
        None
    };
    reason.map_or(Ok(()), |reason| Err(BatchVerificationError::NextRowColumns { air, reason }))
}

/// What [`commitments_with_opening_points`] builds: the PCS opening argument itself — one
/// [`CommitmentWithOpeningPoints`] per commitment round — paired with each instance's
/// quotient-chunk domains, a byproduct of the same construction that the caller needs for its
/// own post-opening constraint check.
pub type OpeningArgumentWithQuotientDomains<SC> = (
    Vec<CommitmentWithOpeningPoints<Challenge<SC>, Commitment<SC>, Domain<SC>>>,
    Vec<Vec<Domain<SC>>>,
    Option<usize>,
);

/// Builds the `commitments_with_opening_points` a batch-STARK proof's PCS opening argument is
/// checked against: one round per commitment (the trace round, the quotient-chunks round, an
/// optional preprocessed round, an optional permutation round), each pairing a commitment with
/// the domains/points/claimed-evaluations [`UnivariateStarkPcs::verify_with_preprocessing`]
/// checks it at.
///
/// C3 (L5 plan, 2026-10-31): there is no separate ZK-randomization round. Each instance's
/// randomization polynomial is claimed in the quotient-chunks round, after every chunk, in
/// instance order, over the instance's extended trace domain, at zeta.
///
/// C3n (L5 leaf L0' v2, 2026-10-31): the trace and permutation rounds claim each instance's
/// committed matrices as its next-row column set lays them out (`TraceSplit::matrices`): a
/// matrix of the set at zeta and zeta * g, every other matrix at zeta only. The sets are the
/// caller's (`next_rows`, derived from the AIRs by `verify_batch`), never the proof's; an opened
/// row of another length is rejected here (`BatchVerificationError::NextRowOpening`).
///
/// This is exactly what [`verify_batch`] builds internally before checking the PCS — pulled
/// out so a caller that has already sampled `zeta` from its own transcript replay (and already
/// has the per-instance shape data `verify_batch`'s own precompute loop derives) can build the
/// same structure without needing a live `A: Air<...>` reference for anything beyond
/// [`BaseAir::main_next_row_columns`]/[`BaseAir::preprocessed_next_row_columns`] — e.g. a
/// recursive verifier that reads trace width and quotient degree from the proof's own
/// opened-value shape instead of a live AIR.
///
/// # Arguments
///
/// - `zeta` — the out-of-domain point, already sampled from the transcript.
/// - `degree_bits` — per-instance extended trace degree bits, straight from the proof. Both
///   the trace and quotient domain sizes are derived from these through the same
///   [`validate_degree_bits`] gate `verify_batch` applies.
/// - `preprocessed_widths`, `log_num_quotient_chunks` — per-instance, derived exactly as
///   `verify_batch`'s own precompute loop computes them. The committed chunk count follows
///   from `log_num_quotient_chunks` and the ZK setting, so it is derived here rather than
///   passed in.
///
/// Performs no transcript interaction.
///
/// # Omitted checks
///
/// Only the shape checks this construction itself needs are performed (degree-bit bounds,
/// quotient-domain sizes, matching quotient-chunk counts, preprocessed metadata agreement).
/// A caller assembling the opening argument itself inherits the rest of `verify_batch`'s
/// proof-shape validation, none of which happens here:
///
/// - per-instance counts agreeing across `airs`, opened values, public values, degree bits,
///   lookup terminals and lookups ([`InvalidProofShapeError::InstanceCountMismatch`]);
/// - absence of a separate randomization commitment (C3) and the per-instance randomization
///   openings matching [`UnivariateStarkPcs::ZK`], and each random opening's dimension;
/// - public-value counts, trace-width agreement (local and next) and the
///   `main_next_row_columns` presence rule;
/// - quotient-chunk counts and per-chunk dimensions;
/// - preprocessed presence/width agreement against `CommonData` and the
///   `preprocessed_next_row_columns` presence rule;
/// - one lookup terminal per AIR with lookups and none otherwise, plus the lookup-commitment
///   consistency check (`commitments.permutation.is_some()` iff some AIR has lookups);
/// - [`check_multiplicity_height_bound`], the LogUp bound that stops multiplicities wrapping
///   modulo `p`;
/// - the shape rule every declared periodic column must satisfy against its trace height.
///
/// A caller needing all of them should either call `verify_batch` directly or replicate the
/// ones it needs.
///
/// # Returns
///
/// `(commitments_with_opening_points, quotient_domains, preprocessed_index)` — the second element is each
/// instance's quotient-chunk domains, a byproduct of this construction that `verify_batch`
/// also needs for its own post-opening constraint check.
/// The third element comes from trusted `common` metadata and must be passed to
/// [`UnivariateStarkPcs::verify_with_preprocessing`], not inferred from the proof.
#[expect(clippy::too_many_arguments)]
pub fn commitments_with_opening_points<SC>(
    config: &SC,
    next_rows: &[NextRowColumns],
    zeta: Challenge<SC>,
    commitments: &BatchCommitments<Commitment<SC>>,
    opened_values: &BatchOpenedValues<Challenge<SC>>,
    common: &CommonData<SC>,
    degree_bits: &[usize],
    preprocessed_widths: &[usize],
    log_num_quotient_chunks: &[usize],
) -> Result<OpeningArgumentWithQuotientDomains<SC>, BatchVerificationError<PcsError<SC>>>
where
    SC: SGC,
{
    if next_rows.len() != degree_bits.len() || opened_values.instances.len() != degree_bits.len() {
        return Err(InvalidProofShapeError::InstanceCountMismatch.into());
    }
    let pcs = config.pcs();
    let is_zk = config.is_zk();
    let mut coms_to_verify = vec![];

    // Trace round: per instance, open at zeta and zeta_next.
    //
    // The extended domain size is `1 << degree_bits[i]`, gated by `validate_degree_bits` so
    // that an out-of-range degree is an error rather than an overflow, and so that a caller
    // cannot pass a domain size disagreeing with the degree bits it also passed.
    let trace_domain_pairs = degree_bits
        .iter()
        .enumerate()
        .map(|(i, &ext_db)| {
            let (_, ext_domain_size) = validate_degree_bits(
                Some(i),
                ext_db,
                is_zk,
                pcs.log_min_trace_height(),
                pcs.log_max_trace_height(),
            )?;
            Ok((
                pcs.natural_domain_for_degree(ext_domain_size >> is_zk),
                pcs.natural_domain_for_degree(ext_domain_size),
            ))
        })
        .collect::<Result<Vec<_>, InvalidProofShapeError>>()?;
    let (trace_domains, ext_trace_domains): (Vec<Domain<SC>>, Vec<Domain<SC>>) =
        trace_domain_pairs.into_iter().unzip();

    // C3: no separate randomization round; the polynomials are claimed in the quotient round.

    // C3n: each instance's main matrices as its next-row set lays them out.
    let mut trace_round = Vec::new();
    for (i, (ext_dom, inst_opened_vals)) in ext_trace_domains
        .iter()
        .zip(opened_values.instances.iter())
        .enumerate()
    {
        let base = &inst_opened_vals.base_opened_values;
        trace_round.extend(trace_claims(
            i,
            "main",
            &next_rows[i].main_split(),
            *ext_dom,
            zeta,
            trace_domains[i].next_point(zeta),
            &base.trace_local,
            base.trace_next.as_deref(),
        )?);
    }
    coms_to_verify.push((commitments.main.clone(), trace_round));

    // Quotient chunks round: flatten per-instance chunks to match commit order.
    // Use extended domains for the outer commit domain, with size = base_degree * num_quotient_chunks.
    let quotient_domains: Vec<Vec<Domain<SC>>> = (0..degree_bits.len())
        .map(|i| {
            let ext_db = degree_bits[i];
            let log_num_chunks = log_num_quotient_chunks[i];
            // The committed chunk count, ZK randomization included.
            let (_, n_chunks) = checked_log_size_sum(log_num_chunks, is_zk).ok_or_else(|| {
                InvalidProofShapeError::QuotientDomainTooLarge {
                    air: Some(i),
                    maximum: usize::BITS as usize - 1,
                    got: log_num_chunks.saturating_add(is_zk),
                }
            })?;
            let ext_dom = ext_trace_domains[i];
            let (quotient_domain_log_size, quotient_domain_size) =
                checked_log_size_sum(ext_db, log_num_chunks).ok_or_else(|| {
                    InvalidProofShapeError::QuotientDomainTooLarge {
                        air: Some(i),
                        maximum: usize::BITS as usize - 1,
                        got: ext_db.saturating_add(log_num_chunks),
                    }
                })?;
            let qdom = ext_dom
                .try_create_disjoint_domain(quotient_domain_size)
                .ok_or_else(|| InvalidProofShapeError::QuotientDomainTooLarge {
                    air: Some(i),
                    maximum: pcs.log_max_trace_height(),
                    got: quotient_domain_log_size,
                })?;
            Ok(qdom.split_domains(n_chunks))
        })
        .collect::<Result<Vec<_>, InvalidProofShapeError>>()?;

    // When ZK is enabled, the size of the quotient chunks' domains doubles.
    let randomized_quotient_chunks_domains = quotient_domains
        .iter()
        .map(|doms| {
            doms.iter()
                .map(|dom| pcs.natural_domain_for_degree(dom.size() << is_zk))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    // Build the per-matrix openings for the aggregated quotient commitment.
    let mut qc_round = Vec::new();
    for (i, domains) in randomized_quotient_chunks_domains.iter().enumerate() {
        let inst_qcs = &opened_values.instances[i]
            .base_opened_values
            .quotient_chunks;
        for (d, vals) in zip_eq(
            domains.iter(),
            inst_qcs,
            VerificationError::from(InvalidProofShapeError::QuotientDomainsCountMismatch {
                air: i,
            }),
        )? {
            qc_round.push((*d, vec![(zeta, vals.clone())]));
        }
    }
    // C3: the randomization polynomials are the last matrices of the quotient commitment, one per
    // instance in instance order, over the extended trace domain, opened at zeta. Their presence
    // exactly under zero knowledge is checked by the caller (`verify_batch`) before this runs.
    for (domain, inst_opened_vals) in ext_trace_domains.iter().zip(opened_values.instances.iter()) {
        if let Some(random_vals) = &inst_opened_vals.base_opened_values.random {
            qc_round.push((*domain, vec![(zeta, random_vals.clone())]));
        }
    }
    coms_to_verify.push((commitments.quotient_chunks.clone(), qc_round));

    // Preprocessed rounds: a single global commitment with one matrix per
    // instance that has preprocessed columns.
    let preprocessed_index = common.preprocessed.as_ref().map(|_| coms_to_verify.len());
    if let Some(global) = &common.preprocessed {
        let mut pre_round = Vec::new();

        for (matrix_index, &inst_idx) in global.matrix_to_instance.iter().enumerate() {
            let pre_w = preprocessed_widths[inst_idx];
            if pre_w == 0 {
                return Err(
                    InvalidProofShapeError::PreprocessedMetadataMismatch { air: inst_idx }.into(),
                );
            }

            let inst = &opened_values.instances[inst_idx];
            let preprocessed = inst
                .base_opened_values
                .preprocessed
                .as_ref()
                .ok_or_else(|| {
                    VerificationError::from(InvalidProofShapeError::MissingPreprocessedValues {
                        air: inst_idx,
                    })
                })?;
            let local = &preprocessed.local;

            // Validate that the preprocessed data's extended degree matches what we expect.
            let ext_db = degree_bits[inst_idx];

            let meta = global.instances[inst_idx].as_ref().ok_or_else(|| {
                VerificationError::from(InvalidProofShapeError::PreprocessedMetadataMismatch {
                    air: inst_idx,
                })
            })?;
            if meta.matrix_index != matrix_index || meta.degree_bits != ext_db {
                return Err(
                    InvalidProofShapeError::PreprocessedMetadataMismatch { air: inst_idx }.into(),
                );
            }

            let meta_db = meta.degree_bits;
            let pre_domain = pcs.natural_domain_for_degree(1 << meta_db);
            // C3n: the derived set, none or every column (one key matrix per instance).
            let pre_split = next_rows[inst_idx].preprocessed_split();
            if pre_split.is_split() {
                return Err(BatchVerificationError::NextRowColumns {
                    air: inst_idx,
                    reason: "a proper subset of the preprocessed columns (the key commits one matrix per instance)",
                });
            }
            if local.len() != pre_w
                || preprocessed.next.as_ref().map(Vec::len) != pre_split.next_len()
            {
                return Err(BatchVerificationError::NextRowOpening {
                    air: inst_idx,
                    trace: "preprocessed",
                    expected: pre_split.next_len(),
                    got: preprocessed.next.as_ref().map(Vec::len),
                });
            }
            if !pre_split.next.is_empty() {
                let next = preprocessed.next.as_ref().ok_or_else(|| {
                    VerificationError::from(InvalidProofShapeError::MissingPreprocessedValues {
                        air: inst_idx,
                    })
                })?;
                let zeta_next_i = trace_domains[inst_idx]
                    .next_point(zeta)
                    .ok_or(VerificationError::NextPointUnavailable)?;

                pre_round.push((
                    pre_domain,
                    vec![(zeta, local.clone()), (zeta_next_i, next.clone())],
                ));
            } else {
                pre_round.push((pre_domain, vec![(zeta, local.clone())]));
            }
        }

        coms_to_verify.push((global.commitment.clone(), pre_round));
    }

    if commitments.permutation.is_some() {
        let permutation_commit = commitments.permutation.clone().unwrap();
        let mut permutation_round = Vec::new();
        for (i, (ext_dom, inst_opened_vals)) in ext_trace_domains
            .iter()
            .zip(opened_values.instances.iter())
            .enumerate()
        {
            // C3n: the next-row values are the coordinates of the extension columns read there (the
            // stock layout requires them as long as the values at zeta).
            let split = next_rows[i].permutation_split(Challenge::<SC>::DIMENSION);
            if split.width == 0 {
                if !inst_opened_vals.permutation_local.is_empty()
                    || !inst_opened_vals.permutation_next.is_empty()
                {
                    return Err(LookupError::PermutationLengthMismatch { air: i }.into());
                }
                continue;
            }
            let next = (!inst_opened_vals.permutation_next.is_empty())
                .then_some(inst_opened_vals.permutation_next.as_slice());
            permutation_round.extend(trace_claims(
                i,
                "permutation",
                &split,
                *ext_dom,
                zeta,
                trace_domains[i].next_point(zeta),
                &inst_opened_vals.permutation_local,
                next,
            )?);
        }
        coms_to_verify.push((permutation_commit, permutation_round));
    }

    Ok((
        coms_to_verify.into_iter().map(Into::into).collect(),
        quotient_domains,
        preprocessed_index,
    ))
}

/// Verify a batch proof.
///
/// C3n: the columns each instance must have opened at `zeta * g` are derived from its AIR and the key's
/// lookups ([`next_row_columns_for_batch`]), never read from the proof; omitted next-row entries are zero
/// in the constraint check.
#[instrument(skip_all)]
pub fn verify_batch<SC, A>(
    config: &SC,
    airs: &[A],
    proof: &BatchProof<SC>,
    public_values: &[Vec<Val<SC>>],
    common: &CommonData<SC>,
) -> Result<(), BatchVerificationError<PcsError<SC>>>
where
    SC: SGC,
    Val<SC>: PrimeField64,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>: Algebra<SC::Challenge>,
    A: Air<InteractionSymbolicBuilder<Val<SC>, SC::Challenge>>
        + for<'a> Air<VerifierConstraintFolderWithLookups<'a, SC>>,
    Challenge<SC>: BasedVectorSpace<Val<SC>>,
    SC::Challenger: GrindingChallenger<Witness = Val<SC>>,
{
    // The derivation reads the key per instance, so the key must describe this batch first.
    if airs.len() != common.lookups.len()
        || common
            .preprocessed
            .as_ref()
            .is_some_and(|global| global.instances.len() != airs.len())
    {
        return Err(InvalidProofShapeError::InstanceCountMismatch.into());
    }
    let next_rows = next_row_columns_for_batch(airs.iter(), common);
    verify_batch_with_next_row_columns(
        config,
        airs,
        proof,
        public_values,
        common,
        &next_rows,
        OmittedFill::Zero,
    )
}

/// [`verify_batch`] with the next-row column sets and the value of omitted next-row entries given by the
/// caller (C3n). For controls only: [`verify_batch`] is this with the derived sets and zero.
#[instrument(skip_all)]
pub fn verify_batch_with_next_row_columns<SC, A>(
    config: &SC,
    airs: &[A],
    proof: &BatchProof<SC>,
    public_values: &[Vec<Val<SC>>],
    common: &CommonData<SC>,
    next_rows: &[NextRowColumns],
    omitted: OmittedFill,
) -> Result<(), BatchVerificationError<PcsError<SC>>>
where
    SC: SGC,
    Val<SC>: PrimeField64,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>: Algebra<SC::Challenge>,
    A: Air<InteractionSymbolicBuilder<Val<SC>, SC::Challenge>>
        + for<'a> Air<VerifierConstraintFolderWithLookups<'a, SC>>,
    Challenge<SC>: BasedVectorSpace<Val<SC>>,
    SC::Challenger: GrindingChallenger<Witness = Val<SC>>,
{
    // Public inputs reach this proof only through AIR constraints.
    // A cell listed for backend binding would go completely unbound.
    assert!(
        airs.iter().all(|air| air.public_boundary_io().is_empty()),
        "batch-stark does not support boundary-IO public values; bind them with AIR constraints"
    );

    // TODO: Extend if additional lookup gadgets are added.
    let lookup_gadget = LogUpGadget::new();

    let BatchProof {
        commitments,
        opened_values,
        opening_proof,
        lookup_terminals,
        degree_bits,
        lookup_pow_witness,
        ood_pow_witness,
    } = proof;

    let all_lookups = &common.lookups;

    let pcs = config.pcs();

    // Sanity checks
    if airs.len() != opened_values.instances.len()
        || airs.len() != public_values.len()
        || airs.len() != degree_bits.len()
        || airs.len() != lookup_terminals.len()
        || airs.len() != all_lookups.len()
        || common
            .preprocessed
            .as_ref()
            .is_some_and(|global| global.instances.len() != airs.len())
    {
        return Err(InvalidProofShapeError::InstanceCountMismatch.into());
    }
    // C3n: one next-row column set per instance.
    if next_rows.len() != airs.len() {
        return Err(InvalidProofShapeError::InstanceCountMismatch.into());
    }

    // Check that the randomization openings are/are not present depending on the ZK setting.
    // - If ZK is enabled, the prover should have opened a randomization polynomial per instance.
    // - If ZK is not enabled, the prover should not have.
    // C3: the polynomials are committed in the quotient tree, so a separate randomization
    // commitment is never present, whatever the setting (a stock-layout proof carries one).
    if (opened_values
        .instances
        .iter()
        .any(|ov| ov.base_opened_values.random.is_some() != SC::Pcs::ZK))
        || commitments.random.is_some()
    {
        return Err(VerificationError::RandomizationError.into());
    }

    // Validate opened values shape per instance and observe per-instance binding data.
    // Precompute per-instance preprocessed widths and number of quotient chunks.
    let mut preprocessed_widths = Vec::with_capacity(airs.len());
    // Number of quotient chunks per instance before ZK randomization.
    let mut log_num_quotient_chunks = Vec::with_capacity(airs.len());
    // The total number of quotient chunks, including ZK randomization.
    let mut num_quotient_chunks = Vec::with_capacity(airs.len());
    let mut base_degree_bits = Vec::with_capacity(airs.len());
    let mut ext_domain_sizes = Vec::with_capacity(airs.len());

    for (i, air) in airs.iter().enumerate() {
        let (base_db, ext_domain_size) = validate_degree_bits(
            Some(i),
            degree_bits[i],
            config.is_zk(),
            pcs.log_min_trace_height(),
            pcs.log_max_trace_height(),
        )?;
        base_degree_bits.push(base_db);
        ext_domain_sizes.push(ext_domain_size);

        let pre_w = common
            .preprocessed
            .as_ref()
            .and_then(|g| g.instances[i].as_ref().map(|m| m.width))
            .unwrap_or(0);
        preprocessed_widths.push(pre_w);

        let layout = AirLayout {
            preprocessed_width: pre_w,
            main_width: air.width(),
            num_public_values: air.num_public_values(),
            num_periodic_columns: air.num_periodic_columns(),
            ..Default::default()
        };
        let log_num_chunks =
            info_span!("infer log of constraint degree", air_idx = i).in_scope(|| {
                get_log_num_quotient_chunks_for_domain::<_, SC::Challenge, A, _>(
                    air,
                    layout,
                    pcs.natural_domain_for_degree(1usize << base_db),
                    &all_lookups[i],
                    config.is_zk(),
                    &lookup_gadget,
                )
            });
        log_num_quotient_chunks.push(log_num_chunks);

        let (_, n_chunks) =
            checked_log_size_sum(log_num_chunks, config.is_zk()).ok_or_else(|| {
                InvalidProofShapeError::QuotientDomainTooLarge {
                    air: Some(i),
                    maximum: usize::BITS as usize - 1,
                    got: log_num_chunks.saturating_add(config.is_zk()),
                }
            })?;
        num_quotient_chunks.push(n_chunks);
    }

    // Soundness: bound LogUp multiplicities so none wraps modulo p.
    // Base degree bits give the same heights the prover used.
    let trace_heights: Vec<usize> = base_degree_bits.iter().map(|&b| 1usize << b).collect();
    check_multiplicity_height_bound(all_lookups, &trace_heights)?;

    for (i, air) in airs.iter().enumerate() {
        let air_width = A::width(air);
        let expected_public_values_len = air.num_public_values();
        let got_public_values_len = public_values[i].len();
        let inst_opened_vals = &opened_values.instances[i];
        let inst_base_opened_vals = &inst_opened_vals.base_opened_values;

        if got_public_values_len != expected_public_values_len {
            return Err(InvalidProofShapeError::PublicValuesLengthMismatch {
                expected: expected_public_values_len,
                got: got_public_values_len,
            }
            .into());
        }

        // C3n: the caller's next-row column set must describe this instance.
        let permutation_width = if all_lookups[i].is_empty() {
            0
        } else {
            all_lookups[i].len() + 1
        };
        check_next_row_columns(
            i,
            &next_rows[i],
            air_width,
            preprocessed_widths[i],
            permutation_width,
        )?;

        // Validate trace widths match the AIR
        if inst_base_opened_vals.trace_local.len() != air_width {
            return Err(InvalidProofShapeError::TraceLocalWidthMismatch {
                air: i,
                expected: air_width,
                got: inst_base_opened_vals.trace_local.len(),
            }
            .into());
        }
        // C3n: the next row carries exactly the columns the AIR reads there: none (absent) or that
        // many values. Presence is tested as well as length: an empty row is still an opening.
        let expected_next = next_rows[i].main_split().next_len();
        let got_next = inst_base_opened_vals.trace_next.as_ref().map(Vec::len);
        if got_next != expected_next {
            return Err(BatchVerificationError::NextRowOpening {
                air: i,
                trace: "main",
                expected: expected_next,
                got: got_next,
            });
        }

        // Validate quotient chunks structure
        let n_chunks = num_quotient_chunks[i];
        if inst_base_opened_vals.quotient_chunks.len() != n_chunks {
            return Err(InvalidProofShapeError::QuotientChunksCountMismatch {
                air: i,
                expected: n_chunks,
                got: inst_base_opened_vals.quotient_chunks.len(),
            }
            .into());
        }

        for chunk in &inst_base_opened_vals.quotient_chunks {
            if chunk.len() != Challenge::<SC>::DIMENSION {
                return Err(
                    InvalidProofShapeError::QuotientChunkDimensionMismatch { air: i }.into(),
                );
            }
        }

        // Validate random commit
        if inst_opened_vals
            .base_opened_values
            .random
            .as_ref()
            .is_some_and(|r_comm| r_comm.len() != SC::Challenge::DIMENSION)
        {
            return Err(VerificationError::RandomizationError.into());
        }

        // Validate that any preprocessed width implied by CommonData matches the opened shapes.
        //
        //     no preprocessed columns    -> no opening at all
        //     reads the next row         -> next row present, as wide as the current row
        //     does not read the next row -> next row absent
        //
        // Presence is tested rather than width.
        // An empty row is zero columns wide, yet still an opening nothing binds.
        let pre_w = preprocessed_widths[i];
        // C3n: the derived set (none or every column, checked above), not the AIR's declaration.
        let pre_next = next_rows[i].preprocessed_split().next_len();
        match &inst_base_opened_vals.preprocessed {
            Some(_) if pre_w == 0 => {
                return Err(
                    InvalidProofShapeError::UnexpectedPreprocessedValues { air: Some(i) }.into(),
                );
            }
            Some(preprocessed) => {
                if preprocessed.local.len() != pre_w {
                    return Err(InvalidProofShapeError::PreprocessedWidthMismatch { air: i }.into());
                }
                let got = preprocessed.next.as_ref().map(Vec::len);
                if got != pre_next {
                    return Err(BatchVerificationError::NextRowOpening {
                        air: i,
                        trace: "preprocessed",
                        expected: pre_next,
                        got,
                    });
                }
            }
            None if pre_w > 0 => {
                return Err(InvalidProofShapeError::PreprocessedWidthMismatch { air: i }.into());
            }
            None => {}
        }

        // Width of the two lookup permutation rows, under the single-terminal layout:
        //
        //     no lookups -> no permutation columns at all
        //     k lookups  -> one shared accumulator column plus one fraction column per lookup
        //
        // Each column holds extension-field elements, flattened into base-field coefficients.
        // The opened row is therefore that column count times the extension degree.
        let expected_perm_len = if all_lookups[i].is_empty() {
            0
        } else {
            (all_lookups[i].len() + 1) * Challenge::<SC>::DIMENSION
        };

        // Checked alongside every other proof-carried width.
        // A malformed shape is then rejected before any transcript work begins.
        if inst_opened_vals.permutation_local.len() != expected_perm_len {
            return Err(LookupError::PermutationWidthMismatch {
                air: i,
                expected: expected_perm_len,
            }
            .into());
        }
        // C3n: at the next row only the coordinates of the extension columns read there (the
        // accumulator's, for LogUp); none without lookups.
        let expected_perm_next = next_rows[i]
            .permutation_split(Challenge::<SC>::DIMENSION)
            .next
            .len();
        if inst_opened_vals.permutation_next.len() != expected_perm_next {
            return Err(BatchVerificationError::NextRowOpening {
                air: i,
                trace: "permutation",
                expected: Some(expected_perm_next),
                got: Some(inst_opened_vals.permutation_next.len()),
            });
        }

        // One terminal per AIR with lookups; none otherwise.
        let expected_present = !all_lookups[i].is_empty();
        let got_present = lookup_terminals[i].is_some();
        if expected_present != got_present {
            return Err(LookupError::TerminalPresenceMismatch {
                air: i,
                expected_present,
                got_present,
            }
            .into());
        }
    }

    // Validate the shape of the lookup commitment.
    let num_lookup_instances = all_lookups.iter().filter(|c| !c.is_empty()).count();

    if commitments.permutation.is_some() != (num_lookup_instances > 0) {
        return Err(LookupError::CommitmentMismatch.into());
    }

    // Transcript: describe the run, then seed a driver from that description.
    //
    // Every number here comes from the AIRs, the common data, or the config.
    // Every proof-carried count the description relies on was rejected above.
    let shape = BatchShape {
        trace_widths: airs.iter().map(A::width).collect(),
        public_value_counts: airs.iter().map(BaseAir::num_public_values).collect(),
        preprocessed_widths: preprocessed_widths.clone(),
        has_preprocessed_commitment: common.preprocessed.is_some(),
        num_lookup_instances,
        lookup_pow_bits: config.lookup_proof_of_work_bits(),
        has_randomization_commitment: SC::Pcs::ZK,
        ood_pow_bits: config.ood_proof_of_work_bits(),
        next_row_columns: next_rows.to_vec(),
    };

    let mut challenger = config.initialise_challenger();
    let mut transcript =
        BatchVerifierTranscript::<SC::Challenger, Val<SC>, Challenge<SC>, Commitment<SC>>::new(
            &mut challenger,
            shape,
        );

    // The size of each instance is the prover's to choose, so it is replayed.
    transcript.instance_bindings(degree_bits);

    transcript.main_phase(commitments.main.clone(), public_values);
    transcript.preprocessed_phase(common.preprocessed.as_ref().map(|g| g.commitment.clone()));

    // Replay the grind guarding the lookup challenges, then redraw them.
    //
    // Why: the check runs before the first squeeze.
    // A bad witness is therefore rejected without the challenges ever being drawn.
    let challenges_per_instance =
        transcript.lookup_phase(all_lookups, &lookup_gadget, *lookup_pow_witness)?;

    let terminal_values: Vec<Challenge<SC>> =
        lookup_terminals.iter().flatten().map(|t| t.0).collect();
    let alpha: Challenge<SC> =
        transcript.permutation_phase(commitments.permutation.clone(), &terminal_values);

    // C3: that one commitment also holds the randomization polynomials under zero knowledge.
    transcript.quotient_phase(commitments.quotient_chunks.clone());

    // Replay the grind guarding the out-of-domain point, then redraw it.
    //
    // Why: the check runs before the sample.
    // A bad witness is therefore rejected without zeta ever being drawn.
    let zeta = transcript.ood_phase(*ood_pow_witness)?;

    // Assembling the opening argument can still reject the proof's shape.
    //
    // The driver is mid-pattern here, and dropping it unfinished panics.
    // Releasing its completeness check first keeps the rejection the only failure.
    let opening_argument = commitments_with_opening_points(
        config,
        next_rows,
        zeta,
        commitments,
        opened_values,
        common,
        degree_bits,
        &preprocessed_widths,
        &log_num_quotient_chunks,
    );
    let (coms_to_verify, quotient_domains, preprocessed_index) = match opening_argument {
        Ok(argument) => argument,
        Err(err) => {
            transcript.abort();
            return Err(err);
        }
    };

    // Verify all openings via PCS, on the same sponge and under its own description.
    let opening_result = transcript.delegate(|challenger| {
        pcs.verify_with_preprocessing(
            coms_to_verify,
            opening_proof,
            challenger,
            preprocessed_index,
        )
    });

    // The bracket is closed either way, so the driver finishes before the rejection travels.
    transcript.finish();
    opening_result.map_err(VerificationError::InvalidOpeningArgument)?;

    // Un-extended trace domains, one per instance — needed below for periodic-column
    // evaluation. `commitments_with_opening_points` derives the same domains internally but
    // doesn't expose them, since only the caller's own post-opening constraint check needs them.
    let trace_domains: Vec<Domain<SC>> = ext_domain_sizes
        .iter()
        .map(|&ext_size| pcs.natural_domain_for_degree(ext_size >> config.is_zk()))
        .collect();

    // Now check constraint equality per instance.
    // For each instance, recombine quotient from chunks at zeta and compare to folded constraints.
    for (i, air) in airs.iter().enumerate() {
        let _air_span = info_span!("verify constraints", air_idx = i).entered();

        let qc_domains = &quotient_domains[i];

        // Recompose quotient(zeta) from chunks using utility function.
        let quotient = recompose_quotient_from_chunks::<SC>(
            qc_domains,
            &opened_values.instances[i]
                .base_opened_values
                .quotient_chunks,
            zeta,
        );

        // Recompose permutation openings into extension-field columns.
        //
        // Shapes:
        // - commitment           — base-flattened matrix, width = aux_width * DIMENSION.
        // - constraint evaluator — extension-field matrix, width = aux_width.
        //
        // aux_width under the single-terminal layout:
        // - col 0:      shared accumulator
        // - col i + 1:  fraction column for lookup i
        // - so aux_width = num_lookups + 1, or 0 when the AIR declares no lookup.
        let aux_width = if all_lookups[i].is_empty() {
            0
        } else {
            all_lookups[i].len() + 1
        };

        // Number of base-field coefficients one extension-field element flattens into.
        let ext_degree = Challenge::<SC>::DIMENSION;

        let recompose = |flat: &[Challenge<SC>]| -> Vec<Challenge<SC>> {
            if aux_width == 0 {
                return vec![];
            }
            // Each `ext_degree`-chunk holds the basis coefficients (in EF) of one EF element.
            // chunks_exact yields chunks of exactly `ext_degree` = DIMENSION, so the unwrap
            // below cannot panic.
            flat.chunks_exact(ext_degree)
                .map(|chunk| {
                    Challenge::<SC>::from_ext_basis_coefficients(chunk)
                        .expect("chunk length matches DIMENSION by construction")
                })
                .collect()
        };

        // C3n: every next row at its full width, the opened values at their columns and every omitted
        // entry from `omitted` (zero in `verify_batch`). No constraint reads an omitted entry, which is
        // how the sets are derived, so the folded constraints do not depend on the fill.
        let fill = |trace: u64| {
            move |column: usize| {
                Challenge::<SC>::from_basis_coefficients_fn(|k| {
                    Val::<SC>::from_u64(omitted.coefficient(i, trace, column, k))
                })
            }
        };
        let inst = &opened_values.instances[i];
        let perm_split = next_rows[i].permutation_split(ext_degree);
        let perm_next_full = perm_split.expand_next(&inst.permutation_next, fill(TRACE_PERMUTATION));
        let perm_local_ext = recompose(&inst.permutation_local);
        let perm_next_ext = recompose(&perm_next_full);

        // Verify constraints at zeta using utility function.
        let init_trace_domain = trace_domains[i];
        let trace_next_full = next_rows[i].main_split().expand_next(
            inst.base_opened_values.trace_next.as_deref().unwrap_or(&[]),
            fill(TRACE_MAIN),
        );
        let trace_next_ref = trace_next_full.as_slice();
        let pre_next_full = next_rows[i].preprocessed_split().expand_next(
            inst.base_opened_values.preprocessed_next().unwrap_or(&[]),
            fill(TRACE_PREPROCESSED),
        );
        let pre_next_ref = pre_next_full.as_slice();
        let perm_vals: Vec<SC::Challenge> = lookup_terminals[i].iter().map(|t| t.0).collect();

        // Periodic columns are AIR logic; a malformed one must error, not panic.
        let declared = air.periodic_columns();
        let periodic_columns = PeriodicColumns::new(&declared, trace_domains[i].size())?;

        let periodic_values: Vec<Challenge<SC>> =
            trace_domains[i].evaluate_periodic_columns_at(periodic_columns, zeta);
        let verifier_data = VerifierData {
            trace_local: &opened_values.instances[i].base_opened_values.trace_local,
            trace_next: trace_next_ref,
            preprocessed_local: opened_values.instances[i]
                .base_opened_values
                .preprocessed_local()
                .unwrap_or(&[]),
            preprocessed_next: pre_next_ref,
            permutation_local: &perm_local_ext,
            permutation_next: &perm_next_ext,
            permutation_challenges: &challenges_per_instance[i],
            permutation_values: &perm_vals,
            periodic_values: &periodic_values,
            lookups: &all_lookups[i],
            public_values: &public_values[i],
            trace_domain: init_trace_domain,
            zeta,
            alpha,
            quotient,
        };

        verifier_data
            .verify_constraints_with_lookups::<A, LogUpGadget, PcsError<SC>>(air, &lookup_gadget)
            .map_err(|e| match e {
                VerificationError::OodEvaluationMismatch { .. } => {
                    VerificationError::OodEvaluationMismatch { index: Some(i) }
                }
                other => other,
            })?;
    }

    // Single-terminal LogUp cross-AIR check.
    //
    // Each AIR with lookups commits one terminal: the sum of every per-row
    // rational contribution across its trace.
    //
    // Soundness:
    // - The total across the batch must be zero.
    // - Bus challenges are sampled after the main commitment, so any
    //   per-bus imbalance survives the collapse with overwhelming probability.
    lookup_gadget.verify_terminal_sum(lookup_terminals)?;

    Ok(())
}
