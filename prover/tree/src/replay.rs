//! Native replay of the child's verifier (L5 layer B1, 2026-10-31; G1's module with the child's prefix as a list of
//! absorbed field elements, so that L0' v2's four constant absorptions and G1's child's public ones are both replayed).
//!
//! The child proof is verified by the unchanged C3n verifier (`p3_batch_stark_c3n::verify_batch`) under a
//! configuration that differs from the child's only by two recording wrappers:
//! - `RecPerm`, the challenger's permutation: it records every duplexing (input state, output state) of the native
//!   `DuplexChallenger<_, _, 16, 8>`;
//! - `RecMmcs`, the hiding MMCS (directly for the input batches, inside `ExtensionMmcs` for the FRI rounds): it records
//!   every multi-opening the verifier checks (the whole cap, dimensions, indices, opened rows, salts, pruned paths)
//!   and then delegates to the unchanged MMCS.
//! Both wrappers delegate every computation; the proof bytes decode to the same values. The kernel's trace generator
//! reads these records; the kernel's constraints, not this module, decide acceptance.
//! Research prototype, trace-level checks without proving; loop-internal self-review; not independently reviewed.
use std::any::Any;
use std::sync::{Arc, Mutex};

use p3_challenger::{CanObserve, DuplexChallenger};
use p3_commit::{BatchOpening, BatchOpeningRef, ExtensionMmcs, Mmcs as MmcsTrait};
use p3_dft::Radix2DitParallel;
use p3_field::Field;
use p3_fri::{FriParameters, HidingFriPcs};
use p3_koala_bear::KoalaBear as F;
use p3_matrix::{Dimensions, Matrix};
use p3_merkle_tree::{MerkleTreeMmcs, PrunedMerklePaths};
use p3_symmetric::{CryptographicPermutation, Permutation};

use crate::{CAP_HEIGHT, Compress, EF, Hash, Mmcs, Perm, os_rng};

pub type Packed = <F as Field>::Packing;

/// The challenger's permutation, recording every call made on scalar states `[F; 16]` (the packed form is used only by
/// grinding, which zero difficulty never runs).
#[derive(Clone)]
pub struct RecPerm {
    pub inner: Perm,
    pub log: Arc<Mutex<Vec<([F; 16], [F; 16])>>>,
}
impl<T: Clone + 'static> Permutation<T> for RecPerm
where
    Perm: Permutation<T>,
{
    fn permute_mut(&self, state: &mut T) {
        let input = state.clone();
        self.inner.permute_mut(state);
        let (i, o) = ((&input as &dyn Any).downcast_ref::<[F; 16]>(), (&*state as &dyn Any).downcast_ref::<[F; 16]>());
        if let (Some(i), Some(o)) = (i, o) {
            self.log.lock().unwrap().push((*i, *o));
        }
    }
}
impl<T: Clone + 'static> CryptographicPermutation<T> for RecPerm where Perm: CryptographicPermutation<T> {}

/// One multi-opening checked by the native verifier.
#[derive(Clone, Debug)]
pub struct MmcsCall {
    /// The commitment's cap (2^cap_height digests).
    pub cap: Vec<[F; 8]>,
    pub dims: Vec<(usize, usize)>,
    pub indices: Vec<usize>,
    /// `rows[q][m]`: the opened (unsalted) row of matrix m at query q, as the verifier hashes it.
    pub rows: Vec<Vec<Vec<F>>>,
    pub salts: Vec<Vec<Vec<F>>>,
    pub pruned: PrunedMerklePaths<F, 8>,
    pub accepted: bool,
}

#[derive(Clone)]
pub struct RecMmcs {
    pub inner: Mmcs,
    pub log: Arc<Mutex<Vec<MmcsCall>>>,
}

impl MmcsTrait<F> for RecMmcs {
    type ProverData<M> = <Mmcs as MmcsTrait<F>>::ProverData<M>;
    type Commitment = <Mmcs as MmcsTrait<F>>::Commitment;
    type Proof = <Mmcs as MmcsTrait<F>>::Proof;
    type MultiProof = <Mmcs as MmcsTrait<F>>::MultiProof;
    type Error = <Mmcs as MmcsTrait<F>>::Error;

    fn commit<M: Matrix<F>>(&self, inputs: Vec<M>) -> (Self::Commitment, Self::ProverData<M>) {
        self.inner.commit(inputs)
    }
    fn open_batch<M: Matrix<F>>(&self, index: usize, prover_data: &Self::ProverData<M>) -> BatchOpening<F, Self> {
        let (v, p) = self.inner.open_batch(index, prover_data).unpack();
        BatchOpening::new(v, p)
    }
    fn get_matrices<'a, M: Matrix<F>>(&self, prover_data: &'a Self::ProverData<M>) -> Vec<&'a M> {
        self.inner.get_matrices(prover_data)
    }
    fn verify_batch(
        &self,
        commit: &Self::Commitment,
        dimensions: &[Dimensions],
        index: usize,
        batch_opening: BatchOpeningRef<'_, F, Self>,
    ) -> Result<(), Self::Error> {
        self.inner.verify_batch(commit, dimensions, index, BatchOpeningRef::new(batch_opening.opened_values, batch_opening.opening_proof))
    }
    fn open_multi_batch<M: Matrix<F>>(&self, indices: &[usize], prover_data: &Self::ProverData<M>) -> (Vec<Vec<Vec<F>>>, Self::MultiProof) {
        self.inner.open_multi_batch(indices, prover_data)
    }
    fn verify_multi_batch<R: AsRef<[F]> + PartialEq>(
        &self,
        commit: &Self::Commitment,
        dimensions: &[Dimensions],
        indices: &[usize],
        opened_values: &[Vec<R>],
        proof: &Self::MultiProof,
    ) -> Result<(), Self::Error> {
        let result = self.inner.verify_multi_batch(commit, dimensions, indices, opened_values, proof);
        let (salts, pruned) = proof;
        self.log.lock().unwrap().push(MmcsCall {
            cap: commit.roots().to_vec(),
            dims: dimensions.iter().map(|d| (d.width, d.height)).collect(),
            indices: indices.to_vec(),
            rows: opened_values.iter().map(|rs| rs.iter().map(|r| r.as_ref().to_vec()).collect()).collect(),
            salts: salts.clone(),
            pruned: pruned.clone(),
            accepted: result.is_ok(),
        });
        result
    }
}

pub type RecChMmcs = ExtensionMmcs<F, EF, RecMmcs>;
pub type RecPcs = HidingFriPcs<F, Radix2DitParallel<F>, RecMmcs, RecChMmcs, rand::rngs::StdRng>;
pub type RecChallenger = DuplexChallenger<F, RecPerm, 16, 8>;
/// p3-batch-stark (and its C3n copy) uses p3-uni-stark's `StarkConfig`.
pub type RecConfig = p3_uni_stark::StarkConfig<RecPcs, EF, RecChallenger>;
pub type RecProof = p3_batch_stark_c3n::BatchProof<RecConfig>;

pub struct Recorders {
    pub perms: Arc<Mutex<Vec<([F; 16], [F; 16])>>>,
    pub mmcs: Arc<Mutex<Vec<MmcsCall>>>,
}

/// The child's configuration (the child's own, unchanged) with the recording wrappers, pre-seeded with the child's
/// prefix (the field elements its configuration observes before the batch transcript: L0' v2's domain, AIR digest,
/// descriptor and program digest; the G1 child's domain, verifier-key digest and PI198) exactly as the child's
/// configuration seeds it. With `iv` the challenger's capacity starts at those values instead of zero.
pub fn rec_config(fri: (usize, usize, usize, usize), rc: usize, prefix: &[F], iv: Option<[F; 8]>) -> (RecConfig, Recorders) {
    let perms = Arc::new(Mutex::new(vec![]));
    let calls = Arc::new(Mutex::new(vec![]));
    let perm = p3_koala_bear::default_koalabear_poseidon2_16();
    let mmcs = || RecMmcs { inner: Mmcs::new(Hash::new(perm.clone()), Compress::new(perm.clone()), CAP_HEIGHT, os_rng()), log: calls.clone() };
    let (log_blowup, log_final_poly_len, max_log_arity, num_queries) = fri;
    let params = FriParameters {
        log_blowup,
        log_final_poly_len,
        max_log_arity,
        num_queries,
        batch_proof_of_work_bits: 0,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 0,
        mmcs: RecChMmcs::new(mmcs()),
    };
    let pcs = RecPcs::new(Radix2DitParallel::default(), mmcs(), params, rc, os_rng());
    let mut ch = RecChallenger::new(RecPerm { inner: perm, log: perms.clone() });
    if let Some(iv) = iv {
        ch.sponge_state[8..].copy_from_slice(&iv);
    }
    for &v in prefix {
        ch.observe(v);
    }
    (p3_uni_stark::StarkConfig::new(pcs, ch), Recorders { perms, mmcs: calls })
}

/// Restore one full authentication path per query from a recorded multi-opening (the patched p3-merkle-tree's public
/// `restore_and_recompute_paths`, the same walk its verifier makes), on salted rows, up to the cap.
pub fn restore(call: &MmcsCall, salt: usize) -> Vec<Vec<[F; 8]>> {
    let perm = p3_koala_bear::default_koalabear_poseidon2_16();
    let plain: MerkleTreeMmcs<Packed, Packed, Hash, Compress, 2, 8> = MerkleTreeMmcs::new(Hash::new(perm.clone()), Compress::new(perm), CAP_HEIGHT);
    let dims: Vec<Dimensions> = call.dims.iter().map(|&(w, h)| Dimensions { width: w + salt, height: h }).collect();
    let salted: Vec<Vec<Vec<F>>> = call
        .rows
        .iter()
        .zip(&call.salts)
        .map(|(rs, ss)| rs.iter().zip(ss).map(|(r, s)| r.iter().chain(s.iter()).copied().collect()).collect())
        .collect();
    let paths = plain.restore_and_recompute_paths(&dims, &call.indices, &salted, &call.pruned).expect("restore paths");
    paths.into_iter().map(|p| p.siblings).collect()
}

