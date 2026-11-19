//! Honest witness generation. The AIR and its memory bus, not this native precheck, enforce F verification.
use std::collections::BTreeMap;
use p3_air::BaseAir;
use p3_commit::{Pcs, PolynomialSpace, PeriodicColumns};
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing};
use p3_koala_bear::KoalaBear as F;
use p3_symmetric::CryptographicHasher;
use p3_batch_stark_c3np::StarkGenericConfig;
use crate::{EF, Claims, childpin, areplay, schedule, tracegen};
use schedule::{Schedule, TreeKind, Src};
use tracegen::{KTrace, to_ef};

pub fn periodic(zeta: EF) -> Vec<EF> {
    let key = childpin::key::verifier_key(&childpin::key::TRUSTED_PARAMS).unwrap();
    let cfg = childpin::key::config(&childpin::key::TRUSTED_PARAMS, &[]);
    let domain = <crate::FHPcs as Pcs<EF,crate::Challenger>>::natural_domain_for_degree(cfg.pcs(), 1<<14);
    let columns = BaseAir::<F>::periodic_columns(&key.air);
    domain.evaluate_periodic_columns_at(PeriodicColumns::new(&columns, 1<<14).unwrap(), zeta)
}

pub fn digest(p: &[EF]) -> [F;8] {
    crate::Hash::new(p3_koala_bear::default_koalabear_poseidon2_16())
        .hash_iter(p.iter().flat_map(|v| v.as_basis_coefficients_slice().iter().copied()))
}

fn ef_flat(out: &mut Vec<F>, values: impl Iterator<Item=EF>) {
    for v in values { out.extend_from_slice(v.as_basis_coefficients_slice()); }
}
fn cap_flat(out: &mut Vec<F>, cap: &crate::Cap) {
    for d in cap.roots() { out.extend_from_slice(d); }
}

pub(crate) fn witness(s: &Schedule, p: &crate::FProof, claims: &Claims, advice: &[EF]) -> Vec<F> {
    let mut wit = vec![];
    let fri = &p.opening_proof.1;
    let inputs: Vec<usize> = (0..s.trees.len()).filter(|&t| matches!(s.trees[t].kind,TreeKind::Input(_))).collect();
    for (name,first,len) in &s.wit_segments {
        assert_eq!(wit.len(),*first);
        if name == "batch.main_commitment" { cap_flat(&mut wit,&p.commitments.main); }
        else if name == "batch.permutation_commitment" { cap_flat(&mut wit,p.commitments.permutation.as_ref().unwrap()); }
        else if name == "batch.quotient_random_commitment" { cap_flat(&mut wit,&p.commitments.quotient_chunks); }
        else if let Some(t) = name.strip_prefix("batch.lookup_terminal.table") {
            ef_flat(&mut wit,std::iter::once(p.lookup_terminals[t.parse::<usize>().unwrap()].as_ref().unwrap().0));
        } else if let Some(rest) = name.strip_prefix("pcs.claims.") {
            let parts: Vec<_> = rest.split('.').collect();
            let ti = s.trees.iter().position(|t| t.name == parts[0]).unwrap();
            let round = inputs.iter().position(|&t| t == ti).unwrap();
            let m: usize = parts[1][1..].parse().unwrap();
            let pn = parts[2..].join(".");
            let pt = s.trees[ti].mats[m].points.iter().position(|&i| schedule::pt_name(i)==pn).unwrap();
            ef_flat(&mut wit,claims[round].matrices[m].points[pt].values.iter().copied());
        } else if let Some(r) = name.strip_prefix("fri.round").and_then(|v| v.strip_suffix(".commitment")) {
            cap_flat(&mut wit,&fri.commit_phase_commits[r.parse::<usize>().unwrap()]);
        } else if name == "fri.final_poly" { ef_flat(&mut wit,fri.final_poly.iter().copied()); }
        else if name == "periodic.advice" { ef_flat(&mut wit,advice.iter().copied()); }
        else { panic!("unknown witness segment {name}"); }
        assert_eq!(wit.len(),first+len,"{name}");
    }
    wit
}

pub struct TraceResult {
    pub trace: KTrace,
    pub pv: Vec<F>,
    pub advice: Vec<EF>,
    pub record: serde_json::Value,
}

pub fn honest(s: &Schedule, bytes: &[u8], pi: &[u8;198]) -> TraceResult {
    let pin = &childpin::key::TRUSTED_PARAMS;
    let key = childpin::key::verifier_key(pin).unwrap();
    childpin::pi::Pi198::decode(pi).check_canonical().unwrap();
    let (proof, rest): (crate::FProof, _) = postcard::take_from_bytes(bytes).unwrap();
    assert!(rest.is_empty()); assert_eq!(postcard::to_allocvec(&proof).unwrap(),bytes);
    assert_eq!(proof.degree_bits, vec![15]);
    let pi_fields: Vec<F> = pi.iter().copied().map(F::from_u8).collect();
    let prefix = schedule::prefix_elements(&s.child.prefix,&pi_fields);
    let (cfg,rec) = areplay::rec_config((9,8,4,29),8,&prefix,None);
    let common = p3_batch_stark_c3np::CommonData::new(None,key.common.lookups.clone());
    let rp: p3_batch_stark_c3np::BatchProof<areplay::RecConfig> = postcard::from_bytes(bytes).unwrap();
    p3_batch_stark_c3np::verify_batch_with_next_row_columns(&cfg,std::slice::from_ref(&key.air),&rp,
        &[pi_fields.clone()],&common,&[key.opened.clone()],p3_batch_stark_c3np::OmittedFill::Zero).expect("native F verification");
    let permutations = rec.perms.lock().unwrap().clone();
    let calls = rec.mmcs.lock().unwrap().clone();
    let zeta = to_ef(&core::array::from_fn(|k| permutations[s.zeta_row].1[7-k]));
    let pcs_alpha = to_ef(&core::array::from_fn(|k| permutations[s.pcs_alpha_row].1[7-k]));
    let advice = periodic(zeta);
    let d = digest(&advice);
    let mut pv = pi_fields.clone(); pv.extend(zeta.as_basis_coefficients_slice()); pv.extend(d);
    assert_eq!(pv.len(),s.num_public);
    let native_cfg = childpin::key::config(pin,&pi_fields);
    let (mut claims,_,_) = p3_batch_stark_c3np::verifier::commitments_with_opening_points(&native_cfg,&[key.opened.clone()],zeta,
        &proof.commitments,&proof.opened_values,&key.common,&proof.degree_bits,&[0],&[s.child.tables[0].log_qd]).unwrap();
    for (r,round) in claims.iter_mut().enumerate() {
        for (m,mat) in round.matrices.iter_mut().enumerate() {
            for (p,pt) in mat.points.iter_mut().enumerate() { pt.values.extend(proof.opening_proof.0[r][m][p].iter().copied()); }
        }
    }
    let wit = witness(s,&proof,&claims,&advice);
    let rows = tracegen::transcript_rows_from(&s.trows,&|src| match src { Src::Const(v)=>v, Src::Pub(j)=>pv[j], Src::Wit(j)=>wit[j] },[F::ZERO;16]);
    let advice_start = s.trows.iter().position(|r| r.k==17).unwrap();
    assert_eq!(permutations.len(),advice_start);
    for (i,(input,output)) in permutations.iter().enumerate() {
        assert_eq!(*input,rows[i],"transcript input {i}");
        assert_eq!(*output,tracegen::perm(rows[i]),"transcript output {i}");
    }
    let mut kt = KTrace::new(s.n); kt.inp[..rows.len()].copy_from_slice(&rows);
    let xs = tracegen::query_elements(&s.trows,&rows,s.q);
    assert_eq!(calls.len(),s.trees.len());
    for (ti,t) in s.trees.iter().enumerate() {
        let cap = match t.kind {
            TreeKind::Input(0)=> &proof.commitments.main,
            TreeKind::Input(1)=> &proof.commitments.quotient_chunks,
            TreeKind::Input(3)=> proof.commitments.permutation.as_ref().unwrap(),
            TreeKind::Fri(r)=> &proof.opening_proof.1.commit_phase_commits[r],
            _=>panic!("unexpected tree") };
        let matching: Vec<_> = calls.iter().filter(|v| &v.cap==cap.roots()).collect();
        assert_eq!(matching.len(),1); let call=matching[0]; assert!(call.accepted);
        let dims: Vec<_> = t.mats.iter().map(|m| (m.width,1<<m.log_height)).collect(); assert_eq!(call.dims,dims);
        let sibs = areplay::restore(call,8);
        for q in 0..s.q {
            let bits = tracegen::low_of(xs[q]) >> t.skip;
            assert_eq!(call.indices[q],(bits >> t.consume_lh) as usize);
            let leaves: Vec<Vec<F>> = t.groups.iter().map(|g| g.mats.iter().flat_map(|&m|
                call.rows[q][m].iter().chain(call.salts[q][m].iter()).copied()).collect()).collect();
            tracegen::fill_tree_rows(&mut kt,s,ti,q,&leaves,&sibs[q],bits);
        }
    }
    tracegen::set_all_acc(&mut kt,s,&xs);
    let mem = tracegen::derive(&mut kt,s,&tracegen::no_hooks());
    let betas = tracegen::betas(&s.trows,&rows,s.child.fri_log_arities.len());
    let fp = p3_fri::FriParameters { log_blowup:9,log_final_poly_len:8,max_log_arity:4,num_queries:29,
        batch_proof_of_work_bits:0,commit_proof_of_work_bits:0,query_proof_of_work_bits:0,
        mmcs:crate::FChMmcs::new(crate::FMmcs::new(crate::Hash::new(p3_koala_bear::default_koalabear_poseidon2_16()),
            crate::Compress::new(p3_koala_bear::default_koalabear_poseidon2_16()),0,crate::os_rng())) };
    let mmcs = crate::FMmcs::new(crate::Hash::new(p3_koala_bear::default_koalabear_poseidon2_16()),
        crate::Compress::new(p3_koala_bear::default_koalabear_poseidon2_16()),0,crate::os_rng());
    let idx: Vec<usize> = xs.iter().map(|&v| tracegen::low_of(v) as usize).collect();
    let ro = p3_fri::verifier::open_inputs::<F,EF,crate::FMmcs,crate::FChMmcs>(&fp,24,&idx,&proof.opening_proof.1.input_openings,pcs_alpha,&mmcs,&claims).unwrap();
    let ro: Vec<BTreeMap<usize,EF>> = ro.into_iter().map(|v| v.into_iter().collect()).collect();
    let fri = tracegen::native_fri_check(s,&xs,&mem,&betas,&proof.opening_proof.1.final_poly,&ro);
    TraceResult { trace: kt, pv, advice, record: serde_json::json!({"native_f_accepted":true,
        "native_transcript_rows":permutations.len(),"fri_crosscheck":fri,"proof_sha256":crate::sha256_hex(bytes)}) }
}
