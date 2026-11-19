//! Test-only invalid-inner corpus. No guard or native verdict decides the AIR verdict.
//! Pruned paths are expanded with their original public query geometry when a mutation
//! changes Fiat-Shamir queries. Every path is then checked at the *new* index by AG.
//! The pure FRI fold reconstructs omitted row values, but its final-polynomial equality
//! is deliberately left to AG. None of this module is compiled into the native library.
use std::{path::Path,sync::{Arc,Mutex}};
use p3_field::{BasedVectorSpace,PrimeCharacteristicRing};
use p3_koala_bear::{KoalaBear as F,default_koalabear_poseidon2_16};
use serde_json::{json,Value};
use crate::{EF,FProof,Claims,awitness,areplay,agg,combine,schedule,tracegen,childpin};
use schedule::{Schedule,TreeKind,Src};

fn replay(s:&Schedule,bytes:&[u8],pi:&[u8;198])->(bool,Vec<areplay::MmcsCall>) {
    let key=childpin::key::verifier_key(&childpin::key::TRUSTED_PARAMS).unwrap();
    let pv:Vec<F>=pi.iter().copied().map(F::from_u8).collect();
    let (cfg,rec)=areplay::rec_config((9,8,4,29),8,&schedule::prefix_elements(&s.child.prefix,&pv),None);
    let p:areplay::RecProof=postcard::from_bytes(bytes).unwrap();
    let common=p3_batch_stark_c3np::CommonData::new(None,key.common.lookups.clone());
    let ok=p3_batch_stark_c3np::verify_batch_with_next_row_columns(&cfg,std::slice::from_ref(&key.air),&p,
        &[pv],&common,&[key.opened.clone()],p3_batch_stark_c3np::OmittedFill::Zero).is_ok();
    let calls=rec.mmcs.lock().unwrap().clone();(ok,calls)
}

fn claims(s:&Schedule,p:&FProof,zeta:EF)->Claims {
    let pin=&childpin::key::TRUSTED_PARAMS;
    let key=childpin::key::verifier_key(pin).unwrap();
    let cfg=childpin::key::config(pin,&[]);
    let (mut c,_,_)=p3_batch_stark_c3np::verifier::commitments_with_opening_points(&cfg,&[key.opened.clone()],zeta,
        &p.commitments,&p.opened_values,&key.common,&p.degree_bits,&[0],&[s.child.tables[0].log_qd]).unwrap();
    for (r,round) in c.iter_mut().enumerate(){for(m,mat)in round.matrices.iter_mut().enumerate(){
        for(k,point)in mat.points.iter_mut().enumerate(){point.values.extend(p.opening_proof.0[r][m][k].iter().copied());}
    }}c
}

fn unchecked(s:&Schedule,bytes:&[u8],pi:&[u8;198],geometry:&[areplay::MmcsCall])->awitness::TraceResult {
    let p:FProof=postcard::from_bytes(bytes).unwrap();
    assert_eq!(postcard::to_allocvec(&p).unwrap(),bytes);assert_eq!(p.degree_bits,[15]);
    let mut pv:Vec<F>=pi.iter().copied().map(F::from_u8).collect();pv.resize(214,F::ZERO);
    // Claims' values do not depend on their opening points. Bootstrap zeta from the
    // proof's complete transcript, then reconstruct the true opening points/advice.
    let w0=awitness::witness(s,&p,&claims(s,&p,EF::ZERO),&vec![EF::ZERO;162]);
    let r0=tracegen::transcript_rows_from(&s.trows,&|x|match x{Src::Const(v)=>v,Src::Pub(i)=>pv[i],Src::Wit(i)=>w0[i]},[F::ZERO;16]);
    let zeta=tracegen::to_ef(&core::array::from_fn(|i|tracegen::perm(r0[s.zeta_row])[7-i]));
    let advice=awitness::periodic(zeta);let digest=awitness::digest(&advice);
    pv[198..206].copy_from_slice(zeta.as_basis_coefficients_slice());pv[206..].copy_from_slice(&digest);
    let claims=claims(s,&p,zeta);let wit=awitness::witness(s,&p,&claims,&advice);
    let rows=tracegen::transcript_rows_from(&s.trows,&|x|match x{Src::Const(v)=>v,Src::Pub(i)=>pv[i],Src::Wit(i)=>wit[i]},[F::ZERO;16]);
    let xs=tracegen::query_elements(&s.trows,&rows,s.q);
    let indices:Vec<usize>=xs.iter().map(|&x|tracegen::low_of(x)as usize).collect();
    let alpha=tracegen::to_ef(&core::array::from_fn(|i|tracegen::perm(rows[s.pcs_alpha_row])[7-i]));
    let betas=tracegen::betas(&s.trows,&rows,s.child.fri_log_arities.len());
    let perm=default_koalabear_poseidon2_16();let log=Arc::new(Mutex::new(vec![]));
    let mmcs=areplay::RecMmcs{inner:crate::FMmcs::new(crate::Hash::new(perm.clone()),crate::Compress::new(perm),0,crate::os_rng()),log:log.clone(),test_bypass:true};
    let fp=p3_fri::FriParameters{log_blowup:9,log_final_poly_len:8,max_log_arity:4,num_queries:29,
        batch_proof_of_work_bits:0,commit_proof_of_work_bits:0,query_proof_of_work_bits:0,mmcs:areplay::RecChMmcs::new(mmcs.clone())};
    let rp:areplay::RecProof=postcard::from_bytes(bytes).unwrap();
    let ro=p3_fri::verifier::open_inputs::<F,EF,areplay::RecMmcs,areplay::RecChMmcs>(&fp,24,&indices,
        &rp.opening_proof.1.input_openings,alpha,&mmcs,&claims).expect("test-only opening arithmetic, no MMCS acceptance gate");
    let mut calls=log.lock().unwrap().clone();
    let rounds=s.child.fri_log_arities.len();let mut group_indices=vec![vec![];rounds];let mut fri_rows=vec![vec![];rounds];
    for(q,(&index,reduced))in indices.iter().zip(ro).enumerate(){
        let mut index=index;
        // This reconstructs every coset. Its returned final value is NOT checked
        // natively: AG's final-polynomial identity must reject the bad proof.
        let _=p3_fri::verifier::fold_query::<_,F,EF,areplay::RecChMmcs>(
            &p3_fri::TwoAdicFriFolding::<Vec<()>,()>(core::marker::PhantomData),q,&mut index,&betas,
            &s.child.fri_log_arities,&rp.opening_proof.1.commit_phase_openings,reduced,24,17,&mut group_indices,&mut fri_rows).unwrap();
    }
    for(r,t)in s.trees.iter().filter_map(|t|if let TreeKind::Fri(r)=t.kind{Some((r,t))}else{None}){
        let(salts,pruned)=&p.opening_proof.1.commit_phase_openings[r].opening_proof;
        calls.push(areplay::MmcsCall{cap:p.opening_proof.1.commit_phase_commits[r].roots().to_vec(),
            dims:t.mats.iter().map(|m|(m.width,1<<m.log_height)).collect(),indices:group_indices[r].clone(),
            rows:fri_rows[r].iter().map(|m|m.iter().map(|v|v.iter().flat_map(|x|x.as_basis_coefficients_slice().iter().copied()).collect()).collect()).collect(),
            salts:salts.clone(),pruned:pruned.clone(),accepted:false});
    }
    let mut kt=tracegen::KTrace::new(s.n);kt.inp[..rows.len()].copy_from_slice(&rows);
    for(ti,t)in s.trees.iter().enumerate(){
        let cap=match t.kind{TreeKind::Input(0)=>&p.commitments.main,TreeKind::Input(1)=>&p.commitments.quotient_chunks,
            TreeKind::Input(3)=>p.commitments.permutation.as_ref().unwrap(),TreeKind::Fri(r)=>&p.opening_proof.1.commit_phase_commits[r],_=>unreachable!()};
        let call=calls.iter().find(|c|c.cap==cap.roots()).unwrap();
        let old=geometry.iter().find(|c|c.cap==cap.roots()).unwrap();
        let mut expansion=call.clone();expansion.indices=old.indices.clone();
        // Only the multiproof expansion geometry comes from the public baseline.
        // All opening values/salts/pruned sibling bytes come from the supplied proof.
        let sibs=areplay::restore(&expansion,8);
        for q in 0..s.q {
            let leaves:Vec<Vec<F>>=t.groups.iter().map(|g|g.mats.iter().flat_map(|&m|
                call.rows[q][m].iter().chain(&call.salts[q][m]).copied()).collect()).collect();
            tracegen::fill_tree_rows(&mut kt,s,ti,q,&leaves,&sibs[q],tracegen::low_of(xs[q])>>t.skip);
        }
    }
    tracegen::set_all_acc(&mut kt,s,&xs);tracegen::derive(&mut kt,s,&tracegen::no_hooks());
    awitness::TraceResult{trace:kt,pv,advice,record:json!({"native_guard_bypassed":true,"invalid_proof_sha256":crate::sha256_hex(bytes)})}
}

pub fn run(out:&Path,inputs:&Path){
    std::fs::create_dir(out).expect("fresh negative-corpus output");
    let mut spec=agg::child_spec();spec.num_public=214;let single=Schedule::build(&spec);
    let pis:Vec<[u8;198]>=(0..4).map(|i|crate::unhex(std::fs::read_to_string(inputs.join(format!("{i}/statement/pi198.hex"))).unwrap().trim()).try_into().unwrap()).collect();
    let proofs:Vec<Vec<u8>>=(0..4).map(|i|std::fs::read(inputs.join(format!("{i}/f/proof.postcard"))).unwrap()).collect();
    let geometry:Vec<_>=(0..4).map(|i|{let(ok,g)=replay(&single,&proofs[i],&pis[i]);assert!(ok);g}).collect();
    let mut children:Vec<_>=(0..4).map(|i|awitness::honest(&single,&proofs[i],&pis[i])).collect();
    let control=unchecked(&single,&proofs[2],&pis[2],&geometry[2]);
    assert_eq!(control.trace.finalize().values,children[2].trace.finalize().values,"guard-free honest witness must equal original witness byte for byte");
    assert_eq!(control.pv,children[2].pv);
    let (s,used,stride)=combine::schedule(Schedule::build(&spec));let mut reports=vec![];
    for case in ["honest","bad_merkle_sibling","wrong_ood_value","wrong_fri_final_polynomial","f_valid_for_another_pi"]{
        let source=if case=="f_valid_for_another_pi"{1}else{2};let mut p:FProof=postcard::from_bytes(&proofs[source]).unwrap();
        match case{
            "bad_merkle_sibling"=>p.opening_proof.1.input_openings[0].opening_proof.1.sibling_hashes[0][0]+=F::ONE,
            "wrong_ood_value"=>p.opened_values.instances[0].base_opened_values.trace_local[0]+=EF::ONE,
            "wrong_fri_final_polynomial"=>p.opening_proof.1.final_poly[0]+=EF::ONE,_=>{}
        }
        let bytes=postcard::to_allocvec(&p).unwrap();
        let native=replay(&single,&bytes,&pis[2]).0;assert_eq!(native,case=="honest");
        // The verdict above is audit metadata only. No native acceptance is required below.
        let tr=unchecked(&single,&bytes,&pis[2],&geometry[source]);
        let previous=std::mem::replace(&mut children[2],tr);let(matrix,pv)=combine::trace(&children,used,stride);
        let(n,fail,bus,messages)=crate::kernel::check(&s.air,&matrix,&pv);
        let accepted=fail.is_empty()&&bus.is_empty();assert_eq!(accepted,case=="honest","AG accepted {case}");
        let groups:std::collections::BTreeSet<_>=fail.iter().map(|f|f.group).collect();
        let roles:std::collections::BTreeSet<_>=fail.iter().filter_map(|f|{
            let local=f.row.checked_sub(2*used)?;single.instr_row.iter().position(|&r|r==local).map(|i|single.program[i].role.clone())}).collect();
        reports.push(json!({"case":case,"native_accepted":native,"native_guard_bypassed":true,"AG_accepted":accepted,"passed":true,
            "rows":s.n,"constraints_per_row":n,"failures":fail.len(),"unbalanced_bus":bus.len(),"bus_messages":messages,"groups":groups,"failing_instruction_roles":roles,
            "first_failures":fail.iter().take(24).map(|f|json!([f.row,f.constraint,f.group])).collect::<Vec<_>>(),"proof_sha256":crate::sha256_hex(&bytes)}));
        std::fs::write(out.join(format!("{case}.postcard")),bytes).unwrap();children[2]=previous;
    }
    let doc=json!({"tier":"test-only, full 65536-row AG constraint identities and exact memory bus; no invalid AG proof claimed",
        "honest_unguarded_trace_equals_original":true,"AIR_or_verifier_modified":false,"cases":reports,"all_passed":true,
        "path_expansion":"original public multiproof query geometry only; changed transcript indices, openings, salts, sibling hashes and reconstructed FRI rows checked by unchanged AG",
        "review":crate::REVIEW});
    std::fs::write(out.join("inner-trace-corpus.json"),serde_json::to_vec_pretty(&doc).unwrap()).unwrap();println!("{doc}");
}
