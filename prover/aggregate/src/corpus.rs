//! Mandatory public-vector rejection corpus. Does not claim to be a proof of soundness.
use std::{path::Path,time::Instant};
use p3_field::{PrimeCharacteristicRing,PrimeField32,BasedVectorSpace};
use p3_koala_bear::KoalaBear as F;
use serde_json::json;
use crate::{aggregate_native as a,childpin};
use childpin::key::{FProof,EF};

fn child_ok(bytes:&[u8],pi:&[u8])->bool {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let (p,r):(FProof,_)=postcard::take_from_bytes(bytes).unwrap();
        if !r.is_empty()||p.degree_bits!=[15]||postcard::to_allocvec(&p).unwrap()!=bytes{return false;}
        let key=childpin::key::verifier_key(&childpin::key::TRUSTED_PARAMS).unwrap();
        let pv:Vec<F>=pi.iter().copied().map(F::from_u8).collect();
        let cfg=childpin::key::config(&childpin::key::TRUSTED_PARAMS,&pv);
        p3_batch_stark_c3np::verify_batch_with_next_row_columns(&cfg,std::slice::from_ref(&key.air),&p,&[pv],&key.common,
            std::slice::from_ref(&key.opened),p3_batch_stark_c3np::OmittedFill::Zero).is_ok()
    })).unwrap_or(false)
}
pub fn run(inputs:&Path,proof:&Path,out:&Path) {
    std::fs::create_dir(out).expect("fresh corpus directory");
    let carrier=std::fs::read(proof.join("carrier.bin")).unwrap();
    let statement=std::fs::read(proof.join("statement.bin")).unwrap();
    let children:Vec<Vec<u8>>=(0..4).map(|i|std::fs::read(inputs.join(i.to_string()).join("f/proof.postcard")).unwrap()).collect();
    let pis:Vec<&[u8]>=statement[6..].chunks_exact(198).collect();
    assert!(children.iter().zip(&pis).all(|(p,pi)|child_ok(p,pi)));
    let mut rows=vec![];
    for name in ["one_bad_merkle_sibling","one_bad_ood_value","one_bad_fri_final_polynomial","one_f_valid_for_another_pi"] {
        let mut p:FProof=postcard::from_bytes(&children[2]).unwrap();
        match name {
            "one_bad_merkle_sibling"=>p.opening_proof.1.input_openings[0].opening_proof.1.sibling_hashes[0][0]+=F::ONE,
            "one_bad_ood_value"=>p.opened_values.instances[0].base_opened_values.trace_local[0]+=EF::ONE,
            "one_bad_fri_final_polynomial"=>p.opening_proof.1.final_poly[0]+=EF::ONE,
            _=>{}
        }
        let bytes=if name=="one_f_valid_for_another_pi"{children[1].clone()}else{postcard::to_allocvec(&p).unwrap()};
        let t=Instant::now();
        let accepted=(0..4).all(|i|child_ok(if i==2 {&bytes}else{&children[i]},pis[i]));
        std::fs::write(out.join(format!("{name}.postcard")),&bytes).unwrap();
        rows.push(json!({"case":name,"accepted":accepted,"expected":"reject","passed":!accepted,"layer":"four-input F native boundary; not an invalid AG proof experiment","ms":t.elapsed().as_secs_f64()*1000.}));
        assert!(!accepted);
    }
    for name in ["honest","swapped_pi_order","changed_n","changed_version","truncated_pi_list","extended_pi_list","wrong_digest","wrong_zeta","noncanonical_auxiliary","truncated_carrier","extended_carrier","changed_c_proof"] {
        let mut c=carrier.clone(); let mut s=statement.clone();
        match name {
            "swapped_pi_order"=>{let p=s[6..204].to_vec();s.copy_within(204..402,6);s[204..402].copy_from_slice(&p);},
            "changed_n"=>s[1]=3,
            "changed_version"=>s[5]^=1,
            "truncated_pi_list"=>{s.truncate(s.len()-198);},
            "extended_pi_list"=>{s.extend(pis[0]);},
            "wrong_digest"=>{let x=u32::from_le_bytes(c[32..36].try_into().unwrap());c[32..36].copy_from_slice(&((x+1)%F::ORDER_U32).to_le_bytes());},
            "wrong_zeta"=>{let x=u32::from_le_bytes(c[..4].try_into().unwrap());c[..4].copy_from_slice(&((x+1)%F::ORDER_U32).to_le_bytes());},
            "noncanonical_auxiliary"=>c[..4].copy_from_slice(&F::ORDER_U32.to_le_bytes()),
            "truncated_carrier"=>{c.pop();},
            "extended_carrier"=>c.push(0),
            "changed_c_proof"=>c[300]^=1,
            _=>{}
        }
        let t=Instant::now(); let result=a::verify(&c,&s,&a::TRUSTED_PARAMS);
        let expected=name=="honest";
        assert_eq!(result.is_ok(),expected,"{name}: {result:?}");
        rows.push(json!({"case":name,"accepted":result.is_ok(),"expected":if expected{"accept"}else{"reject"},"passed":true,"error":result.err().map(|e|e.to_string()),"layer":"complete native C verifier","ms":t.elapsed().as_secs_f64()*1000.}));
    }
    // Isolate the mandatory deterministic check: no replacement of the outer verification in production.
    let mut pv:Vec<F>=statement.iter().copied().map(F::from_u8).collect();
    pv.extend(carrier[..a::AUX_LEN].chunks_exact(4).map(|b|F::from_u32(u32::from_le_bytes(b.try_into().unwrap()))));
    assert!(a::check_periodic(&pv).is_ok());
    let z=EF::from_basis_coefficients_slice(&pv[a::BASE_LEN..a::BASE_LEN+8]).unwrap();
    let mut wrong_p=a::periodic(z).unwrap();wrong_p[0]+=EF::ONE;
    let wrong_d=a::advice_digest(&wrong_p);pv[a::BASE_LEN+8..a::BASE_LEN+16].copy_from_slice(&wrong_d);
    let rejected=a::check_periodic(&pv).is_err();assert!(rejected);
    rows.push(json!({"case":"wrong_periodic_advice_digest_mismatch","accepted":false,"passed":rejected,"layer":"native deterministic periodic recomputation, isolated from outer proof"}));
    let doc=json!({"rows":rows,"all_passed":true,"review":"loop-internal self-review; not independently reviewed"});
    std::fs::write(out.join("corpus.json"),serde_json::to_vec_pretty(&doc).unwrap()).unwrap();
    println!("{}",json!({"cases":doc["rows"].as_array().unwrap().len(),"all_passed":true}));
}
