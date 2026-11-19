//! Serial, public-vector construction of AG and C. Every honest base and LogUp constraint is checked.
use std::{path::Path, time::Instant};
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_koala_bear::KoalaBear as F;
use serde_json::{json, Value};
use crate::{agg, awitness, combine, schedule, hex, sha256_hex, save, ms};

fn report(out: &Path, name: &str, value: &Value) {
    save(&out.join(name), &serde_json::to_vec_pretty(value).unwrap());
    println!("{}",json!({"file":name,"result":value}));
}

pub fn prove(out: &Path, inputs: &Path) {
    let tail:Vec<String>=std::env::args().skip(4).collect();
    let keep_inner=tail==["--keep-inner","--public-test-data"];
    assert!(tail.is_empty()||keep_inner,"inner exports require --keep-inner --public-test-data");
    std::fs::create_dir(out).expect("fresh public-vector output directory required");
    let begin=Instant::now();
    let mut spec=agg::child_spec(); spec.num_public=214;
    let single=schedule::Schedule::build(&spec);
    let mut children=Vec::new();
    let mut base=combine::HEADER.to_vec();
    for owner in 0..combine::N {
        let dir=inputs.join(owner.to_string());
        let pi: [u8;198]=crate::unhex(std::fs::read_to_string(dir.join("statement/pi198.hex")).unwrap().trim()).try_into().unwrap();
        let bytes=std::fs::read(dir.join("f/proof.postcard")).unwrap();
        let t=Instant::now();
        let tr=awitness::honest(&single,&bytes,&pi);
        report(out,&format!("child-{owner}.json"),&json!({"native":tr.record,"proof_bytes":bytes.len(),"sha256":sha256_hex(&bytes),"trace_ms":ms(t)}));
        base.extend(pi); children.push(tr);
    }
    // Four distinct test accounts, as requested. AG receives only F proofs/PIs, never a seed.
    let owners: std::collections::BTreeSet<_> = base[6..].chunks_exact(198).map(|pi|pi[64..84].to_vec()).collect();
    assert_eq!(owners.len(),4);
    let (s,used,stride)=combine::schedule(single);
    let (trace,pv)=combine::trace(&children,used,stride); drop(children);
    let (nc,fail,bus,messages)=crate::kernel::check(&s.air,&trace,&pv);
    report(out,"ag-base-check.json",&json!({"rows":s.n,"pre_width":s.air.pre.len(),"constraints_per_row":nc,"failures":fail.len(),"unbalanced_bus":bus.len(),"messages":messages,
        "first_failures":fail.iter().take(12).map(|f|json!([f.row,f.constraint,f.group])).collect::<Vec<_>>(),"review":crate::REVIEW}));
    assert!(fail.is_empty()&&bus.is_empty(),"AG honest trace must satisfy every base constraint and exact memory bus");
    if std::env::var_os("PQ_AG_TRACE_ONLY").is_some(){
        trace_negatives(out,&s,&trace,&pv,used); metadata(out,&s);return;
    }
    let t=Instant::now();
    let (data,key)=crate::b2_keygen(&s); let keygen_ms=ms(t);
    let vk=crate::b2_vk_digest(&s,&key);
    let layout=p3_air::symbolic::AirLayout::from_air(&s.air);
    let gadget=p3_lookup::LogUpGadget::new();
    let lk=&data.common.lookups[0];
    let (bcnt,ecnt)=p3_batch_stark_c3::symbolic::get_symbolic_constraints::<F,crate::EF,_,_>(&s.air,layout,lk,&gadget);
    let degree=p3_batch_stark_c3::symbolic::get_max_constraint_degree::<F,crate::EF,_,_>(&s.air,layout,s.n,lk,&gadget);
    let lqd=p3_batch_stark_c3::symbolic::get_log_num_quotient_chunks::<F,crate::EF,_,_>(&s.air,layout,s.n,lk,1,&gadget);
    report(out,"ag-shape.json",&json!({"rows":s.n,"log_n":s.log_n,"main_width":crate::kernel::WIDTH,"pre_width":s.air.pre.len(),
        "base_constraints":bcnt.len(),"extension_constraints":ecnt.len(),"max_degree":degree,"quotient_chunks":1usize<<(lqd+1),
        "lookups":crate::b2_vk_json(&s,&data.common,&key,&vk)["lookups"],"perm_ef":lk.len()+1}));
    let lc=crate::lcheck::check(&s.air,&trace,&pv,&data.common.lookups[0],0x41474743);
    report(out,"ag-logup-check.json",&lc);
    assert_eq!(lc["all_zero"],json!(true)); assert_eq!(lc["terminal_is_zero"],json!(true));
    report(out,"ag-key.json",&crate::b2_vk_json(&s,&data.common,&key,&vk));
    let t=Instant::now();
    let ag=crate::prove_kernel(&crate::b2_config(&vk,&pv),&s,&data,&trace,&pv);
    let prove_ms=ms(t); drop(trace);
    let (ok,error,verify_ms)=crate::verify_kernel(&s,&vk,&data.common,&ag,&pv);
    assert!(ok,"AG proof: {error:?}");
    let bytes=postcard::to_allocvec(&ag).unwrap(); drop(ag);
    if keep_inner { save(&out.join("ag.postcard"),&bytes); }
    report(out,"ag-proof.json",&json!({"tier":"real-backend public-vector; n=1", "hiding":"HidingFriPcs, 8 random codewords and 8 salt fields; no composition upgrade claimed",
        "accepted":ok,"rows":s.n,"pre_width":s.air.pre.len(),"public_fields":pv.len(),"proof_bytes":bytes.len(),"proof_sha256":sha256_hex(&bytes),
        "keygen_ms":keygen_ms,"prove_ms":prove_ms,"verify_ms":verify_ms,"vk":hex(&vk),"parameters":crate::b2_params(),"inner_proof_exported":keep_inner,"review":crate::REVIEW}));
    let crate::KData{common,prover_only}=data; drop(prover_only);
    let prefix=vec![crate::fschedule::PrefixItem::Bytes("AG.domain".into(),crate::B_DOMAIN.to_vec()),
        crate::fschedule::PrefixItem::Bytes("AG.key".into(),vk.to_vec()),
        crate::fschedule::PrefixItem::PubBytes("statement".into(),0,pv.len())];
    let bc=crate::fchild::BChild{s,common,key,vk,vk_check:json!({"all_equal":true}),statement:pv.clone(),prefix,record:json!({"kind":"AG", "N":4})};
    let cs=crate::fchild::b_spec(&bc);
    let outer=crate::fschedule::Schedule::build(&cs);
    report(out,"c-plan.json",&json!({"rows":outer.n,"required_rows":crate::fmodes::f_used_rows(&outer),"hash_rows":outer.used_rows,"transcript_rows":outer.t_rows,"query_rows":outer.block_rows,"instructions":outer.program.len()}));
    assert_eq!(outer.n,1<<14,"C must retain the approved 2^14 rows");
    let (common,next,rule,cvk)=crate::fmodes::f_identity(&outer);
    report(out,"c-key.json",&crate::fmodes::f_vk_json(&outer,&common,&next,&cvk));
    report(out,"c-shape.json",&crate::fmodes::f_shape_doc(&outer,&bc,&common,&next,&rule,&cvk));
    let (cd,replay)=crate::fchild::replay_b(&bc,&outer,&bytes,&pv,"accepted");
    let (kt,_,honest)=crate::ftracegen::honest(&outer,&cd);
    let trace=kt.finalize(); drop(kt);
    let (nc,check,names,_)=crate::fmodes::fcheck_report(&outer,&trace,&pv);
    report(out,"c-base-check.json",&json!({"constraints_per_row":nc,"check":check,"names":names,"replay":replay,"honest":honest}));
    assert!(names.is_empty(),"C honest constraints");
    let lc=crate::flcheck::check(&outer.air,&trace,&pv,&common.lookups[0],0x43474741);
    report(out,"c-logup-check.json",&lc);
    assert_eq!(lc["all_zero"],json!(true)); assert_eq!(lc["terminal_is_zero"],json!(true));
    // Export a local key artifact. It becomes trusted only after its full hashes are pinned in the native crate.
    let material=json!({"schema":"pq-aggregate-verifier/key/v1","air":crate::material::air_to_json(&outer.air),
        "next":crate::material::next_rows_to_json(&next.1),"vk":hex(&cvk),"ag_vk":hex(&vk),"child_f_vk":hex(&cs.child_vk),
        "input_f_vk":hex(childpin_digest()),"params":crate::fmodes::f_params(),"domain":String::from_utf8_lossy(crate::fmodes::F_DOMAIN)});
    report(out,"c-material.json",&material);
    save(&out.join("c-periodic.rle"),&crate::material::encode_periodic(&outer.air.periodic));
    drop(cd); drop(bc); drop(cs); drop(bytes);
    let data=crate::fmodes::f_data(&outer);
    let cfg=crate::fmodes::f_config(&cvk,&pv);
    let airs=[outer.air.clone()]; let traces=[&trace];
    let instances=p3_batch_stark_c3np::StarkInstance::new_multiple(&airs,&traces,&[pv.clone()]);
    let t=Instant::now();
    let proof=p3_batch_stark_c3np::prove_batch_with_next_row_columns(&cfg,&instances,&data,&[next.1.clone()]).expect("C prover");
    let prove_ms=ms(t); drop(instances); drop(data);
    let (ok,error,verify_ms)=crate::fprove::verify_f(&outer,&cvk,&common,&next.1,&proof,&pv);
    assert!(ok,"C proof: {error:?}");
    let encoded=postcard::to_allocvec(&proof).unwrap();
    let (bd,errors)=crate::fbreakdown::report(&encoded,&proof,&crate::fbreakdown::FShape::of(&outer,&next.1,&common));
    assert!(errors.is_empty()); report(out,"c-breakdown.json",&bd);
    let aux:Vec<u8>=pv[6+198*4..].iter().flat_map(|v|v.as_canonical_u32().to_le_bytes()).collect();
    assert_eq!(aux.len(),64*4);
    let mut carrier=aux; carrier.extend(&encoded);
    assert!(carrier.len()<=196608,"C plus auxiliary data exceeds carrier budget");
    save(&out.join("c.postcard"),&encoded); save(&out.join("carrier.bin"),&carrier); save(&out.join("statement.bin"),&base);
    report(out,"c-proof.json",&json!({"tier":"real-backend public-vector; n=1","accepted":ok,"rows":outer.n,"required_rows":crate::fmodes::f_used_rows(&outer),
        "proof_bytes":encoded.len(),"auxiliary_bytes":256,"carrier_bytes":carrier.len(),"carrier_sha256":sha256_hex(&carrier),"statement_sha256":sha256_hex(&base),
        "prove_ms":prove_ms,"verify_ms":verify_ms,"total_ms":ms(begin),"peak_rss_kib":crate::peak_rss_kib(),"vk":hex(&cvk),"parameters":crate::fmodes::f_params(),"review":crate::REVIEW}));
}
fn childpin_digest()-> &'static [u8;32] { crate::childpin::key::TRUSTED_PARAMS.f_vk_digest() }

fn trace_negatives(out:&Path,s:&schedule::Schedule,trace:&p3_matrix::dense::RowMajorMatrix<F>,pv:&[F],used:usize){
    use crate::kernel as k;
    let mut rows=vec![];
    for case in ["owner2_nonzero_sponge_iv","merkle_leaf_link","merkle_direction_bit","child_deep_challenge_changed_mid_segment","other_child_deep_challenge",
        "changed_transcript_zeta_public","changed_periodic_digest_public","swapped_owner_pi","periodic_advice_input"] {
        let mut m=trace.clone();let mut v=pv.to_vec();let mut rehash=None;
        let row=match case {
            "owner2_nonzero_sponge_iv"=>{let r=used;m.values[r*k::WIDTH+k::IN+8]+=F::ONE;rehash=Some(r);r},
            "merkle_leaf_link"=>{let r=s.air.pre[s.air.pidx.start].iter().position(|&f|f==F::ONE).unwrap();m.values[r*k::WIDTH+k::IN]+=F::ONE;rehash=Some(r);r},
            "merkle_direction_bit"=>{let r=(0..s.n).find(|&r|s.air.pre[s.air.pidx.cons][r]==F::ONE&&s.air.pre[s.air.pidx.lnk][r]==F::ONE).unwrap();m.values[r*k::WIDTH+k::BIT]=F::ONE-m.values[r*k::WIDTH+k::BIT];r},
            "child_deep_challenge_changed_mid_segment"=>{let r=3*used+100;m.values[r*k::WIDTH+k::PW]+=F::ONE;r},
            "other_child_deep_challenge"=>{let wrong=m.values[k::PW..k::PW+32].to_vec();for r in used..2*used{m.values[r*k::WIDTH+k::PW..r*k::WIDTH+k::PW+32].copy_from_slice(&wrong);}used},
            "changed_transcript_zeta_public"=>{v[combine::global_public(2,198)]+=F::ONE;0},
            "changed_periodic_digest_public"=>{v[combine::global_public(2,206)]+=F::ONE;0},
            "swapped_owner_pi"=>{for i in 0..198{v.swap(combine::global_public(0,i),combine::global_public(1,i));}0},
            "periodic_advice_input"=>{let r=s.t_rows-162;m.values[r*k::WIDTH+k::IN]+=F::ONE;rehash=Some(r);r},
            _=>unreachable!()
        };
        if let Some(r)=rehash {
            let input: [F;16]=m.values[r*k::WIDTH+k::IN..r*k::WIDTH+k::IN+16].try_into().unwrap();
            let p=p3_poseidon2_air::generate_trace_rows::<F,p3_koala_bear::GenericPoseidon2LinearLayersKoalaBear,16,3,0,4,20>(vec![input],&k::constants(),0);
            m.values[r*k::WIDTH..r*k::WIDTH+k::P2W].copy_from_slice(&p.values);
        }
        let (_,fail,bus,_)=k::check(&s.air,&m,&v);
        let groups:std::collections::BTreeSet<_>=fail.iter().map(|f|f.group).collect();
        assert!(!fail.is_empty()||!bus.is_empty(),"{case} survived all constraints");
        rows.push(json!({"case":case,"row":row,"failures":fail.len(),"unbalanced_bus":bus.len(),"groups":groups,"rejected":true}));
    }
    report(out,"ag-constraint-corpus.json",&json!({"tier":"full AG honest trace with adversarial witness/public-value mutations; no invalid aggregate proof generated","cases":rows,"all_rejected":true,"review":crate::REVIEW}));
}

fn metadata(out:&Path,s:&schedule::Schedule){
    use p3_commit::{Pcs,PolynomialSpace};
    use p3_batch_stark_c3::StarkGenericConfig;
    use p3_lookup::{LogUpGadget,Lookups};
    use p3_air::symbolic::AirLayout;
    use p3_batch_stark_c3::symbolic as sym;
    let cfg=crate::b2_config(&[0;32],&[]);
    let domain=<crate::HPcs as Pcs<crate::EF,crate::Challenger>>::natural_domain_for_degree(cfg.pcs(),s.n);
    let g=LogUpGadget::new(); let layout=AirLayout::from_air(&s.air);
    let unpacked=Lookups::<F>::from_air::<crate::EF,_>(&s.air);
    let log=sym::get_log_num_quotient_chunks_for_domain::<F,crate::EF,_,_>(&s.air,layout,domain,&unpacked,1,&g);
    let packed=unpacked.pack_same_bus_with_degree(1<<log,|l|g.constraint_degree_with_transition(l,domain.transition_degree_multiple()));
    let (b,e)=sym::get_symbolic_constraints::<F,crate::EF,_,_>(&s.air,layout,&packed,&g);
    let degree=sym::get_max_constraint_degree::<F,crate::EF,_,_>(&s.air,layout,s.n,&packed,&g);
    let lookups:Vec<_>=packed.iter().map(|l|json!({"column":l.column,"tuple_width":l.elements.first().map(Vec::len),"tuples":l.elements.len(),"count_weight":l.count_weight})).collect();
    report(out,"ag-shape.json",&json!({"rows":s.n,"log_n":s.log_n,"main_width":crate::kernel::WIDTH,"pre_width":s.air.pre.len(),
        "base_constraints":b.len(),"extension_constraints":e.len(),"max_degree":degree,"quotient_chunks":1usize<<(log+1),"lookups":lookups,"perm_ef":packed.len()+1}));
}
