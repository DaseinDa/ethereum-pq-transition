//! Option C aggregation. Child identity is pinned independently of the changed AG machine.
use std::path::Path;
use std::sync::Arc;
use p3_air::{BaseAir, symbolic::AirLayout};
use p3_challenger::CanObserve;
use p3_commit::{Pcs, PolynomialSpace};
use p3_field::{PrimeCharacteristicRing, Field};
use p3_koala_bear::KoalaBear as F;
use p3_lookup::LogUpGadget;
use p3_fri::{PcsShape, FriShape, fold_schedule};
use serde_json::json;
use crate::{EF, childpin, compiler, schedule, sha256_hex, hex};
use compiler::{Options, TableShape, TableConstraints};
use schedule::{ChildSpec, TableSpec, PrefixItem};

#[derive(Clone)]
struct Rec(Vec<F>);
impl CanObserve<F> for Rec { fn observe(&mut self, x: F) { self.0.push(x); } }

pub fn child_spec() -> ChildSpec {
    let pin = &childpin::key::TRUSTED_PARAMS;
    let vk = childpin::key::verifier_key(pin).expect("fixed F verifier key");
    let air = &vk.air;
    let lk = &vk.common.lookups[0];
    let (base, ext) = p3_batch_stark_c3np::symbolic::get_symbolic_constraints::<F, EF, _, _>(
        air, AirLayout::from_air(air), lk, &LogUpGadget::new());
    let cfg = childpin::key::config(pin, &vec![F::ZERO; 198]);
    use p3_batch_stark_c3np::StarkGenericConfig;
    let domain = <childpin::key::FHPcs as Pcs<EF, childpin::key::Challenger>>::natural_domain_for_degree(cfg.pcs(), 1 << 14);
    let lqd = p3_batch_stark_c3np::symbolic::get_log_num_quotient_chunks_for_domain::<F, EF, _, _>(
        air, AirLayout::from_air(air), domain, lk, 1, &LogUpGadget::new());
    let (buses, nbus, mw) = crate::fchild::bus_layout_lk(&vk.common.lookups);
    let shape = TableShape { name: "F".into(), log_trace: 14, log_ext: 15,
        width: BaseAir::<F>::width(air), num_public: 198, preprocessed_width: 0,
        perm_width: lk.len()+1, lookup_bus: buses[0].clone(), log_quotient_degree: lqd, chunks: 1 << (lqd+1) };
    let program = compiler::compile(&[shape.clone()], &[TableConstraints { base: &base, ext: &ext }], nbus, mw, Options::default());
    let program_sha256: [u8; 32] = <sha2::Sha256 as sha2::Digest>::digest(&program.file_bytes(&hex(pin.f_vk_digest()))).into();
    let batch = p3_batch_stark_c3np::BatchShape { trace_widths: vec![shape.width], public_value_counts: vec![198],
        preprocessed_widths: vec![0], has_preprocessed_commitment: false, num_lookup_instances: 1,
        lookup_pow_bits: 0, has_randomization_commitment: true, ood_pow_bits: 0, next_row_columns: vec![vk.opened.clone()] };
    let mut br = Rec(vec![]); batch.domain_separator::<F, EF>().seed(&mut br);
    let arities = fold_schedule(&[24], 17, 4);
    let table = TableSpec { name: "F".into(), log_trace: 14, width: shape.width, pre_width: 0,
        public: (0..198).collect(), next_main: vk.opened.main.clone(), next_pre: vec![], next_perm: vk.opened.permutation.clone(),
        perm_width: shape.perm_width, lookup_bus: buses[0].clone(), log_qd: lqd, chunks: shape.chunks };
    let draft = ChildSpec { name: "Pinned F for option C".into(), tables: vec![table], rc: 8, salt: 8,
        log_blowup: 9, log_final_poly_len: 8, max_log_arity: 4, num_queries: 29, index_bits: 24,
        fri_log_arities: arities.clone(), prefix: vec![PrefixItem::Bytes("F.domain".into(), pin.f_domain().as_bytes().to_vec()),
            PrefixItem::Bytes("F.key".into(), pin.f_vk_digest().to_vec()), PrefixItem::PubBytes("F.PI198".into(), 0, 198)],
        num_public: 198, seeds: [br.0, vec![], vec![]], child_vk: *pin.f_vk_digest(), pre_cap: vec![],
        num_buses: nbus, max_message_width: mw, program: Arc::new(program), program_sha256 };
    let trees = schedule::trees(&draft);
    let counts = trees.iter().filter(|t| matches!(t.kind, schedule::TreeKind::Input(_)))
        .map(|t| t.mats.iter().map(|m| m.points.iter().map(|_| m.width).collect()).collect()).collect();
    let mut pr = Rec(vec![]); PcsShape { claimed_evaluation_counts: counts, batch_pow_bits: 0 }.domain_separator::<F,EF>().seed(&mut pr);
    let perm = p3_koala_bear::default_koalabear_poseidon2_16();
    let fri = p3_fri::FriParameters { log_blowup: 9, log_final_poly_len: 8, max_log_arity: 4, num_queries: 29,
        batch_proof_of_work_bits: 0, commit_proof_of_work_bits: 0, query_proof_of_work_bits: 0,
        mmcs: crate::FChMmcs::new(crate::FMmcs::new(crate::Hash::new(perm.clone()), crate::Compress::new(perm), 0, crate::os_rng())) };
    let mut fr = Rec(vec![]); FriShape::with_schedule(&fri, arities, 24).domain_separator::<F,EF>().seed(&mut fr);
    ChildSpec { seeds: [draft.seeds[0].clone(), pr.0, fr.0], ..draft }
}

pub fn main() {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(String::as_str) {
        Some("prove") => crate::agprove::prove(Path::new(args.get(2).expect("output directory")),Path::new(args.get(3).expect("public input root"))),
        Some("outer-plan") => {
            let out = Path::new(args.get(2).expect("output directory"));
            std::fs::create_dir_all(out).unwrap();
            let mut spec = child_spec(); spec.num_public = 214;
            let single = schedule::Schedule::build(&spec);
            let (s,segment,stride) = crate::combine::schedule(single);
            println!("{}",json!({"phase":"AG keygen","segment_rows":segment,"address_stride":stride,"pre_width":s.air.pre.len()}));
            let (data,key)=crate::b2_keygen(&s);
            let vk=crate::b2_vk_digest(&s,&key);
            let crate::KData {common,prover_only}=data; drop(prover_only);
            let prefix=vec![crate::fschedule::PrefixItem::Bytes("AG.domain".into(),crate::B_DOMAIN.to_vec()),
                crate::fschedule::PrefixItem::Bytes("AG.key".into(),vk.to_vec()),
                crate::fschedule::PrefixItem::PubBytes("statement".into(),0,crate::combine::PV_COUNT)];
            let bc=crate::fchild::BChild { s,common,key,vk,vk_check:json!(null),statement:vec![F::ZERO;crate::combine::PV_COUNT],prefix,record:json!(null) };
            let cs=crate::fchild::b_spec(&bc);
            let outer=crate::fschedule::Schedule::build(&cs);
            let required=crate::fmodes::f_used_rows(&outer);
            let doc=json!({"tier":"compiled schedule with real AG preprocessed key; no aggregate proof",
                "ag_rows":bc.s.n,"segment_rows":segment,"ag_pre_width":bc.s.air.pre.len(),"ag_vk":hex(&vk),
                "outer_rows":outer.n,"outer_required_rows":required,"outer_instructions":outer.program.len(),
                "outer_periodic_columns":outer.air.periodic.len(),"fits_2_14":outer.n<=1<<14,"review":crate::REVIEW});
            std::fs::write(out.join("outer-plan.json"),serde_json::to_vec_pretty(&doc).unwrap()).unwrap(); println!("{doc}");
            std::fs::write(out.join("ag-key.json"),serde_json::to_vec_pretty(&crate::b2_vk_json(&bc.s,&bc.common,&bc.key,&vk)).unwrap()).unwrap();
            assert!(outer.n<=1<<14,"outer schedule exceeds the approved 2^14-row shape");
        }
        Some("schedule") | Some("trace") => {
            let out = Path::new(args.get(2).expect("output directory"));
            std::fs::create_dir_all(out).unwrap();
            let mut spec = child_spec(); spec.num_public = 214;
            let s = schedule::Schedule::build(&spec);
            let required = s.used_rows.max(s.instr_row.iter().max().unwrap()+1);
            let doc = json!({"tier":"compiled schedule; not a proof", "rows": s.n,"required_rows": required,
                "instructions":s.program.len(),"transcript_and_hash_rows":s.t_rows,"preprocessed_width":s.air.pre.len(),
                "main_width":crate::kernel::WIDTH,"periodic_advice_count":162,"review":crate::REVIEW});
            std::fs::write(out.join("schedule.json"),serde_json::to_vec_pretty(&doc).unwrap()).unwrap();
            println!("{doc}");
            if args[1] == "trace" {
                let input = Path::new(args.get(3).expect("owner directory"));
                let pi: [u8;198] = crate::unhex(std::fs::read_to_string(input.join("statement/pi198.hex")).unwrap().trim()).try_into().unwrap();
                let bytes = std::fs::read(input.join("f/proof.postcard")).unwrap();
                let tr = crate::awitness::honest(&s,&bytes,&pi);
                let matrix = tr.trace.finalize();
                let (n,fail,bus,messages) = crate::kernel::check(&s.air,&matrix,&tr.pv);
                let doc = json!({"native":tr.record,"constraints_per_row":n,"failures":fail.len(),
                    "first_failures":fail.iter().take(10).map(|f| json!([f.row,f.constraint,f.group])).collect::<Vec<_>>(),
                    "unbalanced_bus":bus.len(),"messages":messages,"rows":s.n,"review":crate::REVIEW});
                std::fs::write(out.join("trace.json"),serde_json::to_vec_pretty(&doc).unwrap()).unwrap();
                println!("{doc}"); assert!(fail.is_empty() && bus.is_empty());
            }
        }
        Some("compile") => {
            let out = Path::new(args.get(2).expect("output directory"));
            std::fs::create_dir_all(out).unwrap();
            let s = child_spec();
            let bytes = s.program.file_bytes(&hex(&s.child_vk));
            std::fs::write(out.join("f-program.json"), &bytes).unwrap();
            let periodic = s.program.inputs.iter().filter(|(_, x)| matches!(x, compiler::Input::Periodic(..))).count();
            let doc = json!({"review": crate::REVIEW, "tier": "compiled constraint program; no aggregate proof",
                "child_vk": hex(&s.child_vk), "instructions": s.program.instrs.len(), "periodic_inputs": periodic,
                "program_sha256": sha256_hex(&bytes), "stats": s.program.stats});
            std::fs::write(out.join("compile.json"), serde_json::to_vec_pretty(&doc).unwrap()).unwrap();
            println!("{}", json!({"instructions": s.program.instrs.len(), "periodic_inputs": periodic}));
        }
        _ => panic!("supported: compile OUTPUT (aggregate prover is being implemented)"),
    }
}
