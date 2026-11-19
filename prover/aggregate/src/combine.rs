//! Four child programs share one AIR, with disjoint memory addresses and DEEP segments.
use std::collections::HashMap;
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_koala_bear::KoalaBear as F;
use p3_matrix::dense::RowMajorMatrix;
use crate::{kernel, schedule, tracegen, awitness};

pub const N: usize = 4;
pub const HEADER: [u8;6] = [0,4,0x80,0,0,8];
pub const PV_COUNT: usize = 6+198*N+16*N;

pub fn global_public(child: usize, local: usize) -> usize {
    if local < 198 { 6+198*child+local } else { 6+198*N+16*child+local-198 }
}

pub fn schedule(mut s: schedule::Schedule) -> (schedule::Schedule, usize, usize) {
    let used = s.used_rows.max(s.instr_row.iter().max().unwrap()+1)+1;
    assert!(used*N <= 1<<16, "four complete F programs do not fit AG at 2^16 rows");
    let stride = s.addr.values().copied().max().unwrap()+1;
    let mut air = s.air.clone();
    air.log_n=16; air.num_public=PV_COUNT;
    air.pre_names.clear(); air.pre.clear();
    air.pub_terms=vec![vec![];8]; air.output_terms=vec![vec![];8];
    let mut names = HashMap::new();
    for child in 0..N {
        let mut mapped=vec![];
        for (j,name) in s.air.pre_names.iter().enumerate() {
            let n = if name.starts_with("public_") {format!("{name}.owner{child}")} else {name.clone()};
            let idx = *names.entry(n.clone()).or_insert_with(|| { let ix=air.pre.len();
                air.pre_names.push(n); air.pre.push(vec![F::ZERO;1<<16]); ix });
            mapped.push(idx);
            let is_addr = kernel::CTRL_NAMES.iter().enumerate().any(|(slot,nm)| nm.starts_with("addr_") && s.air.pidx.ctrl[slot]==j);
            for row in 0..used {
                let mut v=s.air.pre[j][row];
                if is_addr && v!=F::ZERO {v+=F::from_u32(stride*child as u32);}
                air.pre[idx][child*used+row]=v;
            }
        }
        for lane in 0..8 {
            for &(sel,pv) in &s.air.pub_terms[lane] { air.pub_terms[lane].push((mapped[sel],global_public(child,pv))); }
            for &(sel,pv) in &s.air.output_terms[lane] { air.output_terms[lane].push((mapped[sel],global_public(child,pv))); }
        }
        if child+1<N {air.pre[s.air.pidx.segment_end][(child+1)*used-1]=F::ONE;}
    }
    // Common control columns retain their first child's positions. Public selectors can only append columns.
    for j in s.air.pidx.ctrl.iter().chain([&s.air.pidx.segment_start,&s.air.pidx.segment_end]) {
        assert_eq!(air.pre_names[*j],s.air.pre_names[*j]);
    }
    // Equal *fixed* columns need only one opening. This is exact vector equality,
    // not a probabilistic fingerprint or a removed constraint. All AIR references
    // are remapped, and the resulting table is committed by AG's key.
    let old=std::mem::take(&mut air.pre);
    let old_names=std::mem::take(&mut air.pre_names);
    let mut remap=vec![];
    for (name,col) in old_names.into_iter().zip(old) {
        let j=if let Some(j)=air.pre.iter().position(|v|v==&col){j}else{
            let j=air.pre.len();air.pre.push(col);air.pre_names.push(name);j
        };remap.push(j);
    }
    let p=&mut air.pidx;
    macro_rules! scalar {($($x:ident),*)=>{$(p.$x=remap[p.$x];)*}}
    macro_rules! array {($($x:ident),*)=>{$(for v in &mut p.$x{*v=remap[*v];})*}}
    scalar!(segment_end,segment_start,kc,tag,ivf,lnk,cons,path_t,start,pend,pend_canon,xs,x0,xp,xc,vs,xce,vacc,vsig,kappa,kx,dv,dc,dp,dw,inj,capr,capw,hiw);
    array!(cf,cv,kr,lsel,op,unp,ctrl,dl,cs,bind);
    for lane in air.pub_terms.iter_mut().chain(&mut air.output_terms){for (sel,_) in lane{*sel=remap[*sel];}}
    s.air=air; s.n=1<<16; s.log_n=16; s.num_public=PV_COUNT;
    (s,used,stride as usize)
}

pub fn trace(children: &[awitness::TraceResult], used: usize, stride: usize) -> (RowMajorMatrix<F>,Vec<F>) {
    assert_eq!(children.len(),N);
    let width=kernel::WIDTH;
    let mut matrix=RowMajorMatrix::new(vec![F::ZERO;(1<<16)*width],width);
    let mut pv=vec![F::ZERO;PV_COUNT];
    for (i,&b) in HEADER.iter().enumerate(){pv[i]=F::from_u8(b);}
    for (child,tr) in children.iter().enumerate() {
        assert_eq!(tr.pv.len(),214);
        for (i,&v) in tr.pv.iter().enumerate(){pv[global_public(child,i)]=v;}
        let cm=tr.trace.finalize();
        matrix.values[child*used*width..(child+1)*used*width].copy_from_slice(&cm.values[..used*width]);
        for r in child*used..(child+1)*used {
            let aa=&mut matrix.values[r*width+kernel::AA];
            if *aa!=F::ZERO{*aa+=F::from_usize(stride*child);}
        }
    }
    // Padding has a real zero-input Poseidon2 permutation, and keeps the final child's DEEP challenge.
    let padding=tracegen::KTrace::new(((1usize<<16)-N*used).next_power_of_two()).inp;
    let constants=kernel::constants();
    let pad=p3_poseidon2_air::generate_trace_rows::<F,p3_koala_bear::GenericPoseidon2LinearLayersKoalaBear,16,3,0,4,20>(padding,&constants,0);
    let pw: Vec<F> = matrix.values[(N*used-1)*width+kernel::PW..(N*used-1)*width+kernel::PW+32].to_vec();
    for r in N*used..1<<16 {
        let row=&mut matrix.values[r*width..(r+1)*width];
        row[..kernel::P2W].copy_from_slice(&pad.values[(r-N*used)*kernel::P2W..(r-N*used+1)*kernel::P2W]);
        row[kernel::PW..kernel::PW+32].copy_from_slice(&pw);
    }
    (matrix,pv)
}
