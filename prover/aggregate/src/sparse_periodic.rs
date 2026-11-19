//! Exact sparse barycentric evaluation of the fixed input F periodic table.
//! No prover-supplied table or interpolation cache is accepted.
use std::{collections::BTreeMap,sync::OnceLock};
use p3_field::{BasedVectorSpace,Field,PrimeCharacteristicRing,PrimeField32,TwoAdicField,batch_multiplicative_inverse};
use p3_koala_bear::KoalaBear as F;
use crate::{childpin,aggregate_native::VerifyError};
use childpin::key::EF;

#[derive(PartialEq,Eq)]
struct Column{base:F,delta:Vec<(usize,F)>}
struct Table{cols:Vec<Column>,mapping:Vec<usize>,points:Vec<F>,inv_n:F}
static TABLE:OnceLock<Result<Table,VerifyError>>=OnceLock::new();

fn table()->Result<&'static Table,VerifyError>{
    TABLE.get_or_init(||{
        let fk=childpin::key::verifier_key(&childpin::key::TRUSTED_PARAMS)
            .map_err(|_|VerifyError::LocalFault("input F key"))?;
        let n=1<<14;
        // The original verifier evaluates these full-length columns over the
        // unshifted base trace domain, never over the doubled hiding domain.
        if fk.air.periodic.len()!=162 || fk.air.periodic.iter().any(|c|c.len()!=n){
            return Err(VerifyError::LocalFault("input F periodic shape"));
        }
        let mut cols=vec![];let mut mapping=vec![];
        for col in &fk.air.periodic {
            let mut counts=BTreeMap::<u32,usize>::new();
            for v in col{*counts.entry(v.as_canonical_u32()).or_default()+=1;}
            let (&mode,_)=counts.iter().max_by_key(|(v,count)|(**count,**v)).unwrap();
            let base=F::from_u32(mode);
            let delta=col.iter().enumerate().filter_map(|(i,&v)|if v==base{None}else{Some((i,v-base))}).collect();
            let column=Column{base,delta};
            let id=if let Some(id)=cols.iter().position(|c|c==&column){id}else{let id=cols.len();cols.push(column);id};
            mapping.push(id);
        }
        let points=F::two_adic_generator(14).powers().take(n).collect();
        Ok(Table{cols,mapping,points,inv_n:F::from_usize(n).inverse()})
    }).as_ref().map_err(Clone::clone)
}

pub fn evaluate(z:EF)->Result<Vec<EF>,VerifyError>{
    let t=table()?;
    // Lagrange basis is a Kronecker delta on the domain. Avoid a zero inverse.
    let coeffs:&[F]=z.as_basis_coefficients_slice();
    if coeffs[1..].iter().all(|&x|x==F::ZERO){
        let base=coeffs[0];
        if let Some(i)=t.points.iter().position(|&x|x==base){
            let unique:Vec<EF>=t.cols.iter().map(|c|EF::from(c.base+c.delta.iter().find(|(r,_)|*r==i).map_or(F::ZERO,|(_,v)|*v))).collect();
            return Ok(t.mapping.iter().map(|&j|unique[j]).collect());
        }
    }
    let den:Vec<EF>=t.points.iter().map(|&x|z-x).collect();
    let mut weights=batch_multiplicative_inverse(&den);
    let factor=(z.exp_power_of_2(14)-EF::ONE)*t.inv_n;
    for(w,&x)in weights.iter_mut().zip(&t.points){*w*=factor*x;}
    // f(z) = mode + sum_{i: f_i != mode} (f_i-mode) L_i(z).
    // One set of weights serves all 162 columns; full-equal columns are evaluated once.
    let unique:Vec<EF>=t.cols.iter().map(|c|EF::from(c.base)+c.delta.iter().map(|&(i,v)|weights[i]*v).sum::<EF>()).collect();
    Ok(t.mapping.iter().map(|&j|unique[j]).collect())
}

pub fn stats()->Result<serde_json::Value,VerifyError>{
    let t=table()?;Ok(serde_json::json!({"columns":t.mapping.len(),"rows":t.points.len(),"unique_columns":t.cols.len(),
        "nontrivial_unique_columns":t.cols.iter().filter(|c|!c.delta.is_empty()).count(),
        "nonconstant_original_columns":t.mapping.iter().filter(|&&j|!t.cols[j].delta.is_empty()).count(),
        "original_columns_more_than_one_delta":t.mapping.iter().filter(|&&j|t.cols[j].delta.len()>1).count(),
        "unique_columns_more_than_one_delta":t.cols.iter().filter(|c|c.delta.len()>1).count(),
        "nondefault_entries":t.cols.iter().map(|c|c.delta.len()).sum::<usize>(),
        "barycentric_weight_sets_per_zeta":1,"key_cache":"existing pinned OnceLock","table_cache":"pinned OnceLock"}))
}

/// Differential check against the unmodified pinned library implementation.
pub fn differential()->Result<serde_json::Value,VerifyError>{
    use p3_air::BaseAir;
    use p3_commit::{Pcs,PeriodicColumns,PolynomialSpace};
    use p3_batch_stark_c3np::StarkGenericConfig;
    let pin=&childpin::key::TRUSTED_PARAMS;
    let fk=childpin::key::verifier_key(pin).map_err(|_|VerifyError::LocalFault("input F key"))?;
    let cfg=childpin::key::config(pin,&[]);
    let domain=<childpin::key::FHPcs as Pcs<EF,childpin::key::Challenger>>::natural_domain_for_degree(cfg.pcs(),1<<14);
    let cols=BaseAir::<F>::periodic_columns(&fk.air);
    let mut zs=vec![EF::ZERO];
    zs.extend([0,1,17,8191,16383].map(|i|EF::from(F::two_adic_generator(14).exp_u64(i))));
    for k in 1..=24{zs.push(EF::from_basis_coefficients_fn(|i|F::from_usize((k*53+i*71+1)*(k+i+3))));}
    for &z in &zs{
        let expected=domain.evaluate_periodic_columns_at(PeriodicColumns::new(&cols,1<<14).unwrap(),z);
        if evaluate(z)?!=expected{return Err(VerifyError::LocalFault("sparse periodic differential mismatch"));}
    }
    Ok(serde_json::json!({"all_equal":true,"points":zs.len(),"includes_trace_domain_points":5,
        "stats":stats()?,"review":"loop-internal self-review; not independently reviewed"}))
}
