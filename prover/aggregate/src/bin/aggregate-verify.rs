use std::{path::Path, time::Instant};
use pq_migrate_tree::{verify,TRUSTED_PARAMS};
fn main(){
    let a:Vec<String>=std::env::args().collect();
    assert!(a.len()>=3,"aggregate-verify CARRIER STATEMENT [N]");
    let p=std::fs::read(Path::new(&a[1])).unwrap();
    let s=std::fs::read(Path::new(&a[2])).unwrap();
    let n:usize=a.get(3).map(|s|s.parse().unwrap()).unwrap_or(1);
    let t=Instant::now(); let warm=verify(&p,&s,&TRUSTED_PARAMS);
    let cold=t.elapsed().as_secs_f64()*1000.;
    if let Err(e)=warm {println!("{}",serde_json::json!({"accepted":false,"error":e.to_string(),"cold_ms":cold}));std::process::exit(1);}
    let mut samples=vec![];
    for _ in 0..n {let t=Instant::now();verify(&p,&s,&TRUSTED_PARAMS).expect("repeat");samples.push(t.elapsed().as_secs_f64()*1000.);}
    println!("{}",serde_json::json!({"accepted":true,"cold_ms":cold,"samples_ms":samples,"n":n,"tier":"real-backend internal verification","review":"loop-internal self-review; not independently reviewed"}));
}
