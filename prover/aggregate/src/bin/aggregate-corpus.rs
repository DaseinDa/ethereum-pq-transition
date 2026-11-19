fn main(){
    let a:Vec<String>=std::env::args().collect();
    assert_eq!(a.len(),4,"aggregate-corpus INPUTS PROOF_DIR OUTPUT");
    pq_migrate_tree::corpus::run(std::path::Path::new(&a[1]),std::path::Path::new(&a[2]),std::path::Path::new(&a[3]));
}
