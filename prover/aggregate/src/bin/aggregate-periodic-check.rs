fn main(){
    let report=pq_migrate_tree::sparse_periodic::differential().expect("sparse interpolation equivalence");
    println!("{}",serde_json::to_string_pretty(&report).unwrap());
}
