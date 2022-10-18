use std::io::Read;

use solcsmtr::cdcl_dimacs::solve_dimacs_file;

fn main() {
    let mut input = String::new();
    if let Some(f) = std::env::args().nth(1) {
        input = std::fs::read_to_string(f).unwrap();
    } else {
        println!("c waiting for data on standard input");
        std::io::stdin().read_to_string(&mut input).unwrap();
    }
    if solve_dimacs_file(&input) {
        println!("s SATISFIABLE");
    } else {
        println!("s UNSATISFIABLE");
    }
}
