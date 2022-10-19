use std::{fs, path::Path};

use solcsmtr::cdcl_dimacs::solve_dimacs_file;

#[test]
#[ignore]
fn cdcl_external_tests() {
    let base_path = Path::new(&std::env::var("SOLCSMTR_BENCHMARKS").unwrap()).join("cdcl");
    let mut tests_run = 0;
    for (result, subdir) in [(true, "sat"), (false, "unsat")] {
        for file in fs::read_dir(base_path.join(subdir)).unwrap() {
            let path = &file.unwrap().path();
            println!("{}", path.to_string_lossy());
            let input = fs::read_to_string(path).unwrap();
            assert_eq!(solve_dimacs_file(&input), result);
            tests_run += 1;
        }
    }
    assert_eq!(tests_run, 2004);
}
