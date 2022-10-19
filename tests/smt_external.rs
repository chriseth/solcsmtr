use std::{fs, io::BufWriter, path::Path};

use solcsmtr::smt_smtlib::handle_commands;

#[test]
#[ignore]
fn smt_external_tests() {
    let base_path = Path::new(&std::env::var("SOLCSMTR_BENCHMARKS").unwrap()).join("smt");
    let mut tests_run = 0;
    for subdir in ["sat", "unsat"] {
        for file in fs::read_dir(base_path.join(subdir)).unwrap() {
            let path = &file.unwrap().path();
            println!("{}", path.to_string_lossy());
            let mut input = fs::File::open(path).unwrap();
            let mut output = BufWriter::new(Vec::new());
            handle_commands(&mut input, &mut output);
            assert_eq!(std::str::from_utf8(output.buffer()).unwrap(), subdir);
            tests_run += 1;
        }
    }
    assert_eq!(tests_run, 1);
}
