use solcsmtr::smt_smtlib;

fn main() {
    if let Some(f) = std::env::args().nth(1) {
        let mut input = std::fs::File::open(f).unwrap();
        smt_smtlib::handle_commands(&mut input, &mut std::io::stdout());
    } else {
        smt_smtlib::handle_commands(&mut std::io::stdin(), &mut std::io::stdout());
    }
}
