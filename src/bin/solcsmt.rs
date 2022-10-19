use solcsmtr::smt_smtlib;

fn main() {
    smt_smtlib::handle_commands(&mut std::io::stdin(), &mut std::io::stdout());
}
