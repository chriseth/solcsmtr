use std::io::{Read, Write};

use crate::{
    sexpr_parser,
    smt_solver::{self, SMTSolver},
};

pub fn handle_commands(input: &mut impl Read, output: &mut impl Write) {
    let mut solver = SMTSolver::new();

    loop {
        let mut buf = Vec::new();
        input.read_to_end(&mut buf).unwrap();
        //println!("Read: {}", std::str::from_utf8(&buf).unwrap());

        let mut p = 0;
        loop {
            while p < buf.len() && matches!(buf[p], b' ' | b'\r' | b'\n') {
                p += 1
            }
            if p >= buf.len() {
                break;
            }

            let (command, rest) = sexpr_parser::parse_sexpr_slice(&buf, p);
            let parts = command.as_subexpr();
            //println!("{}", command);
            match parts[0].as_symbol() {
                b"set-info" => {}
                b"set-option" => {}
                b"declare-fun" => {
                    assert!(parts.len() == 4);
                    let name = parts[1].as_symbol();
                    assert!(parts[2].as_subexpr().is_empty());
                    let sort = match parts[3].as_symbol() {
                        b"Real" => smt_solver::Sort::Real,
                        b"Bool" => smt_solver::Sort::Bool,
                        _ => panic!("Invalid variable sort: {}", parts[3]),
                    };
                    solver.declare_variable(name.into(), sort);
                }
                //b"define-fun" => {}
                b"assert" => solver.add_assertion(&parts[1]),
                b"push" => solver.push(),
                b"pop" => solver.pop(),
                b"set-logic" => {}
                b"check-sat" => match solver.check() {
                    Some(true) => writeln!(output, "sat").unwrap(),
                    Some(false) => writeln!(output, "unsat").unwrap(),
                    None => writeln!(output, "unknown").unwrap(),
                },
                b"exit" => return,
                _ => panic!("Unknown command: {}", command),
            }
            p = rest;
        }
    }
}
