use std::{fs::File, io::Read};

use solcsmtr::sexpr_parser;

fn main() {
    handle_commands(&mut std::io::stdin());
}

fn handle_commands(input: &mut impl Read) {
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
            let command_parts = command.as_subexpr();
            println!("{}", command_parts[0]);
            match command_parts[0].as_symbol() {
                b"set-info" => {}
                b"set-option" => {}
                b"declare-fun" => {}
                b"define-fun" => {}
                b"assert" => {}
                b"push" => {}
                b"pop" => {}
                b"set-logic" => {}
                b"check-sat" => {}
                b"exit" => return,
                _ => panic!("Unknown command: {}", command),
            }
            p = rest;
        }
    }
}
