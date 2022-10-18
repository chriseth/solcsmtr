use std::cmp::max;

use crate::cdcl::{Clause, Literal, Variable, CDCL};

pub fn solve_dimacs_file(input: &str) -> bool {
    let (vars, clauses) = parse_input(&input);
    let mut solver = CDCL::default();
    for i in 0..vars {
        solver.add_variable(format!("x{}", i + 1));
    }
    for clause in clauses {
        solver.add_clause(clause);
    }
    solver.solve()
}

fn parse_input(input: &str) -> (usize, Vec<Clause>) {
    let mut vars = 0;
    let clauses = input
        .split('\n')
        .flat_map(|line| {
            if line.is_empty() || line.starts_with('c') || line.starts_with('%') {
                None
            } else if line.starts_with('p') {
                assert!(line.starts_with("p cnf "));
                None
            } else {
                let mut clause = line
                    .split_whitespace()
                    .filter(|s| !s.is_empty())
                    .map(|e| e.parse::<i64>().unwrap())
                    .map(|lit| {
                        let var = lit.abs() as Variable;
                        vars = max(vars, var as usize);
                        if lit < 0 {
                            !Literal::from(var)
                        } else {
                            Literal::from(var)
                        }
                    })
                    .collect::<Vec<_>>();
                assert!(clause.last().unwrap().var() == 0);
                clause.pop();
                if clause.is_empty() {
                    None
                } else {
                    Some(clause)
                }
            }
        })
        .collect::<Vec<_>>();
    (vars, clauses)
}
