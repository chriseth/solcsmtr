use std::collections::HashMap;
use std::fmt::{self, Display};

use num_rational::BigRational;

use crate::cdcl::{TheorySolver, CDCL};
use crate::linear_expression::LinearExpression;
use crate::lp_solver::LPSolver;
use crate::sexpr_parser::SExpr;
use crate::smt_encoder::SMTEncoder;
use crate::types::*;
use crate::variable_pool::*;

#[derive(Default)]
pub struct SMTSolver {
    variables: VariablePool,
    /// Constraints of the form z = 2x + y
    linear_constraints: HashMap<VariableID, Vec<(VariableID, BigRational)>>,
    clauses: Vec<Clause>,
    /// Real variable and its upper bound for each theory predicate, if taken positively.
    bounds_for_theory_predicates: HashMap<VariableID, (VariableID, RationalWithDelta)>,
    fixed_bounds: HashMap<VariableID, Bounds>,
}

struct LPTheory<'a> {
    solver: LPSolver,
    pool: &'a VariablePool,
    bounds_for_theory_predicates: &'a HashMap<VariableID, (VariableID, RationalWithDelta)>,
    trail_size: usize,
    stored_bounds: Vec<(
        usize,
        VariableID,
        Bounds,
        (Option<Literal>, Option<Literal>),
    )>,
}
impl<'a> LPTheory<'a> {
    pub fn new(
        bounds_for_theory_predicates: &'a HashMap<VariableID, (VariableID, RationalWithDelta)>,
        pool: &'a VariablePool,
    ) -> LPTheory<'a> {
        LPTheory {
            solver: LPSolver::default(),
            pool,
            bounds_for_theory_predicates,
            trail_size: 0,
            stored_bounds: vec![],
        }
    }
}
impl TheorySolver for LPTheory<'_> {
    fn assign(&mut self, var: VariableID, value: bool) {
        if let Some((rational_var, upper_bound)) = self.bounds_for_theory_predicates.get(&var) {
            if let Some((old_bounds, old_reasons)) = if value {
                println!("Restricting {}", *rational_var);
                self.solver.restrict_bounds_with_reason(
                    *rational_var,
                    Bounds {
                        lower: None,
                        upper: Some(upper_bound.clone()),
                    },
                    (None, Some(!Literal::from(var))),
                )
            } else {
                println!("Restricting negated {}", *rational_var);
                println!("{} >= {}",self.pool.name(*rational_var), upper_bound.clone() - RationalWithDelta::delta());
                self.solver.restrict_bounds_with_reason(
                    *rational_var,
                    Bounds {
                        lower: Some(upper_bound.clone() + RationalWithDelta::delta()),
                        upper: None,
                    },
                    (Some(!Literal::from(var)), None),
                )
            } {
                self.stored_bounds
                    .push((self.trail_size, *rational_var, old_bounds, old_reasons));
            }
        }
    }

    fn set_trail_size(&mut self, trail_size: usize) {
        println!("CDCL sets assignment trail size to {trail_size}");
        if trail_size > self.trail_size {
            println!("-> increment");
            // TODO optimization: store "previous good values",
            // but there was also another (better) technique that re-computed them.
        } else if trail_size < self.trail_size {
            while let Some((stored_size, ..)) = self.stored_bounds.iter().last() {
                if *stored_size <= trail_size {
                    break;
                }
                let (_, var, bounds, reasons) = self.stored_bounds.pop().unwrap();
                println!("undoing {}", var);
                self.solver.set_bounds_with_reason(var, bounds, reasons)
            }
            println!(
                "Solver after resetting trail size:\n{}------------------",
                &self.solver.format(&self.pool)
            );
    
        }
        self.trail_size = trail_size;
    }

    fn solve(&mut self) -> Option<Clause> {
        println!(
            "CDCL asks us to run solver:\n{}------------------",
            &self.solver.format(&self.pool)
        );
        self.solver.feasible()
    }

    fn polarity_indication(&self, predicate: VariableID) -> Option<bool> {
        None //todo!()
    }
}

impl SMTSolver {
    pub fn new() -> SMTSolver {
        Default::default()
    }
    pub fn declare_variable(&mut self, name: VariableName, sort: Sort) -> Variable {
        self.variables.declare_variable(name, sort)
    }

    pub fn add_assertion(&mut self, assertion: &SExpr) {
        SMTEncoder::new(
            &mut self.variables,
            &mut self.linear_constraints,
            &mut self.clauses,
            &mut self.bounds_for_theory_predicates,
            &mut self.fixed_bounds,
        )
        .add_assertion(assertion);
    }
    pub fn push(&mut self) {
        todo!();
    }
    pub fn pop(&mut self) {
        todo!();
    }
    pub fn check(&mut self) -> Option<bool> {
        println!("============ check ================");
        // TODO we could keep the state of the lp solver for longer.
        let mut lp_theory = LPTheory::new(&self.bounds_for_theory_predicates, &self.variables);
        for (var, bounds) in &self.fixed_bounds {
            lp_theory.solver.restrict_bounds(*var, bounds.clone());
        }
        for (basic_var, linear_expr) in &self.linear_constraints {
            lp_theory
                .solver
                .append_row(*basic_var, linear_expr.iter().cloned());
        }
        println!("{}", lp_theory.solver.format(&self.variables));
        if lp_theory.solver.feasible().is_some() {
            return Some(false);
        }
        if self.bounds_for_theory_predicates.is_empty() && self.clauses.is_empty() {
            return Some(true);
        }

        let mut cdcl = CDCL::new(&self.variables, lp_theory);
        for clause in &self.clauses {
            cdcl.add_clause(clause.clone());
        }
        Some(cdcl.solve())
    }
}

impl Display for SMTSolver {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "SMT solver state:")?;
        writeln!(f, "Clauses:")?;
        for clause in &self.clauses {
            writeln!(f, "{}", format_clause(clause, &self.variables))?;
        }
        writeln!(f, "Linear equalities:")?;
        for (main_var, expr) in &self.linear_constraints {
            writeln!(
                f,
                "{} = {}",
                self.variables.name(*main_var),
                LinearExpression::format(expr.iter().map(|(v, f)| (self.variables.name(*v), f)))
            )?;
        }
        writeln!(f, "Fixed bounds:")?;
        for (var, bounds) in &self.fixed_bounds {
            writeln!(f, "{}", bounds.format(self.variables.name(*var)))?;
        }
        writeln!(f, "Theory predicate bounds:")?;
        for (predicate, (var, upper_bound)) in &self.bounds_for_theory_predicates {
            let formatted_bounds = Bounds {
                lower: None,
                upper: Some(upper_bound.clone()),
            }
            .format(self.variables.name(*var));
            writeln!(
                f,
                "{} <=> {formatted_bounds}",
                self.variables.name(*predicate)
            )?;
        }
        Ok(())
    }
}

impl SMTSolver {
    fn is_theory_predicate(&self, var: Variable) -> bool {
        assert!(var.sort == Sort::Bool);
        self.bounds_for_theory_predicates.contains_key(&var.id)
    }
}

#[cfg(test)]
mod test {
    use crate::sexpr_parser::parse_sexpr;

    use super::*;

    fn setup() -> SMTSolver {
        let mut s = SMTSolver::new();
        s.declare_variable("x".as_bytes().into(), Sort::Real);
        s.declare_variable("y".as_bytes().into(), Sort::Real);
        s.declare_variable("z".as_bytes().into(), Sort::Real);
        s.declare_variable("a".as_bytes().into(), Sort::Bool);
        s.declare_variable("b".as_bytes().into(), Sort::Bool);
        s.declare_variable("c".as_bytes().into(), Sort::Bool);
        s
    }

    #[test]
    fn simple_bounds() {
        let mut s = setup();
        s.add_assertion(&parse_sexpr(b"(= x 4)"));
        assert!(s.check() == Some(true));
        s.add_assertion(&parse_sexpr(b"(<= x 2)"));
        assert!(s.check() == Some(false));
    }

    #[test]
    fn simple_arithmetics() {
        let mut s = setup();
        s.add_assertion(&parse_sexpr(b"(= (+ x y) 4)"));
        assert!(s.check() == Some(true));
        s.add_assertion(&parse_sexpr(b"(<= x 2)"));
        assert!(s.check() == Some(true));
        s.add_assertion(&parse_sexpr(b"(<= 2 y)"));
        assert!(s.check() == Some(false));
    }
    #[test]
    fn more_arithmetics() {
        let mut s = setup();
        s.add_assertion(&parse_sexpr(b"(= (- x (* 2 y)) 4)"));
        assert!(s.check() == Some(true));
        s.add_assertion(&parse_sexpr(b"(<= x 2)"));
        assert!(s.check() == Some(true));
        s.add_assertion(&parse_sexpr(b"(<= 1 y)"));
        println!("{}", s);
        assert!(s.check() == Some(false));
    }
    #[test]
    fn only_boolean() {
        let mut s = setup();
        s.add_assertion(&parse_sexpr(b"(or (not a) b)"));
        assert!(s.check() == Some(true));
        s.add_assertion(&parse_sexpr(b"(not b)"));
        assert!(s.check() == Some(true));
        s.add_assertion(&parse_sexpr(b"(a)"));
        println!("{}", s);
        assert!(s.check() == Some(false));
    }
    #[test]
    fn simple_mixed() {
        let mut s = setup();
        s.add_assertion(&parse_sexpr(b"(or (<= x 7) (> y 2))"));
        assert!(s.check() == Some(true));
        s.add_assertion(&parse_sexpr(b"(= x 8)"));
        assert!(s.check() == Some(true));
        s.add_assertion(&parse_sexpr(b"(= y 2)"));
        println!("{}", s);
        assert!(s.check() == Some(false));
    }
}
