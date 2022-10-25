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
    bounds_for_theory_predicates: &'a HashMap<VariableID, (VariableID, RationalWithDelta)>,
}
impl<'a> LPTheory<'a> {
    pub fn new(
        bounds_for_theory_predicates: &HashMap<VariableID, (VariableID, RationalWithDelta)>,
    ) -> LPTheory {
        LPTheory {
            solver: LPSolver::default(),
            bounds_for_theory_predicates,
        }
    }
}
impl TheorySolver for LPTheory<'_> {
    fn assign(&mut self, var: VariableID, value: bool) {
        //todo!()
    }

    fn set_decision_level(&mut self, level: usize) {

        //todo!()
    }

    fn solve(&mut self) -> Option<Clause> {
        None
//        todo!()
    }

    fn polarity_indication(&self, predicate: VariableID) -> Option<bool> {
        None//todo!()
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
        // TODO we could keep the state of the lp solver for longer.
        let mut lp_theory = LPTheory::new(&self.bounds_for_theory_predicates);
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
}
