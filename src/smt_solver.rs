use std::collections::HashMap;
use std::fmt::{self, Display};

use num_rational::BigRational;

use crate::cdcl::CDCL;
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
        // TODO we could keep the state of the solver for longer.
        let mut cdcl = CDCL::new(&self.variables);
        let mut lpsolver = LPSolver::default();
        for (var, bounds) in &self.fixed_bounds {
            lpsolver.restrict_bounds(*var, bounds.clone());
        }
        for (basic_var, linear_expr) in &self.linear_constraints {
            lpsolver.append_row(*basic_var, linear_expr.iter().cloned());
        }
        if !lpsolver.feasible() {
            return Some(false);
        }

        //println!("{self}");
        None
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
