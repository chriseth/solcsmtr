use std::{
    collections::{BTreeMap, HashMap},
    fmt::{self, Display},
};

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Num, One, Signed, Zero};

use crate::{
    linear_expression::LinearExpression,
    sexpr_parser::SExpr,
    types::{Bounds, RationalWithDelta},
    types::{Clause, Literal},
};

#[derive(Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Sort {
    #[default]
    Bool,
    Real,
}

type VariableID = i32;
type VariableName = Box<[u8]>;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Variable {
    id: VariableID,
    sort: Sort,
}
// TODO we do not have to use use disjoint sets of IDs for bool and real variables.

impl From<Variable> for Literal {
    fn from(v: Variable) -> Self {
        assert!(v.sort == Sort::Bool);
        Literal::from(v.id)
    }
}

#[derive(Default)]
pub struct SMTSolver {
    variables: HashMap<VariableName, Variable>,
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
        let id = (self.variables.len() + 1) as VariableID;
        let var = Variable { id, sort };
        assert!(self.variables.insert(name, var).is_none());
        var
    }

    pub fn add_assertion(&mut self, assertion: &SExpr) {
        //println!("Adding assertion: {assertion}");
        let op = assertion.as_subexpr()[0].as_symbol();
        let args = &assertion.as_subexpr()[1..];
        match (op, args.len()) {
            (b"true", 0) => {}
            (b"false", 0) => {
                panic!("Added false as top-level assertion.")
            }
            (b"or", _) => {
                // TODO empty?
                let clause = self.parse_into_literals(args);
                self.add_clause(clause);
            }
            (b"and", _) => {
                // TODO empty?
                for a in args {
                    self.add_assertion(a);
                }
            }
            (b"=" | b"<=", 2) => {
                if op == b"=" && self.determine_sort(&args[0]) == Sort::Bool {
                    let args = self.parse_into_literals(args);
                    self.add_clause(vec![!args[0], args[1]]);
                    self.add_clause(vec![args[0], !args[1]]);
                } else {
                    let left = self.parse_affine_expression(&args[0]);
                    let right = self.parse_affine_expression(&args[1]);
                    let (factor, var) =
                        self.extract_real_var_or_replace_by_equivalent(left.1 - right.1);
                    let is_negative = factor.is_negative();
                    let constant = RationalWithDelta::from((right.0 - left.0) / factor);
                    let mut bound = Bounds {
                        lower: Some(constant.clone()),
                        upper: Some(constant),
                    };
                    if op == b"<=" {
                        bound.lower = None;
                    }
                    if is_negative && op != b"=" {
                        bound = Bounds {
                            lower: bound.upper,
                            upper: bound.lower,
                        };
                    }
                    // This is now reduced to: z = c
                    self.fixed_bounds.entry(var.id).or_default().combine(bound);
                }
            }
            (_, 0) => {
                let var = self.variable(op);
                assert!(var.sort == Sort::Bool);
                let lit = Literal::from(var.id);
                self.add_clause(vec![lit]);
            }
            _ => {
                todo!("Assertion not yet implemented: {assertion}")
            }
        }
    }
    pub fn push(&mut self) {
        todo!();
    }
    pub fn pop(&mut self) {
        todo!();
    }
    pub fn check(&mut self) -> Option<bool> {
        println!("{self}");
        None
    }
}

impl Display for SMTSolver {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "SMT solver state:")?;
        let variable_names = self
            .variables
            .iter()
            .map(|(k, v)| (v.id, std::str::from_utf8(k).unwrap()))
            .collect::<HashMap<_, _>>();
        writeln!(f, "Linear equalities:")?;
        for (main_var, expr) in &self.linear_constraints {
            let mut row_string = String::new();
            // TODO this is duplicated in lp_solver.rs
            for (var, f) in expr {
                let joiner = if f.is_negative() {
                    " - "
                } else if f.is_positive() && !row_string.is_empty() {
                    " + "
                } else {
                    " "
                };
                let factor = if *f == BigRational::one() || *f == -BigRational::one() {
                    String::new()
                } else {
                    format!("{} ", f.abs())
                };
                row_string = format!("{row_string}{joiner}{factor}{}", &variable_names[var]);
            }
            writeln!(f, "{} = {row_string}", variable_names[main_var])?;
        }
        // TODO:
        /*
        clauses: Vec<Clause>,
        /// Real variable and its upper bound for each theory predicate, if taken positively.
        bounds_for_theory_predicates: HashMap<VariableID, (VariableID, RationalWithDelta)>,
        fixed_bounds: HashMap<VariableID, Bounds>,
        */
        Ok(())
    }
}

impl SMTSolver {
    fn add_clause(&mut self, clause: Clause) {
        self.clauses.push(clause);
    }
    fn variable(&self, name: &[u8]) -> Variable {
        self.variables[name]
    }
    fn new_bool_variable(&mut self) -> Variable {
        // TODO make the names properly unique.
        let name = format!("_t_{}", self.variables.len() + 1);
        self.declare_variable(name.as_bytes().into(), Sort::Bool)
    }
    fn new_real_variable(&mut self) -> Variable {
        // TODO make the names properly unique.
        let name = format!("_r_{}", self.variables.len() + 1);
        self.declare_variable(name.as_bytes().into(), Sort::Real)
    }

    fn parse_into_literal(&mut self, e: &SExpr) -> Literal {
        // TODO there are tons of optimizations here, we don't always need to craete
        // an equivalent boolean, for example if there are nested 'or's
        if let SExpr::Symbol(s) = e {
            // TODO constants
            let var = self.variable(s);
            assert!(var.sort == Sort::Bool);
            return Literal::from(var.id);
        }
        let op = e.as_subexpr()[0].as_symbol();
        let args = &e.as_subexpr()[1..];
        match (op, args.len()) {
            (b"or", 2) => {
                // TODO extend to longer
                let args = self.parse_into_literals(args);
                self.encode_or(args[0], args[1])
            }
            (b"and", 2) => {
                let args = self.parse_into_literals(args);
                self.encode_and(args[0], args[1])
            }
            (b"not", 1) => {
                assert!(args.len() == 1);
                !self.parse_into_literal(&args[0])
            }
            (b"=", 2) => {
                match self.determine_sort(&args[0]) {
                    Sort::Bool => {
                        let result: Literal = self.new_bool_variable().into();
                        let args = self.parse_into_literals(args);
                        self.add_clause(vec![!args[0], args[1], !result]);
                        self.add_clause(vec![args[0], !args[1], !result]);
                        self.add_clause(vec![!args[0], !args[1], result]);
                        self.add_clause(vec![args[0], args[1], result]);
                        result
                    }
                    Sort::Real => {
                        let left = self.parse_affine_expression(&args[0]);
                        let right = self.parse_affine_expression(&args[1]);
                        let (factor, var) =
                            self.extract_real_var_or_replace_by_equivalent(left.1 - right.1);
                        let constant = RationalWithDelta::from((right.0 - left.0) / factor);
                        // This is now reduced to: z = c
                        let less_or_equal = self.new_theory_predicate(var, constant.clone());
                        // !(x < c) is equivalent to x >= c
                        let less_than =
                            self.new_theory_predicate(var, constant + RationalWithDelta::delta());
                        self.encode_and(less_or_equal, !less_than)
                    }
                }
            }
            (b"<=", 2) | (b"<", 2) | (b">", 2) | (b">=", 2) => {
                let is_strict = op == b"<" || op == b">";
                let mut is_reversed = op == b">=" || op == b">";
                let left = self.parse_affine_expression(&args[0]);
                let right = self.parse_affine_expression(&args[1]);
                let (factor, var) =
                    self.extract_real_var_or_replace_by_equivalent(left.1 - right.1);
                if factor.is_negative() {
                    // We divide by factor below, so we need to flip the operator.
                    is_reversed = !is_reversed;
                }
                let mut constant = RationalWithDelta::from((right.0 - left.0) / factor);
                // This is now reduced to: var OP constant
                // In the reversed case, we will negate, so strict and non-strict flip
                if is_strict ^ is_reversed {
                    constant += RationalWithDelta::delta()
                }
                let p = self.new_theory_predicate(var, constant);
                if is_reversed {
                    !p
                } else {
                    p
                }
            }
            (_, _) => {
                panic!("Expected to parse into boolean expression: {}", e);
            }
        }
    }

    fn encode_or(&mut self, arg1: Literal, arg2: Literal) -> Literal {
        // TODO extend to longer
        let result: Literal = self.new_bool_variable().into();
        self.add_clause(vec![arg1, arg2, !result]);
        self.add_clause(vec![!arg1, result]);
        self.add_clause(vec![!arg2, result]);
        result
    }

    fn encode_and(&mut self, arg1: Literal, arg2: Literal) -> Literal {
        !self.encode_or(!arg1, !arg2)
    }

    fn parse_into_literals(&mut self, items: &[SExpr]) -> Vec<Literal> {
        items
            .iter()
            .map(|e| self.parse_into_literal(e))
            .collect::<Vec<_>>()
    }

    fn determine_sort(&self, e: &SExpr) -> Sort {
        if let SExpr::Symbol(s) = e {
            let var = self.variable(s);
            var.sort
        } else {
            match e.as_subexpr()[0].as_symbol() {
                b"-" => Sort::Real,
                _ => panic!("Could not determine sort of arguments to {}", e),
            }
        }
    }

    fn parse_affine_expression(&mut self, e: &SExpr) -> (BigRational, LinearExpression) {
        if let SExpr::Symbol(s) = e {
            if matches!(s[0], b'0'..=b'9') {
                (
                    BigInt::parse_bytes(s, 10).unwrap().into(),
                    LinearExpression::default(),
                )
            } else {
                let var = self.variable(s);
                assert!(var.sort == Sort::Real);
                (BigRational::zero(), LinearExpression::variable(var.id))
            }
        } else {
            let op = e.as_subexpr()[0].as_symbol();
            let args = &e.as_subexpr()[1..];
            match (op, args.len()) {
                (b"-", 2) => {
                    let (lc, ll) = self.parse_affine_expression(&args[0]);
                    let (rc, rl) = self.parse_affine_expression(&args[1]);
                    (lc - rc, ll - rl)
                }
                (b"+", _) => args
                    .iter()
                    .map(|a| self.parse_affine_expression(a))
                    .fold(Default::default(), |l, r| (l.0 + r.0, l.1 + r.1)),
                (b"*", 2) => {
                    let mut left = self.parse_affine_expression(&args[0]);
                    let mut right = self.parse_affine_expression(&args[1]);
                    if left.1.iter().len() != 0 {
                        (left, right) = (right, left)
                    }
                    assert!(left.1.iter().len() == 0);
                    (left.0.clone() * right.0, left.0 * right.1)
                }
                (_, _) => {
                    panic!("Expected to parse into affine expression: {}", e);
                }
            }
        }
    }

    /// If the linear expression is of the form "a * x", returns (a, x).
    /// Otherwise, creates a new variable z and adds "z = a * x" to the linear constraints.
    /// It might also re-use an existing linear constraint.
    fn extract_real_var_or_replace_by_equivalent(
        &mut self,
        expr: LinearExpression,
    ) -> (BigRational, Variable) {
        assert!(expr.iter().len() > 0);
        if expr.iter().len() == 1 {
            let (id, factor) = expr.into_iter().next().unwrap();
            (
                factor,
                Variable {
                    id,
                    sort: Sort::Real,
                },
            )
        } else {
            // TODO try to re-use existing constraints.
            let new_var = self.new_real_variable();
            self.linear_constraints
                .insert(new_var.id, expr.into_iter().collect::<Vec<_>>());
            (One::one(), new_var)
        }
    }

    fn is_theory_predicate(&self, var: Variable) -> bool {
        assert!(var.sort == Sort::Bool);
        self.bounds_for_theory_predicates.contains_key(&var.id)
    }

    /// Creates a new boolean variable equivalent to "var <= upper_bound".
    fn new_theory_predicate(&mut self, var: Variable, upper_bound: RationalWithDelta) -> Literal {
        assert!(var.sort == Sort::Real);
        let predicate = self.new_bool_variable();
        self.bounds_for_theory_predicates
            .insert(predicate.id, (var.id, upper_bound));
        predicate.into()
    }
}
