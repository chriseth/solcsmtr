use std::collections::HashMap;

use num_rational::BigRational;

use crate::{
    linear_expression::LinearExpression,
    sexpr_parser::SExpr,
    types::RationalWithDelta,
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
    linear_constraints: HashMap<VariableID, Vec<(VariableID, RationalWithDelta)>>,
    clauses: Vec<Clause>,
    /// Real variable and its upper bound for each theory predicate, if taken positively.
    bounds_for_theory_predicates: HashMap<VariableID, (VariableID, RationalWithDelta)>,
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
        let op = assertion.as_subexpr()[0].as_symbol();
        let args = &assertion.as_subexpr()[1..];
        match op {
            b"true" => {}
            b"false" => {
                panic!("Added false as top-level assertion.")
            }
            b"or" => {
                // TODO empty?
                let clause = self.parse_into_literals(args);
                self.add_clause(clause);
            }
            b"and" => {
                // TODO empty?
                for a in args {
                    self.add_assertion(a);
                }
            }
            _ => {
                assert_eq!(args.len(), 0);
                let var = self.variable(op);
                assert!(var.sort == Sort::Bool);
                let lit = Literal::from(var.id);
                self.add_clause(vec![lit]);
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
        None
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
                    Some(Sort::Bool) => {
                        let result: Literal = self.new_bool_variable().into();
                        let args = self.parse_into_literals(args);
                        self.add_clause(vec![!args[0], args[1], !result]);
                        self.add_clause(vec![args[0], !args[1], !result]);
                        self.add_clause(vec![!args[0], !args[1], result]);
                        self.add_clause(vec![args[0], args[1], result]);
                        result
                    }
                    Some(Sort::Real) => {
                        let left = self.parse_affine_expression(&args[0]);
                        let right = self.parse_affine_expression(&args[1]);
                        let linear = left.1 - right.1;
                        let constant = RationalWithDelta::from(right.0 - left.0);
                        let var = self.extract_real_var_or_replace_by_equivalent(linear);
                        let less_or_equal = self.new_theory_predicate(var, constant.clone());
                        // !(x < c) is equivalent to x >= c
                        let less_than = self.new_theory_predicate(
                            var,
                            constant + RationalWithDelta::delta(),
                        );
                        self.encode_and(less_or_equal, !less_than)
                    }
                    None => panic!("Could not determine sort of arguments to {}", e),
                }
            }
            (b"<=", 2) | (b"<", 2) | (b">", 2) | (b">=", 2) => {
                let is_strict = op == b"<" || op == b">";
                let mut left = self.parse_affine_expression(&args[0]);
                let mut right = self.parse_affine_expression(&args[1]);
                if op == b">" || op == b">=" {
                    (left, right) = (right, left);
                }
                let linear = left.1 - right.1;
                let constant = RationalWithDelta::from(right.0 - left.0)
                    + if is_strict {
                        RationalWithDelta::delta()
                    } else {
                        RationalWithDelta::default()
                    };
                let var = self.extract_real_var_or_replace_by_equivalent(linear);
                self.new_theory_predicate(var, constant)
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

    fn determine_sort(&self, e: &SExpr) -> Option<Sort> {
        if let SExpr::Symbol(s) = e {
            let var = self.variable(s);
            Some(var.sort)
        } else {
            None
        }
    }

    fn parse_affine_expression(&mut self, e: &SExpr) -> (BigRational, LinearExpression) {
        todo!();
    }

    fn extract_real_var_or_replace_by_equivalent(&mut self, expr: LinearExpression) -> Variable {
        todo!();
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

/*
turn
-(x + 7 <= 8) \/ A
into
-(x <= 1) \/ A
into
-T1  \/ A
T1: x <= 1

turn 2x + 9y < 7
into
x + 4.5y < 3.5
into
T1
row: z = x + 4.5y
T2 z < 3.5

So for every "theory predicate":
we perform "constant propagation" until we have "a_i * x_i <=/< Constant"
then we divide by "a_0"
if there is more than one variable, we simplify:
 - unless the LHS expression does not already have a corresponding variable:
 - introduce new variable and add equality as fact
 - replace the LHS by the new variable
store lower/upper bound relation as predicate (which can be easily negated)

TODO Question: How to encode equality? I.e. how to negate it? Do we need to?

z = 2 <=> (z <= 2 && z >= 2)

*/
