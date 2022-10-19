use std::collections::HashMap;

use crate::{types::{Clause, Literal}, sexpr_parser::SExpr, types::RationalWithDelta};

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
    /// Upper bound for each theory predicate, if taken positively.
    bounds_for_theory_predicates: HashMap<VariableID, RationalWithDelta>,
}

impl SMTSolver {
    pub fn new() -> SMTSolver {
        Default::default()
    }
    pub fn declare_variable(&mut self, name: VariableName, sort: Sort) -> Variable {
        let id = (self.variables.len() + 1) as VariableID;
        let var = Variable{id, sort};
        assert!(self.variables.insert(name, var).is_none());
        var
    }

    pub fn add_assertion(&mut self, assertion: &SExpr) {
        let op = assertion.as_subexpr()[0].as_symbol();
        let args = &assertion.as_subexpr()[1..];
        match op {
            b"true" => {},
            b"false" => { panic!("Added false as top-level assertion.") },
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
        let op = e.as_subexpr()[0].as_symbol();
        let args = &e.as_subexpr()[1..];
        match (op, args.len()) {
            (b"or", 2) => {
                // TODO extend to longer
                let result: Literal = self.new_bool_variable().into();
                let args = self.parse_into_literals(args);
                self.add_clause(vec![args[0], args[1], !result]);
                self.add_clause(vec![!args[0], result]);
                self.add_clause(vec![!args[1], result]);
                result
            }
            (b"and", 2) => {
                let result: Literal = self.new_bool_variable().into();
                let args = self.parse_into_literals(args);
                self.add_clause(vec![!args[0], !args[1], result]);
                self.add_clause(vec![args[0], !result]);
                self.add_clause(vec![args[1], !result]);
                result
            }
            (b"not", 1) => {
                assert!(args.len() == 1);
                !self.parse_into_literal(&args[0])
            }
            (_, 0) => {
                let var = self.variable(op);
                assert!(var.sort == Sort::Bool);
                Literal::from(var.id)
            },
            (_, _) => {
                panic!("Expected to parse into boolean expression: {}", e);
            }
        }
    }

    fn parse_into_literals(&mut self, items: &[SExpr]) -> Vec<Literal> {
        items.iter().map(|e| self.parse_into_literal(e)).collect::<Vec<_>>()
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

*/
