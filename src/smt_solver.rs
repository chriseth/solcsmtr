use std::collections::HashMap;

use crate::{types::Clause, sexpr_parser::SExpr, types::RationalWithDelta};

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

#[derive(Default)]
pub struct SMTSolver {
    variables: HashMap<VariableName, Variable>,
    /// Constraints of the form z = 2x + y
    linear_constraints: HashMap<VariableID, Vec<(VariableID, RationalWithDelta)>>,
    clauses: Vec<Clause>,
}

impl SMTSolver {
    pub fn new() -> SMTSolver {
        Default::default()
    }
    pub fn declare_variable(&mut self, name: VariableName, sort: Sort) {
        let id = (self.variables.len() + 1) as VariableID;
        assert!(self.variables.insert(name, Variable { id, sort }).is_none());
    }

    pub fn add_assertion(&mut self, assertion: &SExpr) {}
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

impl SMTSolver {}

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
