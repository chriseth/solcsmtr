use crate::sexpr_parser::SExpr;

pub struct SMTSolver {}

impl SMTSolver {
    pub fn new() -> SMTSolver {
        SMTSolver{}
    }
    pub fn add_assertion(&mut self, assertion: &SExpr) {}
    pub fn push(&mut self) { todo!(); }
    pub fn pop(&mut self) { todo!(); }
    pub fn check(&mut self) -> Option<bool> { None }
}
