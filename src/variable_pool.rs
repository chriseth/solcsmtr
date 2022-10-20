use std::{collections::HashMap, iter::Iterator};

// different kinds of variables could share ID sets.
// This way we would not need the compression in the linear solven.
// On the other hand, the translation from ID to name needs a sort.

#[derive(Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Sort {
    #[default]
    Bool,
    Real,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Variable {
    pub id: VariableID,
    pub sort: Sort,
}

pub type VariableID = i32;
pub type VariableName = Box<[u8]>;

#[derive(Default)]
pub struct VariablePool {
    // TODO is there a way so that we don't have to store
    // the variable names twice?
    variables: HashMap<VariableName, Variable>,
    variable_names: Vec<VariableName>,
}

impl VariablePool {
    pub fn new() -> VariablePool {
        Default::default()
    }
    pub fn declare_variable(&mut self, name: VariableName, sort: Sort) -> Variable {
        // TODO we have to guarantee that all IDs are > 0,
        // because Literal uses that
        if self.variable_names.is_empty() {
            self.variable_names.push(VariableName::default())
        }
        let id = self.variable_names.len() as VariableID;
        self.variable_names.push(name.clone());
        let var = Variable { id, sort };
        assert!(self.variables.insert(name, var).is_none());
        var
    }
    // TODO make the parameter type as flexible as the one of the hash map
    pub fn variable(&self, name: &[u8]) -> Variable {
        self.variables[name]
    }
    pub fn all_ids(&self) -> impl Iterator<Item = VariableID> {
        (1..self.variables.len()).map(|v| v as VariableID)
    }
    pub fn name(&self, var: VariableID) -> &str {
        std::str::from_utf8(&self.variable_names[var as usize]).unwrap()
    }
    pub fn variable_count(&self) -> usize {
        self.variable_names.len() - 1
    }
}
