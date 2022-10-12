use std::{
    cmp::{max, min},
    collections::HashMap,
};

use num_rational::BigRational;

use crate::{sparse_matrix::SparseMatrix, types::*};

type Number = BigRational;

pub struct LPSolver {
    tableau: SparseMatrix<Number>,

    variables: Vec<Variable>,
    /// Maps outer variable IDs to inner variable IDs.
    var_mapping: HashMap<usize, usize>,
    feasible: Option<bool>,
}

#[derive(Default)]
struct Variable {
    value: RationalWithDelta,
    bounds: Bounds,
    #[cfg(Debug)]
    name: String,
}

impl Variable {
    pub fn violates_upper_bound(&self) -> bool {
        self.bounds
            .upper
            .as_ref()
            .filter(|b| self.value > **b)
            .is_some()
    }
    pub fn violates_lower_bound(&self) -> bool {
        self.bounds
            .lower
            .as_ref()
            .filter(|b| self.value < **b)
            .is_some()
    }
}

#[derive(Default)]
pub struct Bounds {
    pub lower: Option<RationalWithDelta>,
    pub upper: Option<RationalWithDelta>,
}

impl Bounds {
    pub fn combine(&mut self, other: Bounds) {
        *self = combine_bounds(std::mem::take(self), other);
    }
}

impl LPSolver {
    pub fn append_row(&mut self, outer_id: usize, data: impl Iterator<Item = (usize, Number)>) {
        self.feasible = None;
        // TODO do this without copying - maybe separate variables into their own sub-structure?
        let data = data
            .map(|(outer_id, v)| (self.add_outer_variable(outer_id), v))
            .collect::<Vec<_>>();
        self.tableau.append_row(data.into_iter());
    }
    pub fn restrict_bounds(&mut self, outer_id: usize, bounds: Bounds) {
        self.feasible = None;
        let var_id = self.add_outer_variable(outer_id);
        self.variables[var_id].bounds.combine(bounds);
    }
    #[cfg(Debug)]
    pub fn set_variable_name(&mut self, outer_id: usize, name: String) {
        let var_id = self.add_outer_variable(outer_id);
        self.variables[var_id].name = name;
    }

    pub fn feasible(&mut self) -> Option<bool> {
        if self.feasible.is_some() {
            return self.feasible;
        }
        if !self.correct_nonbasic() {
            return Some(false);
        }
        while let Some(cbv) = self.first_conflicting_basic_variable() {
            let var = &self.variables[cbv];
            if var.violates_lower_bound() {
                if let Some(replacement) = self.first_replacement_var(cbv, true) {
                    self.pivot_and_update(cbv, var.bounds.lower.clone().unwrap(), replacement);
                } else {
                    return Some(false);
                }
            } else {
                assert!(var.violates_upper_bound());
                if let Some(replacement) = self.first_replacement_var(cbv, false) {
                    self.pivot_and_update(cbv, var.bounds.upper.clone().unwrap(), replacement);
                } else {
                    return Some(false);
                }
            }
        }
        Some(true)
    }
}

impl LPSolver {
    fn add_outer_variable(&mut self, outer_id: usize) -> usize {
        *self.var_mapping.entry(outer_id).or_insert_with(|| {
            self.variables.push(Default::default());
            self.variables.len() - 1
        })
    }
    fn correct_nonbasic(&mut self) -> bool {
        true
    }
    fn first_conflicting_basic_variable(&self) -> Option<usize> {
        None
    }
    fn first_replacement_var(&self, basic: usize, increasing: bool) -> Option<usize> {
        None
    }
    fn pivot_and_update(
        &mut self,
        old_basic: usize,
        new_value: RationalWithDelta,
        new_basic: usize,
    ) {
    }
}

fn combine_bounds(a: Bounds, b: Bounds) -> Bounds {
    Bounds {
        lower: combine_lower(a.lower, b.lower),
        upper: combine_upper(a.upper, b.upper),
    }
}

fn combine_lower(
    a: Option<RationalWithDelta>,
    b: Option<RationalWithDelta>,
) -> Option<RationalWithDelta> {
    match (a, b) {
        (Some(x), Some(y)) => Some(max(x, y)),
        (a, b) => a.and(b),
    }
}

fn combine_upper(
    a: Option<RationalWithDelta>,
    b: Option<RationalWithDelta>,
) -> Option<RationalWithDelta> {
    match (a, b) {
        (Some(x), Some(y)) => Some(min(x, y)),
        (a, b) => a.and(b),
    }
}
