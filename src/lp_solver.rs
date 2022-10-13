use std::{
    cmp::{max, min},
    collections::HashMap,
};

use num_rational::{BigRational, Ratio};
use num_traits::Signed;

use crate::{sparse_matrix::SparseMatrix, types::*};

type Number = BigRational;

#[derive(Default)]
pub struct LPSolver {
    tableau: SparseMatrix<Number>,
    variables: Vec<Variable>,
    /// Mapping from variable id to row it controls.
    basic_variables: HashMap<usize, usize>,
    basic_variable_for_row: Vec<usize>,
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
    /// Updates the variable to be within bounds and returns the difference
    pub fn update(&mut self) -> Option<RationalWithDelta> {
        let v = match &self.bounds {
            Bounds { lower: Some(l), .. } if self.value < *l => l.clone(),
            Bounds { upper: Some(u), .. } if self.value > *u => u.clone(),
            _ => return None,
        };
        let old = std::mem::replace(&mut self.value, v.clone());
        Some(v - old)
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
    pub fn are_conflicting(&self) -> bool {
        if let (Some(l), Some(u)) = (&self.lower, &self.upper) {
            l > u
        } else {
            false
        }
    }
}

impl LPSolver {
    pub fn append_row(&mut self, outer_id: usize, data: impl IntoIterator<Item = (usize, Number)>) {
        self.feasible = None;
        // TODO do this without copying - maybe separate variables into their own sub-structure?
        let data = data
            .into_iter()
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
        while let Some((cbv, diff)) = self.first_conflicting_basic_variable() {
            let var = &self.variables[cbv];
            if let Some(replacement) = self.first_replacement_var(cbv, diff.is_positive()) {
                self.pivot_and_update(cbv, diff, replacement);
            } else {
                return Some(false);
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
        // TODO mark "dirty" nonbasic variables at the point where they are modified.
        // TODO could we actually split basic and non-basic variables
        // into two vectors?
        for id in 0..self.variables.len() {
            let v = &mut self.variables[id];
            if v.bounds.are_conflicting() {
                return false;
            }
            if self.basic_variables.contains_key(&id) {
                continue;
            }
            if let Some(diff) = v.update() {
                for (row, _, factor) in self.tableau.iterate_column(id) {
                    let bv = self.basic_variable_for_row[row];
                    self.variables[bv].value += diff.clone() * factor.clone();
                }
            }
        }
        true
    }
    /// Finds the first conflicting basic variable, updates it and returns its ID and
    /// difference after the update.
    fn first_conflicting_basic_variable(&mut self) -> Option<(usize, RationalWithDelta)> {
        for id in &self.basic_variable_for_row {
            if let Some(diff) = self.variables[*id].update() {
                return Some((*id, diff));
            }
        }
        None
    }
    fn first_replacement_var(&self, basic: usize, increasing: bool) -> Option<usize> {
        None
    }
    fn pivot_and_update(
        &mut self,
        old_basic: usize,
        value_diff: RationalWithDelta,
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

#[cfg(test)]
mod test {
    use crate::linear_expression::SymbolicVariableGenerator;

    use super::*;
    #[test]
    fn empty() {
        let mut solver = LPSolver::default();
        assert_eq!(solver.feasible(), Some(true));
    }
    #[test]
    fn simple() {
        let mut solver = LPSolver::default();
        let mut g = SymbolicVariableGenerator::default();
        let x = g.var("x");
        let y = g.var("y");
        let t = g.var("_t");
        solver.append_row(g.id("_t"), 2 * x + y);
        solver.restrict_bounds(
            g.id("x"),
            Bounds {
                lower: Some(to_rat(2).into()),
                upper: None,
            },
        );
        assert_eq!(solver.feasible, Some(true));
        solver.restrict_bounds(
            g.id("y"),
            Bounds {
                lower: None,
                upper: Some((-to_rat(20)).into()),
            },
        );
    }
}
