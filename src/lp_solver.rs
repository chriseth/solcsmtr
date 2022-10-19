use std::{
    cmp::{max, min},
    collections::HashMap,
    fmt::{self, Display},
};

use num_rational::{BigRational, Ratio};
use num_traits::{One, Signed, Zero};

use crate::{sparse_matrix::SparseMatrix, types::*};

type Number = BigRational;

#[derive(Default)]
pub struct LPSolver {
    tableau: SparseMatrix<Number>,
    variables: Vec<Variable>,
    /// Mapping from variable id to row it controls.
    basic_variable_to_row: HashMap<usize, usize>,
    basic_variable_for_row: Vec<usize>,
    /// Maps outer variable IDs to inner variable IDs.
    var_mapping: HashMap<VariableID, usize>,
    feasible: Option<bool>,
}

#[derive(Default)]
struct Variable {
    value: RationalWithDelta,
    bounds: Bounds,
    #[cfg(debug_assertions)]
    name: String,
}

impl Variable {
    pub fn can_be_increased(&self) -> bool {
        if let Some(u) = &self.bounds.upper {
            self.value < *u
        } else {
            true
        }
    }
    pub fn can_be_decreased(&self) -> bool {
        if let Some(l) = &self.bounds.lower {
            self.value > *l
        } else {
            true
        }
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
    pub fn name(&self) -> String {
        #[cfg(debug_assertions)]
        {
            self.name.clone()
        }
        #[cfg(not(debug_assertions))]
        {
            // TODO at some point, use the IDs
            String::new()
        }
    }
}

impl Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(l) = &self.bounds.lower {
            write!(f, "{:>8} <= ", format!("{}", l))?
        } else {
            write!(f, "{:8}    ", "")?
        }
        write!(f, "{:^4}", self.name())?;
        if let Some(u) = &self.bounds.upper {
            write!(f, "<= {:<8}", format!("{}", u))?
        } else {
            write!(f, "   {:8}", "")?
        }
        write!(f, ":= {}", self.value)
    }
}

impl LPSolver {
    /// Appends a row represented by the variable `outer_id`. The row must not have any
    /// factor corresponding to that variable.
    pub fn append_row(
        &mut self,
        outer_id: VariableID,
        data: impl IntoIterator<Item = (VariableID, Number)>,
    ) {
        self.feasible = None;
        let basic_id = self.add_outer_variable(outer_id);
        // TODO do this without copying - maybe separate variables into their own sub-structure?
        let data = data
            .into_iter()
            .map(|(outer_id, v)| (self.add_outer_variable(outer_id), v))
            .collect::<Vec<_>>();
        let row = self.tableau.rows();
        self.tableau.append_row(data.into_iter());
        *self.tableau.entry(row, basic_id) = -BigRational::one();
        self.basic_variable_for_row.push(basic_id);
        self.basic_variable_to_row.insert(basic_id, row);
    }
    pub fn restrict_bounds(&mut self, outer_id: VariableID, bounds: Bounds) {
        self.feasible = None;
        let var_id = self.add_outer_variable(outer_id);
        self.variables[var_id].bounds.combine(bounds);
    }
    #[cfg(debug_assertions)]
    pub fn set_variable_name(&mut self, outer_id: VariableID, name: String) {
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
                // Undo correction of basic vaiable.
                self.variables[cbv].value -= diff;
                self.feasible = Some(false);
                return Some(false);
            }
        }
        self.feasible = Some(true);
        Some(true)
    }
}

impl Display for LPSolver {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for v in &self.variables {
            writeln!(f, "{}", v)?
        }
        for row in 0..self.tableau.rows() {
            let mut basic_var_prefix = String::new();
            let mut row_string = String::new();
            let basic_var = self.basic_variable_for_row[row];
            for (_, column, f) in self.tableau.iterate_row(row) {
                if column == basic_var {
                    assert!(basic_var_prefix.is_empty());
                    assert!(*f == -BigRational::one());
                    basic_var_prefix = format!("{:>4} = ", self.variables[basic_var].name());
                } else {
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
                    row_string = format!(
                        "{row_string}{joiner}{factor}{}",
                        self.variables[column].name()
                    );
                }
            }
            assert!(!basic_var_prefix.is_empty());
            writeln!(f, "{}{}", basic_var_prefix, row_string)?;
        }
        Ok(())
    }
}

impl LPSolver {
    fn add_outer_variable(&mut self, outer_id: VariableID) -> usize {
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
            if self.basic_variable_to_row.contains_key(&id) {
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
        for (_, column, factor) in self.tableau.iterate_row(self.basic_variable_to_row[&basic]) {
            if column == basic {
                continue;
            }
            assert!(!factor.is_zero());
            let check_upper = factor.is_negative() ^ increasing;
            if (check_upper && self.variables[column].can_be_increased())
                || self.variables[column].can_be_decreased()
            {
                return Some(column);
            }
        }
        None
    }
    // TODO actually does this updatE?
    fn pivot_and_update(
        &mut self,
        old_basic: usize,
        value_diff: RationalWithDelta,
        new_basic: usize,
    ) {
        let old_row = self.basic_variable_to_row[&old_basic];
        let theta = value_diff / self.tableau.entry(old_row, new_basic).clone();
        self.variables[new_basic].value += theta.clone();
        // TODO combine this with the iteration in `correct_nonbasic`.
        // Maybe even combine it with the update() call.
        for (row, _, factor) in self.tableau.iterate_column(new_basic) {
            let i = self.basic_variable_for_row[row];
            if i != old_basic {
                self.variables[i].value += theta.clone() * factor.clone();
            }
        }
        self.pivot(old_basic, new_basic);
    }

    fn pivot(&mut self, old_basic: usize, new_basic: usize) {
        let pivot_row = self.basic_variable_to_row[&old_basic];
        let pivot = self.tableau.entry(pivot_row, new_basic).clone();
        assert!(!pivot.is_zero());
        if pivot != -BigRational::one() {
            self.tableau
                .multiply_row_by_factor(pivot_row, -pivot.recip());
        }
        let factors = self
            .tableau
            .iterate_column(new_basic)
            .map(|(row, _, f)| (row, f.clone()))
            .collect::<Vec<_>>();
        for (row, factor) in factors {
            if row != pivot_row {
                self.tableau.add_multiple_of_row(pivot_row, row, factor);
            }
        }
        self.basic_variable_to_row.remove_entry(&old_basic);
        self.basic_variable_to_row.insert(new_basic, pivot_row);
        self.basic_variable_for_row[pivot_row] = new_basic;
    }
}

#[cfg(test)]
mod test {
    use crate::linear_expression::test::SymbolicVariableGenerator;

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
        solver.append_row(g.id("_t"), 2 * x + y);
        g.transfer_names(&mut solver);
        solver.restrict_bounds(
            g.id("_t"),
            Bounds {
                lower: Some(to_rat(0).into()),
                upper: Some(to_rat(0).into()),
            },
        );
        solver.restrict_bounds(
            g.id("x"),
            Bounds {
                lower: Some(to_rat(2).into()),
                upper: None,
            },
        );
        assert_eq!(solver.feasible(), Some(true));
        solver.restrict_bounds(
            g.id("y"),
            Bounds {
                lower: Some((to_rat(2)).into()),
                upper: None,
            },
        );
        assert_eq!(solver.feasible(), Some(false));
        // Query again.
        assert_eq!(solver.feasible(), Some(false));
    }
}
