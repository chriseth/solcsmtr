use std::collections::{HashMap, HashSet};

use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::{
    linear_expression::LinearExpression,
    sparse_matrix::SparseMatrix,
    types::*,
    variable_pool::{VariableID, VariablePool},
};

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
    reasons: (Option<Literal>, Option<Literal>),
}

impl Variable {
    pub fn restrict_bounds_with_reason(
        &mut self,
        bounds: Bounds,
        reasons: (Option<Literal>, Option<Literal>),
    ) -> Option<(Bounds, (Option<Literal>, Option<Literal>))> {
        let old_bounds = self.bounds.clone();
        self.bounds.combine(bounds);
        if old_bounds != self.bounds {
            let old_reasons = self.reasons.clone();
            if old_bounds.lower != self.bounds.lower {
                self.reasons.0 = reasons.0;
            }
            if old_bounds.upper != self.bounds.upper {
                self.reasons.1 = reasons.1;
            }
            Some((old_bounds, old_reasons))
        } else {
            None
        }
    }

    pub fn set_bounds_with_reason(
        &mut self,
        bounds: Bounds,
        reasons: (Option<Literal>, Option<Literal>),
    ) {
        self.bounds = bounds;
        self.reasons = reasons;
    }

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
        if let Some(v) = self.needs_update() {
            let old = std::mem::replace(&mut self.value, v.clone());
            Some(v - old)
        } else {
            None
        }
    }

    /// Returns an in-bounds value in case the variable is currently out
    /// of bounds. Otherwise, returns None.
    pub fn needs_update(&self) -> Option<RationalWithDelta> {
        match &self.bounds {
            Bounds { lower: Some(l), .. } if self.value < *l => Some(l.clone()),
            Bounds { upper: Some(u), .. } if self.value > *u => Some(u.clone()),
            _ => None,
        }
    }

    pub fn format(&self, name: &str) -> String {
        // TODO format reasons
        use colored::Colorize;
        let s = format!("{} := {}", self.bounds.format(name), self.value);
        if self.needs_update().is_some() {
            format!("{}", s.red())
        } else {
            s
        }
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
        let mut data = data
            .into_iter()
            .map(|(outer_id, v)| (self.add_outer_variable(outer_id), v))
            .collect::<Vec<_>>();
        data.sort();
        let row = self.tableau.rows();
        self.tableau.append_row(data.into_iter());
        *self.tableau.entry(row, basic_id) = -BigRational::one();
        self.basic_variable_for_row.push(basic_id);
        self.basic_variable_to_row.insert(basic_id, row);
    }
    pub fn restrict_bounds(&mut self, outer_id: VariableID, bounds: Bounds) {
        self.restrict_bounds_with_reason(outer_id, bounds, (None, None));
    }
    /// Restrict bounds and provide reasons.
    /// Reasons must be unique literals that are a consequence of a violation of the bound.
    /// Returns the previous values if the new bounds are stricter.
    pub fn restrict_bounds_with_reason(
        &mut self,
        outer_id: VariableID,
        bounds: Bounds,
        reasons: (Option<Literal>, Option<Literal>),
    ) -> Option<(Bounds, (Option<Literal>, Option<Literal>))> {
        let var_id = self.add_outer_variable(outer_id);
        let old_values = self.variables[var_id].restrict_bounds_with_reason(bounds, reasons);
        if old_values.is_some() {
            self.feasible = None;
        }
        old_values
    }

    /// Set bounds and provide reasons, replacing previous values.
    /// Reasons must be unique literals that are a consequence of a violation of the bound.
    pub fn set_bounds_with_reason(
        &mut self,
        outer_id: VariableID,
        bounds: Bounds,
        reasons: (Option<Literal>, Option<Literal>),
    ) {
        let var_id = self.add_outer_variable(outer_id);
        self.variables[var_id].set_bounds_with_reason(bounds, reasons);
        self.feasible = None;
    }

    /// Returns None if feasible, otherwise returns a set of reasons.
    pub fn feasible(&mut self) -> Option<Clause> {
        if self.feasible == Some(true) {
            return None;
            // TODO do we want to use a cached infeasible result?
        }
        if let Some(reasons) = self.correct_nonbasic() {
            self.feasible = Some(false);
            return Some(reasons);
        } else {
            while let Some((cbv, diff)) = self.fix_first_conflicting_basic_variable() {
                if let Some(replacement) = self.first_replacement_var(cbv, diff.is_positive()) {
                    self.pivot_and_update(cbv, diff, replacement);
                } else {
                    // Undo correction of basic vaiable.
                    self.variables[cbv].value -= diff.clone();

                    self.feasible = Some(false);
                    return Some(self.reasons_for_unsat(cbv, diff.is_positive()));
                }
            }
        }
        None
    }

    pub fn format(&self, pool: &VariablePool) -> String {
        let inverse_var_mapping = self
            .var_mapping
            .iter()
            .map(|(outer, inner)| (*inner, *outer))
            .collect::<HashMap<_, _>>();
        let formatted_variables = self
            .variables
            .iter()
            .enumerate()
            .map(|(id, var)| var.format(pool.name(inverse_var_mapping[&id])))
            .collect::<Vec<_>>()
            .join("\n");
        let formatted_rows = (0..self.tableau.rows())
            .map(|row| self.format_row(row, &|column| pool.name(inverse_var_mapping[&column])))
            .collect::<Vec<_>>()
            .join("\n");
        format!("{formatted_variables}\n{formatted_rows}\n")
    }

    fn format_row<'a>(&self, row: usize, id_to_name: &'a impl Fn(usize) -> &'a str) -> String {
        let mut basic_var_prefix = String::new();
        let basic_var = self.basic_variable_for_row[row];
        let nonbasic =
            LinearExpression::format(self.tableau.iterate_row(row).filter_map(|(_, column, f)| {
                if column == basic_var {
                    assert!(basic_var_prefix.is_empty());
                    assert!(*f == -BigRational::one());
                    basic_var_prefix = format!("{:>4} = ", id_to_name(column));
                    None
                } else {
                    Some((id_to_name(column), f))
                }
            }));

        assert!(!basic_var_prefix.is_empty());
        format!("{basic_var_prefix}{nonbasic}")
    }
}

impl LPSolver {
    fn add_outer_variable(&mut self, outer_id: VariableID) -> usize {
        *self.var_mapping.entry(outer_id).or_insert_with(|| {
            self.variables.push(Default::default());
            self.variables.len() - 1
        })
    }
    /// Try to change all nonbasic variables to be in bounds.
    /// If this is not possible (because one variable has conflicting bounds),
    /// returns the set of reasons for that variable.
    fn correct_nonbasic(&mut self) -> Option<Clause> {
        // TODO mark "dirty" nonbasic variables at the point where they are modified.
        // TODO could we actually split basic and non-basic variables
        // into two vectors?
        for id in 0..self.variables.len() {
            let v = &mut self.variables[id];
            if v.bounds.are_conflicting() {
                return Some(v.reasons.0.into_iter().chain(v.reasons.1).collect());
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
        None
    }
    /// Finds the first conflicting basic variable, updates it and returns its ID and
    /// difference after the update.
    fn fix_first_conflicting_basic_variable(&mut self) -> Option<(usize, RationalWithDelta)> {
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
                || (!check_upper && self.variables[column].can_be_decreased())
            {
                return Some(column);
            }
        }
        None
    }
    fn reasons_for_unsat(&self, basic: usize, increasing: bool) -> Clause {
        let mut reasons = vec![];
        if increasing {
            reasons.extend(self.variables[basic].reasons.0.iter());
        } else {
            reasons.extend(self.variables[basic].reasons.1.iter());
        }
        for (_, column, factor) in self.tableau.iterate_row(self.basic_variable_to_row[&basic]) {
            if column == basic {
                continue;
            }
            assert!(!factor.is_zero());
            let check_upper = factor.is_negative() ^ increasing;
            if check_upper && !self.variables[column].can_be_increased() {
                reasons.extend(self.variables[column].reasons.1);
            } else if !check_upper && !self.variables[column].can_be_decreased() {
                reasons.extend(self.variables[column].reasons.0);
            }
        }
        reasons
    }

    fn pivot_and_update(
        &mut self,
        old_basic: usize,
        value_diff: RationalWithDelta,
        new_basic: usize,
    ) {
        let old_row = self.basic_variable_to_row[&old_basic];
        assert!(!self.tableau.entry(old_row, new_basic).is_zero());
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
    use crate::{linear_expression::LinearExpression, variable_pool::Sort};

    fn expect_reason(got: Option<Clause>, mut expected: Vec<u32>) {
        let mut x: Vec<_> = got.unwrap().iter().map(|l| l.var() as u32).collect();
        x.sort();
        expected.sort();
        assert_eq!(x, expected);
    }

    use super::*;
    #[test]
    fn empty() {
        let mut solver = LPSolver::default();
        assert_eq!(solver.feasible(), None);
    }
    #[test]
    fn simple() {
        let mut pool = VariablePool::new();
        let var_x = pool.declare_variable("x".as_bytes().into(), Sort::Real);
        let var_y = pool.declare_variable("y".as_bytes().into(), Sort::Real);
        let x = LinearExpression::variable(var_x.id);
        let y = LinearExpression::variable(var_y.id);
        let var_t = pool.declare_variable("t".as_bytes().into(), Sort::Real);
        let mut solver = LPSolver::default();
        solver.append_row(var_t.id, 2 * x + y);
        solver.restrict_bounds_with_reason(
            var_t.id,
            Bounds {
                lower: Some(to_rat(0).into()),
                upper: Some(to_rat(0).into()),
            },
            (Some(11.into()), Some(12.into())),
        );
        solver.restrict_bounds_with_reason(
            var_x.id,
            Bounds {
                lower: Some(to_rat(2).into()),
                upper: None,
            },
            (Some(13.into()), Some(14.into())),
        );
        assert_eq!(solver.feasible(), None);
        solver.restrict_bounds_with_reason(
            var_y.id,
            Bounds {
                lower: Some((to_rat(2)).into()),
                upper: None,
            },
            (Some(15.into()), Some(16.into())),
        );
        expect_reason(solver.feasible(), vec![12, 13, 15]);
        // Query again.
        expect_reason(solver.feasible(), vec![12, 13, 15]);
    }
    #[test]
    fn simple_other() {
        let mut pool = VariablePool::new();
        let var_x = pool.declare_variable("x".as_bytes().into(), Sort::Real);
        let var_y = pool.declare_variable("y".as_bytes().into(), Sort::Real);
        let x = LinearExpression::variable(var_x.id);
        let y = LinearExpression::variable(var_y.id);
        let var_t = pool.declare_variable("t".as_bytes().into(), Sort::Real);
        let mut solver = LPSolver::default();
        solver.append_row(var_t.id, x + y);
        solver.restrict_bounds_with_reason(
            var_t.id,
            Bounds {
                lower: Some(to_rat(4).into()),
                upper: Some(to_rat(4).into()),
            },
            (Some(11.into()), Some(12.into())),
        );
        solver.restrict_bounds_with_reason(
            var_x.id,
            Bounds {
                lower: None,
                upper: Some(to_rat(2).into()),
            },
            (Some(13.into()), Some(14.into())),
        );
        solver.restrict_bounds_with_reason(
            var_y.id,
            Bounds {
                lower: None,
                upper: Some(to_rat(-2).into()),
            },
            (Some(15.into()), Some(16.into())),
        );
        expect_reason(solver.feasible(), vec![11, 14, 16]);
    }
}
