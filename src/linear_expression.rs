use std::collections::{BTreeMap, HashMap};
use std::ops::{Add, Deref, Mul, Sub};

use num_rational::BigRational;
use num_traits::identities::One;
use num_traits::{FromPrimitive, Zero};

use crate::lp_solver::LPSolver;
use crate::types::VariableID;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct LinearExpression(Vec<(VariableID, BigRational)>);

impl LinearExpression {
    pub fn variable(var: VariableID) -> LinearExpression {
        LinearExpression(vec![(var, One::one())])
    }
    pub fn iter(&self) -> std::slice::Iter<'_, (VariableID, BigRational)> {
        self.0.iter()
    }
}

impl IntoIterator for LinearExpression {
    type Item = (VariableID, BigRational);
    type IntoIter = <Vec<(VariableID, BigRational)> as IntoIterator>::IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl Mul<LinearExpression> for i32 {
    type Output = LinearExpression;
    fn mul(self, rhs: LinearExpression) -> Self::Output {
        // TODO only filter based on "self"
        LinearExpression(
            rhs.0
                .iter()
                .map(|(i, v)| (*i, v * BigRational::from_i32(self).unwrap()))
                .filter(|(_, x)| !x.is_zero())
                .collect::<Vec<_>>(),
        )
    }
}

impl Mul<LinearExpression> for BigRational {
    type Output = LinearExpression;
    fn mul(self, rhs: LinearExpression) -> Self::Output {
        // TODO only filter based on "self"
        LinearExpression(
            rhs.0
                .iter()
                .map(|(i, v)| (*i, v * self.clone()))
                .filter(|(_, x)| !x.is_zero())
                .collect::<Vec<_>>(),
        )
    }
}

impl Add for LinearExpression {
    type Output = LinearExpression;
    fn add(self, rhs: Self) -> Self::Output {
        // TODO it should be possible to do this with just joining two iterators...

        let mut data = self.into_iter().collect::<BTreeMap<_, _>>();
        for (i, y) in rhs {
            data.entry(i)
                .and_modify(|x| *x = x.clone() + y.clone())
                .or_insert(y);
        }
        LinearExpression(data.into_iter().filter(|(_, x)| !x.is_zero()).collect())
    }
}

impl Sub for LinearExpression {
    type Output = LinearExpression;
    fn sub(self, rhs: Self) -> Self::Output {
        // TODO it should be possible to do this with just joining two iterators...

        let mut data = self.into_iter().collect::<BTreeMap<_, _>>();
        for (i, y) in rhs {
            data.entry(i)
                .and_modify(|x| *x = x.clone() - y.clone())
                .or_insert(y);
        }
        LinearExpression(data.into_iter().filter(|(_, x)| !x.is_zero()).collect())
    }
}

#[cfg(test)]
pub mod test {
    use crate::smt_solver::Variable;

    use super::*;

    #[derive(Default)]
    pub struct SymbolicVariableGenerator {
        id_to_name: Vec<String>,
        name_to_id: HashMap<String, VariableID>,
    }

    impl SymbolicVariableGenerator {
        pub fn var(&mut self, name: &str) -> LinearExpression {
            LinearExpression(vec![(self.id(name), One::one())])
        }
        pub fn id(&mut self, name: &str) -> VariableID {
            *self.name_to_id.entry(name.to_string()).or_insert_with(|| {
                let id = self.id_to_name.len() as VariableID;
                self.id_to_name.push(name.to_string());
                id
            })
        }
        #[cfg(debug_assertions)]
        pub fn transfer_names(&self, solver: &mut LPSolver) {
            for (id, name) in self.id_to_name.iter().enumerate() {
                solver.set_variable_name(id as VariableID, name.clone());
            }
        }
    }

    #[test]
    fn simple() {
        let mut g = SymbolicVariableGenerator::default();
        let x = g.var("x");
        let y = g.var("y");

        assert_eq!(x.clone() + x.clone(), 2 * x.clone());
        assert_eq!(0 * x.clone(), Default::default());
        assert_eq!(x.clone() - x.clone(), Default::default());
        assert_eq!(3 * x.clone() + y.clone(), y.clone() + 3 * x.clone());
        assert_eq!(3 * (x.clone() + y.clone()), 3 * y.clone() + 3 * x.clone());
    }
}
