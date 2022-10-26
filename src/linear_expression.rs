use std::collections::BTreeMap;
use std::ops::{Add, Mul, Neg, Sub};

use num_rational::BigRational;
use num_traits::{FromPrimitive, One, Signed, Zero};

use crate::variable_pool::VariableID;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct LinearExpression(Vec<(VariableID, BigRational)>);

impl LinearExpression {
    pub fn variable(var: VariableID) -> LinearExpression {
        LinearExpression(vec![(var, One::one())])
    }
    pub fn iter(&self) -> std::slice::Iter<'_, (VariableID, BigRational)> {
        self.0.iter()
    }
    pub fn format<'a>(expr: impl IntoIterator<Item = (&'a str, &'a BigRational)>) -> String {
        expr.into_iter()
            .enumerate()
            .map(|(i, (var, f))| {
                let joiner = if f.is_negative() {
                    " - "
                } else if f.is_positive() && i > 0 {
                    " + "
                } else {
                    " "
                };
                let factor = if *f == BigRational::one() || *f == -BigRational::one() {
                    String::new()
                } else {
                    format!("{} ", f.abs())
                };
                format!("{joiner}{factor}{}", var)
            })
            .collect::<Vec<_>>()
            .join("")
    }
}

impl IntoIterator for LinearExpression {
    type Item = (VariableID, BigRational);
    type IntoIter = <Vec<(VariableID, BigRational)> as IntoIterator>::IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a> IntoIterator for &'a LinearExpression {
    type Item = &'a (VariableID, BigRational);
    type IntoIter = <&'a Vec<(VariableID, BigRational)> as IntoIterator>::IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
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
                .or_insert(-y);
        }
        LinearExpression(data.into_iter().filter(|(_, x)| !x.is_zero()).collect())
    }
}

impl Neg for LinearExpression {
    type Output = Self;

    fn neg(mut self) -> Self {
        for (_, value) in &mut self.0 {
            *value = value.clone().neg();
        }
        self
    }
}

#[cfg(test)]
pub mod test {
    use crate::variable_pool::{Sort, VariablePool};

    use super::*;

    #[test]
    fn simple() {
        let mut pool = VariablePool::new();
        let x =
            LinearExpression::variable(pool.declare_variable("x".as_bytes().into(), Sort::Real).id);
        let y =
            LinearExpression::variable(pool.declare_variable("y".as_bytes().into(), Sort::Real).id);

        assert_eq!(x.clone() + x.clone(), 2 * x.clone());
        assert_eq!(0 * x.clone(), Default::default());
        assert_eq!(x.clone() - x.clone(), Default::default());
        assert_eq!(3 * x.clone() + y.clone(), y.clone() + 3 * x.clone());
        assert_eq!(3 * (x.clone() + y.clone()), 3 * y.clone() + 3 * x.clone());
        assert_eq!(3 * (x.clone() - y.clone()), -(3 * y - 3 * x));
    }
}
