use std::collections::BTreeMap;
use std::ops::{Add, Mul, Sub};

use num_rational::BigRational;
use num_traits::identities::One;
use num_traits::FromPrimitive;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct LinearExpression(Vec<(usize, BigRational)>);

impl IntoIterator for LinearExpression {
    type Item = (usize, BigRational);
    type IntoIter = <Vec<(usize, BigRational)> as IntoIterator>::IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl Mul<LinearExpression> for i32 {
    type Output = LinearExpression;
    fn mul(self, rhs: LinearExpression) -> Self::Output {
        LinearExpression(
            rhs.0
                .iter()
                .map(|(i, v)| (*i, v * BigRational::from_i32(self).unwrap()))
                .filter(|(_, x)| *x != BigRational::default())
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
        LinearExpression(
            data.into_iter()
                .filter(|(_, x)| *x != BigRational::default())
                .collect(),
        )
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
        LinearExpression(
            data.into_iter()
                .filter(|(_, x)| *x != BigRational::default())
                .collect(),
        )
    }
}

#[derive(Default)]
pub struct SymbolicVariableGenerator {
    names: Vec<String>,
}

impl SymbolicVariableGenerator {
    pub fn var(&mut self, name: &str) -> LinearExpression {
        let id = self.names.len();
        self.names.push(name.to_string());

        LinearExpression(vec![(id, One::one())])
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn add_linear_expression() {
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
