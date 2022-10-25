use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use std::cmp::{max, min};
use std::fmt::{self, Display};
use std::ops::{Add, AddAssign, Div, Mul, Not, Sub, SubAssign};

use crate::variable_pool::{Sort, Variable, VariableID, VariablePool};

// TODO could also state guarantee that never zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Literal(VariableID);

impl Literal {
    pub fn var(&self) -> VariableID {
        self.0.abs()
    }
    pub fn polarity(&self) -> bool {
        self.0 > 0
    }
}

pub fn format_literal(l: &Literal, pool: &VariablePool) -> String {
    format!(
        "{}{}",
        if l.polarity() { "" } else { "¬" },
        pool.name(l.var())
    )
}

impl From<Variable> for Literal {
    fn from(v: Variable) -> Self {
        assert!(v.sort == Sort::Bool);
        Literal::from(v.id)
    }
}

impl Not for Literal {
    type Output = Literal;

    fn not(self) -> Self {
        Literal(-self.0)
    }
}

impl From<VariableID> for Literal {
    fn from(var: VariableID) -> Self {
        Self(var)
    }
}

pub type Clause = Vec<Literal>;

pub fn format_clause(clause: &Clause, pool: &VariablePool) -> String {
    clause
        .iter()
        .map(|l| format_literal(l, pool))
        .collect::<Vec<_>>()
        .join(" ∨ ")
}

#[derive(Default, Clone, PartialEq)]
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
    pub fn format(&self, var_name: &str) -> String {
        let left = if let Some(l) = &self.lower {
            format!("{:>8} <=", format!("{}", l))
        } else {
            format!("{:8}   ", "")
        };
        let right = if let Some(u) = &self.upper {
            format!("<= {:<8}", format!("{}", u))
        } else {
            format!("   {:8}", "")
        };
        format!("{left} {:^4} {right}", var_name)
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
        (a, b) => a.or(b),
    }
}

fn combine_upper(
    a: Option<RationalWithDelta>,
    b: Option<RationalWithDelta>,
) -> Option<RationalWithDelta> {
    match (a, b) {
        (Some(x), Some(y)) => Some(min(x, y)),
        (a, b) => a.or(b),
    }
}

pub fn to_rat(x: i32) -> BigRational {
    BigRational::from_integer(BigInt::from(x))
}

#[derive(Clone, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct RationalWithDelta {
    value: BigRational,
    delta: BigRational,
}

impl From<BigRational> for RationalWithDelta {
    fn from(x: BigRational) -> Self {
        RationalWithDelta {
            value: x,
            delta: Default::default(),
        }
    }
}

impl RationalWithDelta {
    pub fn delta() -> RationalWithDelta {
        RationalWithDelta {
            value: Default::default(),
            delta: One::one(),
        }
    }
    #[inline]
    pub fn is_zero(&self) -> bool {
        self.value.is_zero() && self.delta.is_zero()
    }
    #[inline]
    pub fn is_positive(&self) -> bool {
        self.value.is_positive() || (self.value.is_zero() && self.delta.is_positive())
    }
    #[inline]
    pub fn is_negative(&self) -> bool {
        self.value.is_negative() || (self.value.is_zero() && self.delta.is_negative())
    }
}

impl Add for RationalWithDelta {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Self {
            value: self.value + rhs.value,
            delta: self.delta + rhs.delta,
        }
    }
}
impl AddAssign for RationalWithDelta {
    fn add_assign(&mut self, rhs: Self) {
        self.value += rhs.value;
        self.delta += rhs.delta;
    }
}
impl Sub for RationalWithDelta {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        Self {
            value: self.value - rhs.value,
            delta: self.delta - rhs.delta,
        }
    }
}
impl SubAssign for RationalWithDelta {
    fn sub_assign(&mut self, rhs: Self) {
        self.value -= rhs.value;
        self.delta -= rhs.delta;
    }
}

impl Mul<BigRational> for RationalWithDelta {
    type Output = Self;
    fn mul(self, rhs: BigRational) -> Self::Output {
        Self {
            value: self.value * rhs.clone(),
            delta: self.delta * rhs,
        }
    }
}

impl Div<BigRational> for RationalWithDelta {
    type Output = Self;

    fn div(self, rhs: BigRational) -> Self::Output {
        Self {
            value: self.value / rhs.clone(),
            delta: self.delta / rhs,
        }
    }
}

impl Display for RationalWithDelta {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.delta.is_zero() {
            write!(f, "{}", self.value)
        } else {
            write!(f, "{} + {}d", self.value, self.delta)
        }
    }
}

#[cfg(test)]
mod test {
    use crate::types::RationalWithDelta;

    #[test]
    pub fn comparison() {
        let d = RationalWithDelta::delta();
        let zero = RationalWithDelta::default();
        assert!(d > zero);
        assert!(zero == zero);
        assert!(d == d);
        assert!(zero.clone() - d.clone() < zero);
        assert!(zero.clone() + d.clone() == zero + d);
    }
}
