use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Num, Signed, Zero};
use std::{
    fmt::{self, Display},
    ops::{Add, AddAssign, Div, Mul, Not, Sub, SubAssign},
};

pub type VariableID = i32;

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
    pub fn delta(v: BigRational) -> RationalWithDelta {
        RationalWithDelta {
            value: Default::default(),
            delta: v,
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
    use num_traits::identities::One;

    use crate::types::RationalWithDelta;

    #[test]
    pub fn comparison() {
        let d = RationalWithDelta::delta(One::one());
        let zero = RationalWithDelta::default();
        assert!(d > zero);
        assert!(zero == zero);
        assert!(d == d);
        assert!(zero.clone() - d.clone() < zero.clone());
        assert!(zero.clone() + d.clone() == zero.clone() + d.clone());
    }
}
