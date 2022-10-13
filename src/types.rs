use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Num, Signed, Zero};
use std::ops::{Add, AddAssign, Mul, Sub};

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

impl Mul<BigRational> for RationalWithDelta {
    type Output = Self;
    fn mul(self, rhs: BigRational) -> Self::Output {
        Self {
            value: self.value * rhs.clone(),
            delta: self.delta * rhs,
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
