use num_rational::BigRational;
use std::ops::{Add, Mul, Sub};

struct RationalWithDelta {
    value: BigRational,
    delta: BigRational,
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
