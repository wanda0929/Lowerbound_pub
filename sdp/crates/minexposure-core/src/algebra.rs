use num_integer::Integer;
use serde::{Deserialize, Serialize};
use std::fmt;
use std::ops::{Add, AddAssign, Mul, Neg, Sub};
use std::str::FromStr;

/// A normalized exact rational with positive denominator.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
pub struct Rational {
    pub numerator: i128,
    pub denominator: i128,
}

impl Rational {
    pub const ZERO: Self = Self {
        numerator: 0,
        denominator: 1,
    };
    pub const ONE: Self = Self {
        numerator: 1,
        denominator: 1,
    };

    pub fn new(numerator: i128, denominator: i128) -> Self {
        assert_ne!(denominator, 0, "zero denominator");
        if numerator == 0 {
            return Self::ZERO;
        }
        let sign = if denominator < 0 { -1 } else { 1 };
        let gcd = numerator.gcd(&denominator);
        Self {
            numerator: sign * numerator / gcd,
            denominator: sign * denominator / gcd,
        }
    }

    pub fn abs(self) -> Self {
        Self::new(self.numerator.abs(), self.denominator)
    }
}

impl From<i64> for Rational {
    fn from(value: i64) -> Self {
        Self::new(i128::from(value), 1)
    }
}

impl Add for Rational {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Self::new(
            self.numerator * rhs.denominator + rhs.numerator * self.denominator,
            self.denominator * rhs.denominator,
        )
    }
}

impl Sub for Rational {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        self + -rhs
    }
}

impl Neg for Rational {
    type Output = Self;
    fn neg(self) -> Self::Output {
        Self::new(-self.numerator, self.denominator)
    }
}

impl Mul for Rational {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        Self::new(
            self.numerator * rhs.numerator,
            self.denominator * rhs.denominator,
        )
    }
}

impl fmt::Display for Rational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.denominator == 1 {
            write!(f, "{}", self.numerator)
        } else {
            write!(f, "{}/{}", self.numerator, self.denominator)
        }
    }
}

impl FromStr for Rational {
    type Err = String;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        if !value.contains('/')
            && let Some((whole, fractional)) = value.split_once('.')
        {
            if fractional.contains('.') || fractional.is_empty() {
                return Err(format!("invalid terminating decimal {value:?}"));
            }
            let negative = whole.starts_with('-');
            let unsigned_whole = whole.strip_prefix(['-', '+']).unwrap_or(whole);
            let digits = format!("{unsigned_whole}{fractional}");
            let mut numerator = digits
                .parse::<i128>()
                .map_err(|_| format!("invalid terminating decimal {value:?}"))?;
            if negative {
                numerator = -numerator;
            }
            let denominator = 10_i128
                .checked_pow(fractional.len() as u32)
                .ok_or_else(|| "terminating decimal has too many digits".to_string())?;
            return Ok(Self::new(numerator, denominator));
        }
        let (numerator, denominator) = value.split_once('/').unwrap_or((value, "1"));
        let numerator = numerator
            .parse::<i128>()
            .map_err(|_| format!("invalid rational numerator {numerator:?}"))?;
        let denominator = denominator
            .parse::<i128>()
            .map_err(|_| format!("invalid rational denominator {denominator:?}"))?;
        if denominator == 0 {
            return Err("rational denominator must be nonzero".into());
        }
        Ok(Self::new(numerator, denominator))
    }
}

/// Exact element `a + b*sqrt(2)` of Q(sqrt(2)).
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
pub struct Qsqrt2 {
    pub rational: Rational,
    pub sqrt2: Rational,
}

impl Qsqrt2 {
    pub const ZERO: Self = Self {
        rational: Rational::ZERO,
        sqrt2: Rational::ZERO,
    };
    pub fn new(rational: Rational, sqrt2: Rational) -> Self {
        Self { rational, sqrt2 }
    }

    pub fn conjugate(self) -> Self {
        Self::new(self.rational, -self.sqrt2)
    }
}

impl Add for Qsqrt2 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Self::new(self.rational + rhs.rational, self.sqrt2 + rhs.sqrt2)
    }
}

impl AddAssign for Qsqrt2 {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl Sub for Qsqrt2 {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        self + Self::new(-rhs.rational, -rhs.sqrt2)
    }
}

impl Neg for Qsqrt2 {
    type Output = Self;
    fn neg(self) -> Self::Output {
        Self::new(-self.rational, -self.sqrt2)
    }
}

impl Mul for Qsqrt2 {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        Self::new(
            self.rational * rhs.rational + Rational::new(2, 1) * self.sqrt2 * rhs.sqrt2,
            self.rational * rhs.sqrt2 + self.sqrt2 * rhs.rational,
        )
    }
}

impl From<i64> for Qsqrt2 {
    fn from(value: i64) -> Self {
        Self::new(Rational::from(value), Rational::ZERO)
    }
}

impl Qsqrt2 {
    pub fn to_f64(self) -> f64 {
        fn rational(value: Rational) -> f64 {
            value.numerator as f64 / value.denominator as f64
        }
        rational(self.rational) + rational(self.sqrt2) * 2.0_f64.sqrt()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn normalizes_and_multiplies_qsqrt2() {
        assert_eq!(Rational::new(-2, -4), Rational::new(1, 2));
        let x = Qsqrt2::new(Rational::new(1, 2), Rational::new(3, 4));
        assert_eq!(
            x * x.conjugate(),
            Qsqrt2::new(Rational::new(-7, 8), Rational::ZERO)
        );
        assert_eq!("-6/8".parse::<Rational>().unwrap(), Rational::new(-3, 4));
        assert_eq!("-7.125".parse::<Rational>().unwrap(), Rational::new(-57, 8));
    }
}
