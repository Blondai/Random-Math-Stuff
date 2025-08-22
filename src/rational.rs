use crate::Integer;

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::{Display, Formatter};
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
/// A struct for calculations involving rational numbers.
/// Stores values in form of sign, numerator and denominator.
pub struct Rational<T: Integer> {
    /// The numerator of the rational number.
    ///
    /// This field carries the sign of the number.
    numerator: T,

    /// The denominator of the rational number.
    ///
    /// This value is always kept positive to ensure a canonical representation.
    denominator: T,
}

impl<T: Integer> Display for Rational<T> {
    /// Formats the rational number.
    ///
    /// The signage is handled.
    fn fmt(&self, format: &mut Formatter<'_>) -> std::fmt::Result {
        if self.numerator >= T::zero() {
            write!(format, "{} / {}", self.numerator, self.denominator)
        } else {
            write!(format, "- {} / {}", -self.numerator, self.denominator)
        }
    }
}

impl<T: Integer> Rational<T> {
    /// Attempts to create a new [`Rational`] instance, returning an error on failure.
    ///
    /// The rational number is simplified to its canonical form.
    ///
    /// # Errors
    ///
    /// Returns [`RationalError::DivisionByZero`] if the denominator is zero.
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Rational;
    /// let one_third = Rational::new(1, 3);
    /// assert_eq!(one_third.numerator(), 1);
    /// assert_eq!(one_third.denominator(), 3);
    ///
    /// // Simplified
    /// let minus_two_fifths = Rational::new(-4, 10);
    /// assert_eq!(minus_two_fifths.numerator(), -2);
    /// assert_eq!(minus_two_fifths.denominator(), 5);
    ///
    /// // Sign moved to numerator
    /// let another_minus_two_fifths = Rational::new(2, -5);
    /// assert_eq!(another_minus_two_fifths.numerator(), -2);
    /// assert_eq!(another_minus_two_fifths.denominator(), 5);
    /// ```
    pub fn try_new(mut numerator: T, mut denominator: T) -> Result<Self, RationalError> {
        if denominator == T::zero() {
            return Err(RationalError::DivisionByZero);
        }

        // Sign to numerator
        if denominator < T::zero() {
            numerator = -numerator;
            denominator = -denominator;
        }

        let gcd: T = T::gcd(numerator, denominator);

        Ok(Self {
            numerator: numerator / gcd,
            denominator: denominator / gcd,
        })
    }

    /// Creates a new [`Rational`] instance.
    ///
    /// This calls `unwrap` on the [`Rational::try_new`] method
    ///
    /// # Panics
    ///
    /// When `denominator` is zero.
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Rational;
    /// let rational = Rational::new(2, 4);
    /// assert_eq!(rational.numerator(), 1);
    /// assert_eq!(rational.denominator(), 2);
    /// ```
    ///
    /// ```should_panic
    /// use random_math_stuff::Rational;
    /// let rational = Rational::new(1, 0);
    /// ```
    #[inline]
    pub fn new(numerator: T, denominator: T) -> Self {
        Self::try_new(numerator, denominator).unwrap()
    }

    /// Returns the additive identity, 0 / 1.
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Rational;
    /// let rational = Rational::zero();
    /// assert_eq!(rational, Rational::new(0, 1));
    /// assert_eq!(rational.numerator(), 0);
    /// assert_eq!(rational.denominator(), 1);
    /// ```
    #[inline]
    pub fn zero() -> Self {
        Self {
            numerator: T::zero(),
            denominator: T::one(),
        }
    }

    /// Returns the multiplicative identity, 1 / 1.
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Rational;
    /// let rational = Rational::one();
    /// assert_eq!(rational, Rational::new(1, 1));
    /// assert_eq!(rational.numerator(), 1);
    /// assert_eq!(rational.denominator(), 1);
    /// ```
    #[inline]
    pub fn one() -> Self {
        Self {
            numerator: T::one(),
            denominator: T::one(),
        }
    }

    /// Returns the (signed) numerator of the rational number.
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Rational;
    /// let rational = Rational::new(3, 7);
    /// assert_eq!(rational.numerator(), 3)
    /// ```
    #[inline]
    pub fn numerator(&self) -> T {
        self.numerator
    }

    /// Returns the denominator of the rational number.
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Rational;
    /// let rational = Rational::new(3, 7);
    /// assert_eq!(rational.denominator(), 7)
    /// ```
    #[inline]
    pub fn denominator(&self) -> T {
        self.denominator
    }

    /// Converts two rational numbers to have a common denominator.
    ///
    /// This method finds the least common multiple (LCM) of the two denominators
    /// and returns a pair of new [`Rational`] numbers that are equivalent to the
    /// originals but share the same denominator.
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::{Rational, Integer};
    /// let a = Rational::new(1, 2);
    /// let b = Rational::new(2, 3);
    ///
    /// let (c, d) = a.common_denominator(&b);
    ///
    /// // a = 1/2, c = 3/6
    /// assert_eq!(c.numerator(), 3);
    /// assert_eq!(c.denominator(), 6);
    ///
    /// // b = 2/3, d = 4/6
    /// assert_eq!(d.numerator(), 4);
    /// assert_eq!(d.denominator(), 6);
    /// ```
    pub fn common_denominator(&self, other: &Self) -> (Self, Self) {
        let lcm: T = self.denominator.lcm(other.denominator);
        let factor_1: T = lcm / self.denominator;
        let factor_2: T = lcm / other.denominator;

        (
            Self {
                numerator: self.numerator * factor_1,
                denominator: lcm,
            },
            Self {
                numerator: other.numerator * factor_2,
                denominator: lcm,
            },
        )
    }

    /// Simplifies a rational number by dividing the numerator and denominator by the gcd.
    ///
    /// This is used internally after arithmetic operations.
    #[inline]
    fn simplify(&mut self) {
        let gcd: T = self.numerator.gcd(self.denominator);

        self.numerator = self.numerator / gcd;
        self.denominator = self.denominator / gcd;
    }

    /// Inverts a rational number.
    ///
    /// This will automatically hand the sign from the old numerator to the new one.
    ///
    /// (a / b).inv() = b / a
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Rational;
    /// let rational = Rational::new(1, 3);
    /// assert_eq!(rational.inv(), Rational::new(3, 1));
    ///
    /// let rational = Rational::new(-5, 2);
    /// assert_eq!(rational.inv(), Rational::new(-2, 5));
    /// ```
    #[inline]
    pub fn inv(&self) -> Self {
        Self::new(self.denominator, self.numerator)
    }

    /// Calculates the absolute value of a rational number.
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Rational;
    /// let rational = Rational::new(1, 3);
    /// assert_eq!(rational.abs(), Rational::new(1, 3));
    ///
    /// let rational = Rational::new(-5, 2);
    /// assert_eq!(rational.abs(), Rational::new(5, 2));
    /// ```
    #[inline]
    pub fn abs(&self) -> Self {
        match self.numerator >= T::zero() {
            true => Self::new(self.numerator, self.denominator),
            false => Self::new(-self.numerator, self.denominator),
        }
    }

    /// Raises a rational number to an integer power.
    ///
    /// # Examples
    ///
    /// ```
    /// use random_math_stuff::Rational;
    /// let rational = Rational::new(1, 2).powi(2);
    /// assert_eq!(rational, Rational::new(1, 4));
    ///
    /// let rational = Rational::new(-2, 3).powi(4);
    /// assert_eq!(rational, Rational::new(16, 81));
    ///
    /// let rational = Rational::new(2, 3).powi(-2);
    /// assert_eq!(rational, Rational::new(9, 4));
    /// ```
    pub fn powi(&self, power: i32) -> Self {
        if power > 0_i32 {
            Self::new(
                self.numerator.pow(power as u32),
                self.denominator.pow(power as u32),
            )
        } else if power < 0_i32 {
            Self::new(
                self.denominator.pow(power.abs() as u32),
                self.numerator.pow(power.abs() as u32),
            )
        } else {
            Rational::one()
        }
    }
}

impl<T: Integer> PartialOrd for Rational<T> {
    /// Compares two rational numbers.
    ///
    /// It uses cross-multiplication to avoid floating-point inaccuracies.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // To compare a/b and c/d, we compare a*d and c*b
        // Denominators are always positive
        Some((self.numerator * other.denominator).cmp(&(other.numerator * self.denominator)))
    }
}

impl<T: Integer> Ord for Rational<T> {
    /// Compares two rational numbers.
    ///
    /// It uses cross-multiplication to avoid floating-point inaccuracies.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::cmp::Ordering;
    /// # use random_math_stuff::Rational;
    /// let rational_1 = Rational::new(1, 2);
    /// let rational_2 = Rational::new(1, 2);
    /// assert_eq!(rational_1.cmp(&rational_2), Ordering::Equal);
    ///
    /// let rational_1 = Rational::new(7, 8);
    /// let rational_2 = Rational::new(8, 9);
    /// assert_eq!(rational_1.cmp(&rational_2), Ordering::Less);
    ///
    /// let rational_1 = Rational::new(-1, 3);
    /// let rational_2 = Rational::new(-1, 2);
    /// assert_eq!(rational_1.cmp(&rational_2), Ordering::Greater);
    /// ```
    ///
    /// ```
    /// # use random_math_stuff::Rational;
    /// assert!(Rational::new(1, 2) < Rational::new(3, 4));
    /// assert!(Rational::new(1, 2) <= Rational::new(1, 2));
    /// assert!(Rational::new(7, 8) > Rational::new(6, 8));
    /// assert!(Rational::new(-1, 2) >= Rational::new(-2, 3));
    /// ```
    fn cmp(&self, other: &Self) -> Ordering {
        (self.numerator * other.denominator).cmp(&(other.numerator * self.denominator))
    }
}

impl<T: Integer> Mul for Rational<T> {
    type Output = Self;

    /// Multiplies two rational number.
    ///
    /// a / b * c / d = (a * c) / (b * d)
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Rational;
    /// let rational_1 = Rational::new(3, 4);
    /// let rational_2 = Rational::new(7, 5);
    /// assert_eq!(rational_1 * rational_2, Rational::new(21, 20));
    ///
    /// let rational_1 = Rational::new(1, 5);
    /// let rational_2 = Rational::new(2, 6);
    /// assert_eq!(rational_1 * rational_2, Rational::new(1, 15));
    /// ```
    fn mul(self, other: Self) -> Self::Output {
        Self::new(
            self.numerator * other.numerator,
            self.denominator * other.denominator,
        )
    }
}

impl<T: Integer> MulAssign for Rational<T> {
    /// Multiplies two rational number.
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Rational;
    /// let mut rational = Rational::new(3, 4);
    /// rational *= Rational::new(7, 5);
    /// assert_eq!(rational, Rational::new(21, 20));
    ///
    /// let mut rational = Rational::new(1, 5);
    /// rational *= Rational::new(2, 6);
    /// assert_eq!(rational, Rational::new(1, 15));
    /// ```
    fn mul_assign(&mut self, other: Self) {
        self.numerator = self.numerator * other.numerator;
        self.denominator = self.denominator * other.denominator;

        self.simplify();
    }
}

impl<T: Integer> Div for Rational<T> {
    type Output = Self;

    /// Divides a rational number by another.
    ///
    /// (a / b) / (c / d) = (a * d) / (b * c)
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Rational;
    /// let rational_1 = Rational::new(-5, 6);
    /// let rational_2 = Rational::new(2, 3);
    /// assert_eq!(rational_1 / rational_2, Rational::new(-5, 4));
    ///
    /// let rational_1 = Rational::new(2, 7);
    /// let rational_2 = Rational::new(1, 8);
    /// assert_eq!(rational_1 / rational_2, Rational::new(16, 7));
    /// ```
    fn div(self, other: Self) -> Self::Output {
        Self::new(
            self.numerator * other.denominator,
            self.denominator * other.numerator,
        )
    }
}

impl<T: Integer> DivAssign for Rational<T> {
    /// Divides a rational number by another.
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Rational;
    /// let mut rational = Rational::new(-5, 6);
    /// rational /= Rational::new(2, 3);
    /// assert_eq!(rational, Rational::new(-5, 4));
    ///
    /// let mut rational = Rational::new(2, 7);
    /// rational /= Rational::new(1, 8);
    /// assert_eq!(rational, Rational::new(16, 7));
    /// ```
    fn div_assign(&mut self, other: Self) {
        self.numerator = self.numerator * other.denominator;
        self.denominator = self.denominator * other.numerator;

        self.simplify();
    }
}

impl<T: Integer> Add for Rational<T> {
    type Output = Self;

    /// Adds two rational numbers.
    ///
    /// This brings them to the same denominator and adds the resulting nominators.
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Rational;
    /// let rational_1 = Rational::new(3, 4);
    /// let rational_2 = Rational::new(1, 2);
    /// assert_eq!(rational_1 + rational_2, Rational::new(5, 4));
    ///
    /// let rational_1 = Rational::new(1, 2);
    /// let rational_2 = Rational::new(7, 5);
    /// assert_eq!(rational_1 + rational_2, Rational::new(19, 10));
    /// ```
    fn add(self, other: Self) -> Self::Output {
        let (rational_1, rational_2): (Self, Self) = self.common_denominator(&other);

        Self::new(
            rational_1.numerator + rational_2.numerator,
            rational_1.denominator,
        )
    }
}

impl<T: Integer> AddAssign for Rational<T> {
    /// Adds two rational numbers.
    ///
    /// This method brings them to the same denominator and adds the resulting nominators.
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Rational;
    /// let mut rational = Rational::new(3, 4);
    /// rational += Rational::new(1, 2);
    /// assert_eq!(rational, Rational::new(5, 4));
    ///
    /// let mut rational = Rational::new(1, 2);
    /// rational += Rational::new(7, 5);
    /// assert_eq!(rational, Rational::new(19, 10));
    /// ```
    fn add_assign(&mut self, other: Self) {
        let lcm: T = self.denominator.lcm(other.denominator);

        self.numerator =
            self.numerator * lcm / self.denominator + other.numerator * lcm / other.denominator;
        self.denominator = lcm;

        self.simplify();
    }
}

// Negation
impl<T: Integer> Neg for Rational<T> {
    type Output = Self;

    /// Negates a rational number.
    ///
    /// This simply negates the numerator.
    ///
    /// # Examples
    ///
    /// ```
    /// use random_math_stuff::Rational;
    /// let rational = -Rational::new(1, 2);
    /// assert_eq!(rational, Rational::new(-1, 2));
    ///
    /// let rational = -Rational::new(-2, 5);
    /// assert_eq!(rational, Rational::new(2, 5));
    /// ```
    fn neg(self) -> Self::Output {
        // Since the rational is already canonical, we only need to flip the numerator's sign.
        // The denominator is unchanged and stays positive.
        // We can construct the struct directly without calling `new()`.
        Self {
            numerator: -self.numerator,
            denominator: self.denominator,
        }
    }
}

impl<T: Integer> Sub for Rational<T> {
    type Output = Self;

    /// Subtracts a rational number from another.
    ///
    /// This method brings them to the same denominator and subtracts the resulting nominators.
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Rational;
    /// let rational_1 = Rational::new(3, 4);
    /// let rational_2 = Rational::new(1, 2);
    /// assert_eq!(rational_1 - rational_2, Rational::new(1, 4));
    ///
    /// let rational_1 = Rational::new(1, 2);
    /// let rational_2 = Rational::new(7, 5);
    /// assert_eq!(rational_1 - rational_2, Rational::new(-9, 10));
    /// ```
    fn sub(self, other: Self) -> Self::Output {
        let rational_1: Self = self;
        let rational_2: Self = -other;

        rational_1 + rational_2
    }
}

impl<T: Integer> SubAssign for Rational<T> {
    /// Subtracts and assigns the result.
    ///
    /// This is implemented as `*self += -other;`
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Rational;
    /// let mut rational = Rational::new(3, 4);
    /// rational -= Rational::new(1, 2);
    /// assert_eq!(rational, Rational::new(1, 4));
    ///
    /// let mut rational = Rational::new(1, 2);
    /// rational -= Rational::new(7, 5);
    /// assert_eq!(rational, Rational::new(-9, 10));
    /// ```
    fn sub_assign(&mut self, other: Self) {
        *self += -other;
    }
}

impl<T: Integer + Into<f64>> Rational<T> {
    /// Evaluates a rational number to its floating point representation.
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Rational;
    /// let r = Rational::new(1, 2);
    /// assert!((r.eval() - 0.5).abs() < f64::EPSILON);
    ///
    /// let one_third = Rational::new(1, 3);
    /// assert!((one_third.eval() - 1.0/3.0).abs() < f64::EPSILON);
    /// ```
    pub fn eval(&self) -> f64 {
        self.numerator.into() / self.denominator.into()
    }
}

/// Describes errors that can occur when creating a `Rational` number.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum RationalError {
    /// Occurs when attempting to create a rational number with a zero denominator.
    DivisionByZero,
}

impl Display for RationalError {
    fn fmt(&self, format: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            RationalError::DivisionByZero => write!(format, "denominator cannot be zero"),
        }
    }
}

impl Error for RationalError {}
