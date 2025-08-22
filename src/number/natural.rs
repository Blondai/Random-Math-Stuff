//! This module contains the implementation of the [`Natural`] trait and its implementation macro.

use std::fmt::Display;
use std::ops::{Add, Div, Mul, Rem, Sub};

/// A trait for generic natural number types.
///
/// This trait bounds types that can be used in numeric computations.
/// It requires the type to support basic arithmetic operations.
/// `Add`, `Sub`, `Mul` and `Div` should return a number of the same type.
/// It needs to have additive and multiplicative identities.
///
/// This trait is automatically implemented for the following types:
///
/// * `u128`
/// * `u64`
/// * `u32`
/// * `u16`
/// * `u8`
/// * `usize`
pub trait Natural:
    Copy
    + Display
    + PartialEq
    + PartialOrd<Self>
    + Add<Self, Output = Self>
    + Sub<Self, Output = Self>
    + Rem<Output = Self>
    + Mul<Self, Output = Self>
    + Div<Self, Output = Self>
{
    /// Returns the additive identity element of `Self`, i.e., `0`.
    fn zero() -> Self;

    /// Returns the multiplicative identity element of `Self`, i.e., `1`.
    fn one() -> Self;

    /// Calculates the greatest common divisor (GCD) of two numbers using the Euclidean algorithm.
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Integer;
    /// assert_eq!(48.gcd(18), 6);
    /// ```
    fn gcd(self, other: Self) -> Self {
        let mut number_1: Self = self;
        let mut number_2: Self = other;

        while number_2 != Self::zero() {
            let temp: Self = number_2;
            number_2 = number_1 % number_2;
            number_1 = temp;
        }
        number_1
    }

    /// Calculates the least common multiple (LCM) of two numbers.
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Integer;
    /// assert_eq!(21.lcm(6), 42);
    /// ```
    fn lcm(self, other: Self) -> Self {
        if self == Self::zero() || other == Self::zero() {
            return Self::zero();
        }

        // a * b / gcd(a, b)
        (self * other) / self.gcd(other)
    }

    /// Checks whether two numbers are coprime.
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Integer;
    /// assert!(5.coprime(7));
    /// assert!(!2.coprime(4));
    /// ```
    fn coprime(self, other: Self) -> bool {
        self.gcd(other) == Self::one()
    }
}

/// Implements the [`Natural`] trait for a given type.
///
/// This macro reduces boilerplate code by generating the [`Natural`] implementation for a specified type.
#[macro_export]
macro_rules! impl_natural {
    ($T:ty, $zero:expr, $one:expr) => {
        impl Natural for $T {
            fn zero() -> $T {
                $zero
            }

            fn one() -> $T {
                $one
            }
        }
    };
}

impl_natural!(u128, 0, 1);
impl_natural!(u64, 0, 1);
impl_natural!(u32, 0, 1);
impl_natural!(u16, 0, 1);
impl_natural!(u8, 0, 1);
impl_natural!(usize, 0, 1);
