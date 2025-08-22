//! This module contains the implementation of the [`Numeric`] trait and its implementation macro.

use std::fmt::Display;
use std::ops::{Add, Div, Mul, Neg, Sub};

/// A trait for generic numeric types.
///
/// This trait bounds types that can be used in numeric computations.
/// It requires the type to support basic arithmetic operations.
/// `Add`, `Sub`, `Mul` and `Div` should return a number of the same type.
/// It needs to have additive and multiplicative identities.
///
/// This trait is automatically implemented for the following types:
///
/// * `f64`
/// * `f32`
/// * `i128`
/// * `i64`
/// * `i32`
/// * `i16`
/// * `i8`
/// * `isize`
pub trait Numeric:
    Copy
    + Display
    + PartialEq
    + PartialOrd<Self>
    + Add<Self, Output = Self>
    + Sub<Self, Output = Self>
    + Neg<Output = Self>
    + Mul<Self, Output = Self>
    + Div<Self, Output = Self>
{
    /// Returns the additive identity element of `Self`, i.e., `0`.
    fn zero() -> Self;

    /// Returns the multiplicative identity element of `Self`, i.e., `1`.
    fn one() -> Self;
}

/// Implements the [`Numeric`] trait for a given type.
///
/// This macro reduces boilerplate code by generating the [`Numeric`] implementation for a specified type.
#[macro_export]
macro_rules! impl_numeric {
    ($T:ty, $zero:expr, $one:expr) => {
        impl Numeric for $T {
            fn zero() -> $T {
                $zero
            }

            fn one() -> $T {
                $one
            }
        }
    };
}

impl_numeric!(f64, 0.0, 1.0);
impl_numeric!(f32, 0.0, 1.0);
impl_numeric!(i128, 0, 1);
impl_numeric!(i64, 0, 1);
impl_numeric!(i32, 0, 1);
impl_numeric!(i16, 0, 1);
impl_numeric!(i8, 0, 1);
impl_numeric!(isize, 0, 1);
