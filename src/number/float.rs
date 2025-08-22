//! This module contains the implementation of the [`Float`] trait and its implementation macro.

use std::fmt::Display;
use std::ops::{Add, Div, Mul, Neg, Sub};

/// A trait for generic float types.
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
pub trait Float:
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

/// Implements the [`Float`] trait for a given type.
///
/// This macro reduces boilerplate code by generating the [`Float`] implementation for a specified type.
#[macro_export]
macro_rules! impl_float {
    ($T:ty, $zero:expr, $one:expr) => {
        impl Float for $T {
            fn zero() -> $T {
                $zero
            }

            fn one() -> $T {
                $one
            }
        }
    };
}

impl_float!(f64, 0.0, 1.0);
impl_float!(f32, 0.0, 1.0);
