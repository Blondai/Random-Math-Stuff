//! This module contains the [`Signum`] enum and its implementations.

use std::fmt::{Display, Formatter};

/// An enum for the [`Signum`] of a number.
///
/// The number needs to implement the [`Signable`] trait.
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Signum {
    /// The number is greater than zero.
    Positive,

    /// The number is smaller than zero.
    Negative,

    ///  The number is zero.
    Zero,
}

impl Signum {
    /// Returns the [`Signum`] of a [`Signable`].
    ///
    /// # Returns
    ///
    /// * [`Signum::Positive`] - The number is greater than [`Signable::zero`].
    /// * [`Signum::Negative`] - The number is smaller than [`Signable::zero`].
    /// * [`Signum::Zero`] - The number is [`Signable::zero`].
    #[inline]
    pub fn sign<T: Signable>(num: T) -> Self {
        if num > T::zero() {
            // Greater than zero
            Self::Positive
        } else if num < T::zero() {
            // Less than zero
            Self::Negative
        } else {
            // Equal to zero
            Self::Zero
        }
    }
}

impl Display for Signum {
    fn fmt(&self, format: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Positive => write!(format, "Positive"),
            Self::Negative => write!(format, "Negative"),
            Self::Zero => write!(format, "Zero"),
        }
    }
}

/// A trait for giving number a [`Signum`].
pub trait Signable: PartialOrd {
    /// Returns zero.
    fn zero() -> Self;
}

/// Easily implements the [`Signable`] trait.
macro_rules! impl_signable {
    ($T:ty, $Num:expr) => {
        impl Signable for $T {
            #[inline]
            fn zero() -> Self {
                $Num
            }
        }
    }
}

impl_signable!(f64, 0_f64);
impl_signable!(f32, 0_f32);
impl_signable!(i128, 0_i128);
impl_signable!(i64, 0_i64);
impl_signable!(i32, 0_i32);
impl_signable!(i16, 0_i16);
impl_signable!(i8, 0_i8);
impl_signable!(isize, 0_isize);
impl_signable!(u128, 0_u128);
impl_signable!(u64, 0_u64);
impl_signable!(u32, 0_u32);
impl_signable!(u16, 0_u16);
impl_signable!(u8, 0_u8);
impl_signable!(usize, 0_usize);
