use std::fmt::{Display, Formatter};
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use crate::Numeric;

/// Represents a complex number with a generic type `T`.
///
/// A complex number is a number that can be expressed in the form `a + bi`,
/// where `a` and `b` are real numbers, and `i` is the imaginary unit.
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct Complex<T> {
    /// The real part of the complex number.
    real: T,

    /// The imaginary part of the complex number.
    imag: T,
}

impl<T: Numeric> Display for Complex<T> {
    /// Formats the complex number.
    ///
    /// The signage is handled.
    fn fmt(&self, format: &mut Formatter<'_>) -> std::fmt::Result {
        let real_positive: bool = self.real >= T::zero();
        let imag_positive: bool = self.imag >= T::zero();

        match (real_positive, imag_positive) {
            (true, true) => write!(format, "{} + {} i", self.real, self.imag),
            (true, false) => write!(format, "{} - {} i", self.real, -self.imag),
            (false, true) => write!(format, "- {} + {} i", -self.real, self.imag),
            (false, false) => write!(format, "- {} - {} i", -self.real, -self.imag),
        }
    }
}

impl<T: Numeric> Complex<T> {
    /// Creates a new complex number from its real and imaginary parts.
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Complex;
    /// let z = Complex::new(1.0, 2.0);
    /// ```
    pub fn new(real: T, imag: T) -> Complex<T> {
        Self { real, imag }
    }

    /// Returns the additive identity, 0.
    pub fn zero() -> Complex<T> {
        let zero: T = T::zero();
        Self::new(zero, zero)
    }

    /// Returns the multiplicative identity, 1.
    pub fn one() -> Complex<T> {
        Self::new(T::one(), T::zero())
    }

    /// Returns the imaginary unit, _i_.
    pub fn i() -> Complex<T> {
        Self::new(T::zero(), T::one())
    }

    /// Returns the real part of the complex number.
    pub fn real(&self) -> T {
        self.real
    }

    /// Returns the imaginary part of the complex number.
    pub fn imag(&self) -> T {
        self.imag
    }

    /// Calculates the norm squared of a complex number.
    ///
    /// (a + b _i_).norm_sq() = a² + b²
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Complex;
    /// let z = Complex::new(1.0, 2.0);
    ///
    /// assert_eq!(z.norm_sq(), 5.0);
    /// ```
    pub fn norm_sq(&self) -> T {
        self.real * self.real + self.imag * self.imag
    }

    /// Inverts a complex number.
    ///
    /// 1 / (a + b _i_) = a / (a² + b²) - b / (a² + b²) _i_
    ///
    /// # Panics
    ///
    /// This function will panic if the norm of the complex number is zero
    /// (i.e., if called on `Complex::zero()`).
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Complex;
    /// let z = Complex::new(4.0, -3.0);
    ///
    /// assert_eq!(z * z.inv(), Complex::one());
    /// ```
    pub fn inv(&self) -> Complex<T> {
        let norm_sq: T = self.norm_sq();

        Self {
            real: self.real / norm_sq,
            imag: -self.imag / norm_sq,
        }
    }

    /// Conjugates a complex number.
    ///
    /// (a + b _i_).conj() = a - b _i_
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Complex;
    /// let z = Complex::new(1.0, 2.0);
    ///
    /// assert_eq!(z.conj(), Complex::new(1.0, -2.0));
    /// ```
    pub fn conj(&self) -> Complex<T> {
        Self {
            real: self.real,
            imag: -self.imag,
        }
    }

    /// Raises a complex number to an integer power.
    ///
    /// # Panics
    ///
    /// This function will panic if the norm of the complex number is zero and the exponent is negative
    /// (i.e., if called on `Complex::zero()`).
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Complex;
    /// let z = Complex::new(1.0, 2.0);
    ///
    /// assert_eq!(z.powi(2), z * z);
    /// assert_eq!(z.powi(-3), z.inv() * z.inv() * z.inv());
    /// ```
    pub fn powi(self, exp: i32) -> Complex<T> {
        if exp == 0_i32 {
            Complex::one()
        } else if exp < 0_i32 {
            self.inv().powi(-exp)
        } else {
            let mut power: Complex<T> = self;
            let mut result: Complex<T> = Complex::one();
            let mut exp: i32 = exp;

            // Using Squaring for O(log n) efficiency
            while exp > 0 {
                if exp % 2 == 1 {
                    result = result * power;
                }
                power = power * power;
                exp /= 2;
            }

            result
        }
    }
}

impl<T: Numeric> Add for Complex<T> {
    type Output = Self;

    /// Adds two complex numbers.
    ///
    /// (a + b _i_) + (c + d _i_) = (a + c) + (b + d) _i_
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Complex;
    /// let z_1 = Complex::new(1.0, 2.0);
    /// let z_2 = Complex::new(3.0, 4.0);
    ///
    /// assert_eq!(z_1 + z_2, Complex::new(4.0, 6.0));
    /// ```
    fn add(self, other: Self) -> Self::Output {
        Self {
            real: self.real + other.real,
            imag: self.imag + other.imag,
        }
    }
}

impl<T: Numeric> AddAssign for Complex<T> {
    /// Adds two complex numbers.
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Complex;
    /// let mut z = Complex::new(1.0, 2.0);
    /// z += Complex::new(3.0, 4.0);
    ///
    /// assert_eq!(z, Complex::new(4.0, 6.0));
    /// ```
    fn add_assign(&mut self, other: Self) {
        self.real = self.real + other.real;
        self.imag = self.imag + other.imag;
    }
}

impl<T: Numeric> Sub for Complex<T> {
    type Output = Self;

    /// Subtracts a complex number from another.
    ///
    /// (a + b _i_) - (c + d _i_) = (a - c) + (b - d) _i_
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Complex;
    /// let z_1 = Complex::new(1.0, 2.0);
    /// let z_2 = Complex::new(3.0, 4.0);
    ///
    /// assert_eq!(z_1 - z_2, Complex::new(-2.0, -2.0));
    /// ```
    fn sub(self, other: Self) -> Self::Output {
        Self {
            real: self.real - other.real,
            imag: self.imag - other.imag,
        }
    }
}

impl<T: Numeric> SubAssign for Complex<T> {
    /// Subtracts a complex number from another.
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Complex;
    /// let mut z = Complex::new(1.0, 2.0);
    /// z -= Complex::new(3.0, 4.0);
    ///
    /// assert_eq!(z, Complex::new(-2.0, -2.0));
    /// ```
    fn sub_assign(&mut self, other: Self) {
        self.real = self.real - other.real;
        self.imag = self.imag - other.imag;
    }
}

impl<T: Numeric> Neg for Complex<T> {
    type Output = Self;

    /// Negates a complex number.
    ///
    /// This uses the [`T::zero`] function necessary in the [`Numeric`] trait.
    ///
    /// \- t = 0 - t
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Complex;
    /// let mut z = Complex::new(1.0, 2.0);
    ///
    /// assert_eq!(-z, Complex::new(-1.0, -2.0));
    /// ```
    fn neg(self) -> Self::Output {
        Self {
            real: T::zero() - self.real,
            imag: T::zero() - self.imag,
        }
    }
}

impl<T: Numeric> Mul for Complex<T> {
    type Output = Self;

    /// Multiplies two complex numbers.
    ///
    /// (a + b _i_) * (c + d _i_) = (a c - b d) + (a d + b c) _i_
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Complex;
    /// let z_1 = Complex::new(1.0, 2.0);
    /// let z_2 = Complex::new(3.0, 4.0);
    ///
    /// assert_eq!(z_1 * z_2, Complex::new(-5.0, 10.0));
    /// ```
    fn mul(self, other: Self) -> Self::Output {
        Self {
            real: self.real * other.real - self.imag * other.imag,
            imag: self.real * other.imag + self.imag * other.real,
        }
    }
}

impl<T: Numeric> MulAssign for Complex<T> {
    /// Multiplies two complex numbers.
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Complex;
    /// let mut z = Complex::new(1.0, 2.0);
    /// z *= Complex::new(3.0, 4.0);
    ///
    /// assert_eq!(z, Complex::new(-5.0, 10.0));
    /// ```
    fn mul_assign(&mut self, other: Self) {
        // New imaginary value uses the old real values
        let new_real: T = self.real * other.real - self.imag * other.imag;
        let new_imag: T = self.real * other.imag + self.imag * other.real;

        self.real = new_real;
        self.imag = new_imag;
    }
}

impl<T: Numeric> Div for Complex<T> {
    type Output = Self;

    /// Divides a complex number by another.
    ///
    /// (a + b _i_) / (c + d _i_) = (a c + b d) / (a² + b²) + (b c - a d) / (a² + b²) _i_
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Complex;
    /// let z_1 = Complex::new(2.0, 3.0);
    /// let z_2 = Complex::new(1.0, -2.0);
    ///
    /// assert_eq!(z_1 / z_2, Complex::new(-0.8, 1.4));
    /// ```
    fn div(self, other: Self) -> Self::Output {
        let norm: T = other.norm_sq();

        Self {
            real: (self.real * other.real + self.imag * other.imag) / norm,
            imag: (self.imag * other.real - self.real * other.imag) / norm,
        }
    }
}

impl<T: Numeric> DivAssign for Complex<T> {
    /// Divides a complex number by another.
    ///
    /// # Examples
    ///
    /// ```
    /// # use random_math_stuff::Complex;
    /// let mut z = Complex::new(2.0, 3.0);
    /// z /= Complex::new(1.0, -2.0);
    ///
    /// assert_eq!(z, Complex::new(-0.8, 1.4));
    /// ```
    fn div_assign(&mut self, other: Self) {
        let norm: T = other.norm_sq();
        // New imaginary value uses the old real values
        let new_real: T = (self.real * other.real + self.imag * other.imag) / norm;
        let new_imag: T = (self.imag * other.real - self.real * other.imag) / norm;

        self.real = new_real;
        self.imag = new_imag;
    }
}
