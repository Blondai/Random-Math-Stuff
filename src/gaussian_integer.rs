use std::fmt::{Display, Formatter};
use std::ops::{Add, Div, Mul, Neg, Rem, Sub};

/// The integer type used for real and imaginary parts.
pub type NumberType = i32;

/// The float type used for evaluations.
pub type FloatType = f32;

/// Zero as type `NumberType`
const ZERO: NumberType = 0 as NumberType;

#[derive(Clone, Copy, Debug)]
/// A  struct for calculations involving [Gaussian Integers](https://en.wikipedia.org/wiki/Gaussian_integer).
/// Stores values in form of `real` and `imaginary` part.
/// Mathematically `real` + `imaginary` * i, with the complex unit i^2 = -1.
pub struct GaussianInteger {
    /// The real part of the Gaussian Integer
    real: NumberType,

    /// The imaginary part of the Gaussian Integer.
    imaginary: NumberType,
}

// New
impl GaussianInteger {
    /// Creates a new `GaussianInteger` instance.
    ///
    /// # Arguments
    /// * `real` (`NumberType`) - The real part of the complex integer.
    /// * `imaginary` (`NumberType`) - The imaginary part of the complex integer.
    ///
    /// # Returns
    /// The `GaussianInteger` instance representing the values `real` + `imaginary` * i.
    ///
    /// # Examples
    /// * Initializes 1+i.
    /// ```
    /// let gaussian_integer: GaussianInteger = GaussianInteger::new(1, 1);
    /// ```
    /// * Initializes -2+4i.
    /// ```
    /// let gaussian_integer: GaussianInteger = GaussianInteger::new(-2, 4);
    /// ```
    pub fn new(real: NumberType, imaginary: NumberType) -> GaussianInteger {
        GaussianInteger { real, imaginary }
    }

    /// Creates a new `GaussianInteger` instance using an integer.
    ///
    /// # Arguments
    /// `integer` (`NumberType`) - The integer to be converted to a `GaussianInteger` instance.
    ///
    /// # Returns
    /// The `GaussianInteger` instance representing the integer using `ZERO` as an `imaginary` part.
    ///
    /// # Examples
    /// * Initializes 5.
    /// ```
    /// let gaussian_integer: GaussianInteger = GaussianInteger::from_int(5);
    /// ```
    /// * Initializes -3.
    /// ```
    /// let gaussian_integer: GaussianInteger = GaussianInteger::from_int(-3);
    /// ```
    pub fn from_int(integer: NumberType) -> GaussianInteger {
        GaussianInteger {
            real: integer,
            imaginary: ZERO,
        }
    }
}

// Special Values
impl GaussianInteger {
    /// Returns the number one in form of a `GaussianInteger` instance.
    ///
    /// # Returns
    /// One as a `GaussianInteger` instance represented by 1+0i.
    ///
    /// # Examples
    /// Initializes one.
    /// ```
    /// let one: GaussianInteger = GaussianInteger::one();
    /// assert_eq!(one, GaussianInteger::new(1, 0));
    /// ```
    pub fn one() -> GaussianInteger {
        GaussianInteger {
            real: 1 as NumberType,
            imaginary: 0 as NumberType,
        }
    }

    /// Returns the number zero in form of a `GaussianInteger` instance.
    ///
    /// # Returns
    /// Zero as a `GaussianInteger` instance represented by 0+0i.
    ///
    /// # Examples
    /// Initializes zero.
    /// ```
    /// let zero: GaussianInteger = GaussianInteger::zero();
    /// assert_eq!(zero, GaussianInteger::new(0, 0));
    /// ```
    pub fn zero() -> GaussianInteger {
        GaussianInteger {
            real: 0 as NumberType,
            imaginary: 0 as NumberType,
        }
    }

    /// Returns the imaginary unit i in form of a `GaussianInteger` instance.
    ///
    /// # Returns
    /// i as a `GaussianInteger` instance represented by 0+i.
    ///
    /// # Examples
    /// Initializes i.
    /// ```
    /// let i: GaussianInteger = GaussianInteger::imaginary_unit();
    /// assert_eq!(i, GaussianInteger::new(0, 1));
    /// ```
    pub fn imaginary_unit() -> GaussianInteger {
        GaussianInteger {
            real: 0 as NumberType,
            imaginary: 1 as NumberType,
        }
    }

    /// Returns the imaginary unit i in form of a `GaussianInteger` instance.
    ///
    /// This method uses `imaginary_unit` internally.
    pub fn i() -> GaussianInteger {
        GaussianInteger::imaginary_unit()
    }

    /// Returns a list of the four units in the Gaussian Integers.
    ///
    /// # Returns
    /// A list of the four units in the Gaussian Integers.
    /// The list consists of 1, -1, i and -i.
    ///
    /// # Examples
    /// Returns the units.
    /// ```
    /// let units: [GaussianInteger; 4] = GaussianInteger::units();
    /// assert_eq!(units[0], GaussianInteger::new(1, 0));
    /// assert_eq!(units[1], GaussianInteger::new(-1, 0));
    /// assert_eq!(units[2], GaussianInteger::new(0, 1));
    /// assert_eq!(units[3], GaussianInteger::new(0, -1));
    /// ```
    pub fn units() -> [GaussianInteger; 4] {
        [
            GaussianInteger::one(),
            -GaussianInteger::one(),
            GaussianInteger::i(),
            -GaussianInteger::i()
        ]
    }
}

// Display
impl Display for GaussianInteger {
    /// Displays a `GaussianInteger` instance.
    ///
    /// This is sensitive to the signs of real and imaginary part to avoid stuff like 5 + - 3 i.
    ///
    /// # Examples
    /// * Prints `1 + 1 i`.
    /// ```
    /// let gaussian_integer: GaussianInteger = GaussianInteger::new(1, 1);
    /// println!("{}", gaussian_integer);
    /// ```
    /// * Prints `- 5 - 3 i`.
    /// ```
    /// let gaussian_integer: GaussianInteger = GaussianInteger::new(-5, -3);
    /// println!("{}", gaussian_integer);
    /// ```
    ///
    /// # Notes
    /// This could be enhanced to also differentiate the case where the imaginary part is one.
    /// This would avoid 1 + 1 i and print 1 + i instead.
    fn fmt(&self, format: &mut Formatter<'_>) -> std::fmt::Result {
        if self.real >= ZERO && self.imaginary >= ZERO {
            write!(format, "{} + {} i", self.real, self.imaginary)
        } else if self.real >= ZERO && self.imaginary < ZERO {
            write!(format, "{} - {} i", self.real, -self.imaginary)
        } else if self.real < ZERO && self.imaginary >= 0 {
            write!(format, "- {} + {} i", -self.real, self.imaginary)
        } else {
            write!(format, "- {} - {} i", -self.real, -self.imaginary)
        }
    }
}

// Equality
impl PartialEq for GaussianInteger {
    /// Compares two `GaussianInteger` instances for equality.
    ///
    /// Obviously two `GaussianInteger` instances are equal if their real- and imaginary parts are equal.
    ///
    /// # Arguments
    /// * `self` - A reference to the first `GaussianInteger` instance.
    /// * `other` - A reference to the second `GaussianInteger` instance.
    ///
    /// # Returns
    /// * `true` if both `GaussianInteger` have the same real- and imaginary part.
    /// * `false` otherwise.
    ///
    /// # Examples
    /// * Compares if 2+i is equal to 2+i.
    /// ```
    /// let gaussian_integer_1: GaussianInteger = GaussianInteger::new(2, 1);
    /// let gaussian_integer_2: GaussianInteger = GaussianInteger::new(2, 1);
    /// assert!(gaussian_integer_1 == gaussian_integer_2);
    /// ```
    /// * Compares if 1 is equal to i.
    /// ```
    /// let gaussian_integer_1: GaussianInteger = GaussianInteger::new(1, 0);
    /// let gaussian_integer_2: GaussianInteger = GaussianInteger::new(0, 1);
    /// assert!(gaussian_integer_1 != gaussian_integer_2);
    /// ```
    fn eq(self: &GaussianInteger, other: &GaussianInteger) -> bool {
        self.real == other.real && self.imaginary == other.imaginary
    }
}

// Norm
impl GaussianInteger {
    /// Calculates the norm of a `GaussianInteger` instance.
    ///
    /// # Arguments
    /// `self` - A reference to a `GaussianInteger` instance.
    ///
    /// # Returns
    /// The norm of the `GaussianInteger` instance in form of a integer of type `NumberType`.
    /// This is achieved by adding the squares of the real and imaginary part.
    ///
    /// # Examples
    /// * Calculates the norm of 2+3i.
    /// ```
    /// let gaussian_integer: GaussianInteger = GaussianInteger::new(2, 3);
    /// let norm: NumberType = gaussian_integer.norm();
    /// assert_eq!(norm, 13);
    /// ```
    /// * Calculates the norm of 2i.
    /// ```
    /// let gaussian_integer: GaussianInteger = GaussianInteger::new(0, 2);
    /// let norm: NumberType = gaussian_integer.norm();
    /// assert_eq!(norm, 4);
    /// ```
    pub fn norm(&self) -> NumberType {
        self.real.pow(2u32) + self.imaginary.pow(2u32)
    }
}

// Conjugation
impl GaussianInteger {
    /// Conjugates a `GaussianInteger` instance.
    ///
    /// # Arguments
    /// `self` - A reference to a `GaussianInteger` instance.
    ///
    /// # Returns
    /// The complex conjugate of the `GaussianInteger` instance.
    /// This is achieved by flipping the sign of the imaginary part.
    ///
    /// # Examples
    /// * Conjugates 2+2i.
    /// ```
    /// let gaussian_integer: GaussianInteger = GaussianInteger::new(2, 2);
    /// let conjugate: GaussianInteger = gaussian_integer.conjugate();
    /// assert_eq!(conjugate, GaussianInteger::new(2, -2));
    /// ```
    /// * Conjugates 2.
    /// ```
    /// let gaussian_integer: GaussianInteger = GaussianInteger::new(2, 0);
    /// let conjugate: GaussianInteger = gaussian_integer.conjugate();
    /// assert_eq!(conjugate, GaussianInteger::new(2, 0));
    /// ```
    pub fn conjugate(&self) -> GaussianInteger {
        GaussianInteger {
            real: self.real,
            imaginary: -self.imaginary,
        }
    }

    /// Conjugates a `GaussianInteger` instance.
    ///
    /// This method uses `conjugate` internally.
    pub fn conj(&self) -> GaussianInteger {
        self.conjugate()
    }
}

// Is ...
impl GaussianInteger {
    /// Checks if a `GaussianInteger` instance is purely real.
    ///
    /// # Arguments
    /// `self` - A reference to a `GaussianInteger` instance.
    ///
    /// # Returns
    /// * `true` if the imaginary part is zero.
    /// * `false` otherwise.
    ///
    /// # Examples
    /// * Checks if 3 is real.
    /// ```
    /// let gaussian_integer: GaussianInteger = GaussianInteger::new(3, 0);
    /// let is_real: bool = gaussian_integer.is_real();
    /// assert!(is_real);
    /// ```
    /// * Checks if i is real.
    /// ```
    /// let gaussian_integer: GaussianInteger = GaussianInteger::new(0, 1);
    /// let is_real: bool = gaussian_integer.is_real();
    /// assert!(!is_real);
    /// ```
    pub fn is_real(&self) -> bool {
        if self.imaginary == ZERO {
            true
        } else {
            false
        }
    }

    /// Checks if a `GaussianInteger` instance is purely imaginary.
    ///
    /// # Arguments
    /// `self` - A reference to a `GaussianInteger` instance.
    ///
    /// # Returns
    /// * `true` if the real part is zero.
    /// * `false` otherwise.
    ///
    /// # Examples
    /// * Checks if i is imaginary.
    /// ```
    /// let gaussian_integer: GaussianInteger = GaussianInteger::new(0, i);
    /// let is_imaginary: bool = gaussian_integer.is_real();
    /// assert!(is_imaginary);
    /// ```
    /// * Checks if 3 is imaginary.
    /// ```
    /// let gaussian_integer: GaussianInteger = GaussianInteger::new(3, 0);
    /// let is_imaginary: bool = gaussian_integer.is_real();
    /// assert!(!is_imaginary);
    /// ```
    pub fn is_imaginary(&self) -> bool {
        if self.real == ZERO {
            true
        } else {
            false
        }
    }
}

// Addition
impl Add for GaussianInteger {
    type Output = GaussianInteger;

    /// Adds two `GaussianInteger` instances.
    ///
    /// # Arguments
    /// * `self` - The first summand.
    /// * `other` - The second summand.
    ///
    /// # Returns
    /// A `GaussianInteger` instance representing the sum of `self` and `other`.
    /// This is achieved by adding the real- and imaginary parts separately.
    ///
    /// # Examples
    /// * Adds 1+2i and 2+3i.
    /// ```
    /// let gaussian_integer_1: GaussianInteger = GaussianInteger::new(1, 2);
    /// let gaussian_integer_2: GaussianInteger = GaussianInteger::new(2, 3);
    /// let sum: GaussianInteger = gaussian_integer_1 + gaussian_integer_2;
    /// assert_eq!(sum, GaussianInteger::new(3, 5));
    /// ```
    /// * Adds 3+2i and -2-i.
    /// ```
    /// let gaussian_integer_1: GaussianInteger = GaussianInteger::new(3, 2);
    /// let gaussian_integer_2: GaussianInteger = GaussianInteger::new(-2, -1);
    /// let sum: GaussianInteger = gaussian_integer_1 + gaussian_integer_2;
    /// assert_eq!(sum, GaussianInteger::new(1, 1));
    /// ```
    fn add(self: GaussianInteger, other: GaussianInteger) -> Self::Output {
        GaussianInteger {
            real: self.real + other.real,
            imaginary: self.imaginary + other.imaginary,
        }
    }
}

// Negation
impl Neg for GaussianInteger {
    type Output = GaussianInteger;

    /// Negates a `GaussianInteger` instance.
    ///
    /// # Arguments
    /// `self` - A `GaussianInteger` instance.
    ///
    /// # Returns
    /// A `GaussianInteger` instance representing the negation of `self`.
    /// This is achieved by negating the real- and imaginary part separately.
    /// Mathematically -(a+bi) = -a-bi.
    ///
    /// # Examples
    /// * Negates 4+2i.
    /// ```
    /// let gaussian_integer: GaussianInteger = GaussianInteger::new(4, 2);
    /// let negative: GaussianInteger = -gaussian_integer;
    /// assert_eq!(negative, GaussianInteger::new(-4, -2);
    /// ```
    /// * Negates -1+2i.
    /// ```
    /// let gaussian_integer: GaussianInteger = GaussianInteger::new(-1, 2);
    /// let negative: GaussianInteger = -gaussian_integer;
    /// assert_eq!(negative, GaussianInteger::new(1, -2);
    /// ```
    fn neg(self: GaussianInteger) -> Self::Output {
        GaussianInteger {
            real: -self.real,
            imaginary: -self.imaginary,
        }
    }
}

// Subtraction
impl Sub for GaussianInteger {
    type Output = GaussianInteger;

    /// Subtracts a `GaussianInteger` instance from another.
    ///
    /// # Arguments
    /// * `self` - The minuend.
    /// * `other` - The subtrahend.
    ///
    /// # Returns
    /// A `GaussianInteger` instance representing the difference of `self` and `other`.
    /// This uses addition and negation internally.
    /// Mathematically x - y = x + (- y).
    ///
    /// # Examples
    /// * Subtracts 5 from 1+i.
    /// ```
    /// let gaussian_integer_1: GaussianInteger = GaussianInteger::new(1, 1);
    /// let gaussian_integer_2: GaussianInteger = GaussianInteger::new(5, 0);
    /// let difference: GaussianInteger = gaussian_integer_1 - gaussian_integer_2;
    /// assert_eq!(difference, GaussianInteger::new(-4, 1));
    /// ```
    /// * Subtracts 2-i from 1+i.
    /// ```
    /// let gaussian_integer_1: GaussianInteger = GaussianInteger::new(1, 1);
    /// let gaussian_integer_2: GaussianInteger = GaussianInteger::new(2, -1);
    /// let difference: GaussianInteger = gaussian_integer_1 - gaussian_integer_2;
    /// assert_eq!(difference, GaussianInteger::new(-1, 2));
    /// ```
    fn sub(self: GaussianInteger, other: GaussianInteger) -> Self::Output {
        self + (-other)
    }
}

// Multiplication
impl Mul for GaussianInteger {
    type Output = GaussianInteger;

    /// Multiplies two `GaussianInteger` instances.
    ///
    /// # Arguments
    /// * `self` - The first factor.
    /// * `other` - The second factor.
    ///
    /// # Returns
    /// A `GaussianInteger` instance representing the product of `self` and `other`.
    /// This is calculated by using (a+bi) (c+di) = (ac-bd) + (ad+bd)i.
    ///
    /// # Examples
    /// * Multiplies 3+i by 2+3i.
    /// ```
    /// let gaussian_integer_1: GaussianInteger = GaussianInteger::new(3, 1);
    /// let gaussian_integer_2: GaussianInteger = GaussianInteger::new(2, 3);
    /// let product: GaussianInteger = gaussian_integer_1 * gaussian_integer_2;
    /// assert_eq!(product, GaussianInteger::new(3, 11));
    /// ```
    /// * Multiplies 4+2i by 3i.
    /// ```
    /// let gaussian_integer_1: GaussianInteger = GaussianInteger::new(4, 2);
    /// let gaussian_integer_2: GaussianInteger = GaussianInteger::new(0, 3);
    /// let product: GaussianInteger = gaussian_integer_1 * gaussian_integer_2;
    /// assert_eq!(product, GaussianInteger::new(-6, 12));
    /// ```
    fn mul(self: GaussianInteger, other: GaussianInteger) -> Self::Output {
        GaussianInteger {
            real: self.real * other.real - self.imaginary * other.imaginary,
            imaginary: self.real * other.imaginary + self.imaginary * other.real,
        }
    }
}

// Division
impl Div for GaussianInteger {
    type Output = GaussianInteger;

    /// Divides a `GaussianInteger` instance by another.
    /// This is done using Euclidean Division.
    ///
    /// # Arguments
    /// * `self` - The dividend.
    /// * `other` - The divisor.
    ///
    /// # Returns
    /// A `GaussianInteger` instance representing the Quotient of `self` and `other`.
    /// This uses floating point division and the `round` method to get an integer result.
    /// Mathematically x = y * q + r with quotient q and remainder r.
    ///
    /// # Examples
    /// * Divides 5 by 2+i.
    /// ```
    /// let gaussian_integer_1: GaussianInteger = GaussianInteger::new(5, 0);
    /// let gaussian_integer_2: GaussianInteger = GaussianInteger::new(2, 1);
    /// let quotient: GaussianInteger = gaussian_integer_1 / gaussian_integer_2;
    /// assert_eq!(quotient, GaussianInteger::new(2, -1));
    /// ```
    /// * Divides 2+8i by 1+i.
    /// ```
    /// let gaussian_integer_1: GaussianInteger = GaussianInteger::new(2, 8);
    /// let gaussian_integer_2: GaussianInteger = GaussianInteger::new(1, 1);
    /// let quotient: GaussianInteger = gaussian_integer_1 / gaussian_integer_2;
    /// assert_eq!(quotient, GaussianInteger::new(5, 3));
    /// ```
    fn div(self: GaussianInteger, other: GaussianInteger) -> Self::Output {
        let numerator: GaussianInteger = self * other.conj();
        let denominator: NumberType = other.norm();
        let real: NumberType = GaussianInteger::round((numerator.real as FloatType) / (denominator as FloatType));
        let imaginary: NumberType = GaussianInteger::round((numerator.imaginary as FloatType) / (denominator as FloatType));
        GaussianInteger { real, imaginary }
    }
}

// Remainder
impl Rem for GaussianInteger {
    type Output = GaussianInteger;

    /// Calculates the remainder of the Euclidean Division fo two `GaussianInteger` instances.
    ///
    /// # Arguments
    /// * `self` - The dividend.
    /// * `other` - The divisor.
    ///
    /// # Returns
    /// A `GaussianInteger` instance representing the remainder when dividing `self` by `other`.
    /// This uses the division method and calculates r = x - y * q.
    /// This is equivalent to the definition of Euclidean Division x = y * q + r.
    ///
    /// # Examples
    /// * Calculates the remainder of 3+4i divided by 1+i.
    /// ```
    /// let gaussian_integer_1: GaussianInteger = GaussianInteger::new(3, 4);
    /// let gaussian_integer_2: GaussianInteger = GaussianInteger::new(1, 1);
    /// let remainder: GaussianInteger = gaussian_integer_1 % gaussian_integer_2;
    /// assert_eq!(remainder, GaussianInteger::new(0, -1));
    /// ```
    /// * Calculates the remainder of 5 divided by 2+i.
    /// ```
    /// let gaussian_integer_1: GaussianInteger = GaussianInteger::new(5, 0);
    /// let gaussian_integer_2: GaussianInteger = GaussianInteger::new(2, 1);
    /// let remainder: GaussianInteger = gaussian_integer_1 % gaussian_integer_2;
    /// assert_eq!(remainder, GaussianInteger::new(0, 0));
    /// ```
    fn rem(self: GaussianInteger, other: GaussianInteger) -> GaussianInteger {
        let quotient: GaussianInteger = self / other;
        self - other * quotient
    }
}

// Greatest Common Divisor
impl GaussianInteger {
    /// Calculates a greatest common divisor (gcd) of two `GaussianInteger` instances using the Euclidean Algorithm.
    /// The greatest common divisor is the biggest number dividing both gaussian integers without remainder.
    /// This value is not unique, because the field of gaussian integers has four associated elements.
    ///
    /// # Arguments
    /// * `number_1` (`GaussianInteger`) - The first number.
    /// * `number_2` (`GaussianInteger`) - The second number.
    ///
    /// # Returns
    /// A `GaussianInteger` instance representing a gcd of `number_1` and `number_2`.
    ///
    /// # Examples
    /// Calculates the gcd of 5+3i and 2-8i.
    /// ```
    /// let gaussian_integer_1: GaussianInteger = GaussianInteger::new(5, 3);
    /// let gaussian_integer_2: GaussianInteger = GaussianInteger::new(2, -8);
    /// let gcd: GaussianInteger = GaussianInteger::greatest_common_divisor(gaussian_integer_1, gaussian_integer_2);
    /// assert_eq!(gcd, GaussianInteger::new(1, -1));
    /// ```
    pub fn greatest_common_divisor(mut number_1: GaussianInteger, mut number_2: GaussianInteger) -> GaussianInteger {
        while number_2.real != ZERO || number_2.imaginary != ZERO {
            let auxiliary: GaussianInteger = number_1 % number_2;
            number_1 = number_2;
            number_2 = auxiliary;
        }
        number_1
    }

    /// Calculates all greatest common divisors of two `GaussianInteger` instances.
    ///
    /// # Arguments
    /// * `self` - A reference to the first `GaussianInteger`.
    /// * `other` - A reference to the second `GaussianInteger`.
    ///
    /// # Returns
    /// A list of four `GaussianInteger`s which are all greatest common divisors.
    /// This is calculated by calculating one greatest common divisor with the `greatest_common_divisor` method
    /// and using the `associated_elements` method to get all four associated elements.
    ///
    /// # Examples
    /// Calculates the gcds for 5+3i and 2-8i.
    /// ```
    /// let gaussian_integer_1: GaussianInteger = GaussianInteger::new(5, 3);
    /// let gaussian_integer_2: GaussianInteger = GaussianInteger::new(2, -8);
    /// let gcds: [GaussianInteger; 4] = gaussian_integer_1.gcds(&gaussian_integer_2);
    /// assert_eq!(gcds[0], GaussianInteger::new(1, -1));
    /// assert_eq!(gcds[1], GaussianInteger::new(-1, 1));
    /// assert_eq!(gcds[2], GaussianInteger::new(1, 1));
    /// assert_eq!(gcds[3], GaussianInteger::new(-1, -1))
    /// ```
    pub fn gcds(self: &GaussianInteger, other: &GaussianInteger) -> [GaussianInteger; 4] {
        let number_1: GaussianInteger = self.clone();
        let number_2: GaussianInteger = other.clone();
        let gcd: GaussianInteger = GaussianInteger::greatest_common_divisor(number_1, number_2);
        gcd.associated_elements()
    }

    /// Calculates the canonical greatest common divisor.
    ///
    /// # Arguments
    /// * `self` - A reference to the first `GaussianInteger` instance.
    /// * `other` - A reference to the second `GaussianInteger` instance.
    ///
    /// # Results
    /// A `GaussianInteger` instance representing the canonical representation of the greatest common divisor.
    /// This is the greatest common divisor with positive real- and imaginary parts.
    /// It is calculated by using the `gcds` method and choosing the right value.
    ///
    /// # Examples
    /// Calculates the gcd of 1+3i and 8+6i.
    /// ```
    /// let gaussian_integer_1: GaussianInteger = GaussianInteger::new(1, 3);
    /// let gaussian_integer_2: GaussianInteger = GaussianInteger::new(8, 6);
    /// let gcd: GaussianInteger = gaussian_integer_1.gcd(&gaussian_integer_2);
    /// assert_eq!(gcd, GaussianInteger::new(1, 1));
    /// ```
    pub fn gcd(self: &GaussianInteger, other: &GaussianInteger) -> GaussianInteger {
        let gcds: [GaussianInteger; 4] = self.gcds(other);
        for gcd in gcds {
            if gcd.real >= 0 && gcd.imaginary >= 0 {
                return gcd;
            }
        }
        gcds[0]  // Impossible
    }

    /// Rounds a float number to the nearest integer.
    ///
    /// # Arguments
    /// `number` (`FloatType`) - A floating number.
    ///
    /// # Returns
    /// An integer of type `NumberType` representing the rounded value of the float.
    ///
    /// # Examples
    /// * Rounds 0.5.
    /// ```
    /// let float: FloatType = 0.5;
    /// assert_eq!(GaussianInteger::round(float), 1);
    /// ```
    /// * Rounds 1.2.
    /// ```
    /// let float: FloatType = 1.2;
    /// assert_eq!(GaussianInteger::round(float), 1);
    /// ```
    /// * Rounds -0.5.
    /// ```
    /// let float: FloatType = -0.5;
    /// assert_eq!(GaussianInteger::round(float), 0);
    /// ```
    /// * Rounds -2.3.
    /// ```
    /// let float: FloatType = -2.3;
    /// assert_eq!(GaussianInteger::round(float), -2);
    /// ```
    ///
    /// # Notes
    /// The logic of this calculation could easily be simplified.
    pub fn round(number: FloatType) -> NumberType {
        let mut copy: FloatType = number.clone();
        const ONE: FloatType = 1 as FloatType;
        const ZERO: FloatType = 0 as FloatType;
        const HALF: FloatType = 0.5 as FloatType;
        if copy >= ZERO {
            while copy >= ONE {
                copy -= ONE
            }
            if copy >= HALF {
                number.ceil() as NumberType
            } else {
                number.floor() as NumberType
            }
        } else {
            while copy <= -ONE {
                copy += ONE
            }
            if copy >= -HALF {
                number.ceil() as NumberType
            } else {
                number.floor() as NumberType
            }
        }
    }
}

impl GaussianInteger {
    /// Calculates a least common multiple of two `GaussianInteger` instances.
    ///
    /// # Arguments
    /// * `self` - A reference to the first `GaussianInteger`.
    /// * `other` - A reference to the second `GaussianInteger`.
    ///
    /// # Returns
    /// A `GaussianInteger` representing a least common multiple.
    /// This is calculated by calculating one greatest common divisor with the `greatest_common_divisor` method
    /// and using its definition.
    ///
    /// # Examples
    /// * Calculates the lcm of 1+3i and 8+6i.
    /// ```
    /// let gaussian_integer_1: GaussianInteger = GaussianInteger::new(1, 3);
    /// let gaussian_integer_2: GaussianInteger = GaussianInteger::new(8, 6);
    /// let lcm: GaussianInteger = gaussian_integer_1.least_common_multiple(&gaussian_integer_2);
    /// assert_eq!(lcm, GaussianInteger::new(10, 20));
    /// ```
    /// * Calculates the lcm of 1+i and 2+2i.
    /// ```
    /// let gaussian_integer_1: GaussianInteger = GaussianInteger::new(1, 1);
    /// let gaussian_integer_2: GaussianInteger = GaussianInteger::new(2, 2);
    /// let lcm: GaussianInteger = gaussian_integer_1.least_common_multiple(&gaussian_integer_2);
    /// assert_eq!(lcm, GaussianInteger::new(2, 2));
    /// ```
    pub fn least_common_multiple(self: &GaussianInteger, other: &GaussianInteger) -> GaussianInteger {
        *self * *other / self.gcd(other)
    }

    /// Calculates all least common multiples of two `GaussianInteger` instances.
    ///
    /// # Arguments
    /// * `self` - A reference to the first `GaussianInteger`.
    /// * `other` - A reference to the second `GaussianInteger`.
    ///
    /// # Returns
    /// A list of four `GaussianInteger`s which are all least common multiples.
    /// This is calculated by calculating one least common multiple with the `least_common_multiple` method
    /// and using the `associated_elements` method to get all four associated elements.
    ///
    /// # Examples
    /// Calculates the lcms for 2+4i and 3+5i.
    /// ```
    /// let gaussian_integer_1: GaussianInteger = GaussianInteger::new(2, 4);
    /// let gaussian_integer_2: GaussianInteger = GaussianInteger::new(3, 5);
    /// let lcms: [GaussianInteger; 4] = gaussian_integer_1.lcms(&gaussian_integer_2);
    /// assert_eq!(lcms[0], GaussianInteger::new(4, 18));
    /// assert_eq!(lcms[1], GaussianInteger::new(-4, -18));
    /// assert_eq!(lcms[2], GaussianInteger::new(-18, 4));
    /// assert_eq!(lcms[3], GaussianInteger::new(18, -4));
    /// ```
    pub fn lcms(self: &GaussianInteger, other: &GaussianInteger) -> [GaussianInteger; 4] {
        let lcm: GaussianInteger = self.least_common_multiple(other);
        lcm.associated_elements()
    }

    /// Calculates the canonical least common multiple.
    ///
    /// # Arguments
    /// * `self` - A reference to the first `GaussianInteger` instance.
    /// * `other` - A reference to the second `GaussianInteger` instance.
    ///
    /// # Results
    /// A `GaussianInteger` instance representing the canonical representation of the least common multiple.
    /// This is the least common multiple with positive real- and imaginary parts.
    /// It is calculated by using the `lcms` method and choosing the right value.
    ///
    /// # Examples
    /// Calculates the lcm of 4+4i and 3+5i.
    /// ```
    /// let gaussian_integer_1: GaussianInteger = GaussianInteger::new(2, 4);
    /// let gaussian_integer_2: GaussianInteger = GaussianInteger::new(3, 5);
    /// let lcm: GaussianInteger = gaussian_integer_1.lcm(&gaussian_integer_2);
    /// assert_eq!(lcm, GaussianInteger::new(4, 18));
    /// ```
    pub fn lcm(self: &GaussianInteger, other: &GaussianInteger) -> GaussianInteger {
        let lcms: [GaussianInteger; 4] = self.lcms(other);
        for lcm in lcms {
            if lcm.real >= 0 && lcm.imaginary >= 0 {
                return lcm;
            }
        }
        lcms[0]  // Impossible
    }
}

// Associated Elements
impl GaussianInteger {
    /// Calculates a `list` of associated elements to a `GaussianInteger` instance.
    ///
    /// # Arguments
    /// `self` - A reference to a `GaussianInteger` instance.
    ///
    /// # Returns
    /// A list of the four elements associated to `self`.
    /// The list is calculated by multiplying `self` by the four units.
    /// 1, -1, i and -i are returned from the `units` method.
    ///
    /// # Examples
    /// Calculates the associated elements of 1+i.
    /// ```
    /// let gaussian_integer: GaussianInteger = GaussianInteger::new(1, 1);
    /// let associated_elements: [GaussianInteger; 4] = gaussian_integer.associated_elements();
    /// assert_eq!(associated_elements[0], GaussianInteger::new(1, 1));
    /// assert_eq!(associated_elements[1], GaussianInteger::new(-1, -1));
    /// assert_eq!(associated_elements[2], GaussianInteger::new(-1, 1));
    /// assert_eq!(associated_elements[3], GaussianInteger::new(1, -1));
    /// ```
    ///
    /// # Notes
    /// This method could possibly be speed up by forgo the multiplication and
    /// just make the combinations with ++, --, -+ and +- with the correct permutations of real- and imaginary parts.
    pub fn associated_elements(&self) -> [GaussianInteger; 4] {
        let mut values: [GaussianInteger; 4] = [GaussianInteger::zero(); 4];
        for (index, unit) in GaussianInteger::units().iter().enumerate() {
            values[index] = *self * *unit
        }
        values
    }
}

// Comprime
impl GaussianInteger {
    /// Checks whether two `GaussianInteger` instances are comprime.
    ///
    /// # Arguments
    /// * `self` - A reference to te first `GaussianInteger` instance.
    /// * `other` - A reference to the second `GaussianInteger` instance.
    ///
    /// # Returns
    /// * `true` if the gcds contain one.
    /// * `false` otherwise.
    ///
    /// Equivalently one could search for -1, i or -i in the list of gcds.
    ///
    /// # Examples
    /// * Checks if 1+i and 3+4i are coprime.
    /// ```
    /// let gaussian_integer_1: GaussianInteger = GaussianInteger::new(1, 1);
    /// let gaussian_integer_2: GaussianInteger = GaussianInteger::new(3, 4);
    /// assert!(gaussian_integer_1.coprime(&gaussian_integer_2))
    /// ```
    /// * Checks if 1+3i an 8+6i are coprime.
    /// ```
    /// let gaussian_integer_1: GaussianInteger = GaussianInteger::new(5, 3);
    /// let gaussian_integer_2: GaussianInteger = GaussianInteger::new(2, -8);
    /// assert!(!gaussian_integer_1.coprime(&gaussian_integer_2))
    /// ```
    pub fn coprime(self: &GaussianInteger, other: &GaussianInteger) -> bool {
        self.gcds(other).contains(&GaussianInteger::one())
    }
}
