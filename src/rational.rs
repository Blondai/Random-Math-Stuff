use std::cmp::Ordering;
use std::fmt::{Display, Formatter};
use std::ops::{Add, Div, Mul, Neg, Rem, Sub};

/// The unsigned integer type used for numerator and denominator.
pub type NumberType = u32;

/// The integer type used for initialization.
pub type IntegerType = i32;

/// The float type used for evaluation of rational numbers.
pub type FloatType = f64;

#[derive(Debug, Clone, Copy)]
/// A struct for calculations involving rational numbers.
/// Stores values in form of sign, numerator and denominator.
/// This has the big advantage of not using floats.
pub struct Rational {
    /// The sign of the rational number.
    /// `true` if it is positive and `false` if it is negative.
    pub positive: bool,

    /// The numerator of the rational number.
    pub numerator: NumberType,

    /// The denominator of the rational number.
    pub denominator: NumberType,
}

// New
impl Rational {
    /// Creates a new `Rational` instance.
    ///
    /// # Arguments
    /// * `positive` (`bool`) - Whether the rational number is positive or not.
    /// * `numerator` (`NumberType`) - The value of the numerator.
    /// * `denominator` (`NumberType`) - The value of the denominator.
    ///
    /// # Returns
    /// A `Rational` instance representing the values.
    ///
    /// # Examples
    /// * Initializes 1/3 = 0.3333333333333333.
    /// ```
    /// let one_third: Rational = Rational::new(true, 1, 3);
    /// ```
    /// * Initializes -1/2 = -0.5.
    /// ```
    /// let one_half: Rational = Rational::new(false, 1, 2);
    /// ```
    pub fn new(positive: bool, numerator: NumberType, denominator: NumberType) -> Rational {
        Rational {
            positive,
            numerator,
            denominator,
        }
    }

    /// Creates a new `Rational` instance using a positive integer.
    ///
    /// # Arguments
    /// `number` (`NumberType`) - The natural number you want to convert to a `Rational` instance.
    ///
    /// # Returns
    /// A `Rational` instance representing number with one as a denominator.
    ///
    /// # Examples
    /// Initializes 1.
    /// ```
    /// let one: Rational = Rational::from_natural(1);
    /// ```
    pub fn from_natural(number: NumberType) -> Rational {
        Rational {
            positive: true,
            numerator: number,
            denominator: 1 as NumberType,
        }
    }

    /// Creates a new rational instance using an integer.
    ///
    /// # Arguments
    /// `number` (`IntegerType`) - The integer number you want to convert to a `Rational` instance.
    ///
    /// # Returns
    /// A `Rational` instance representing the number with one as a denominator.
    ///
    /// # Examples
    /// * Initializes -5.
    /// ```
    /// let negative_five: Rational = Rational::from_integer(-5);
    /// ```
    ///
    /// * Initializes 7.
    /// ```
    /// let seven: Rational = Rational::from_integer(7);
    /// ```
    pub fn from_integer(number: IntegerType) -> Rational {
        if number >= 0 {
            Rational {
                positive: true,
                numerator: number as NumberType,
                denominator: 1 as NumberType,
            }
        } else {
            Rational {
                positive: false,
                numerator: (-number) as NumberType,
                denominator: 1 as NumberType,
            }
        }
    }
}

// Special Values
impl Rational {
    /// Returns the number one in form of a `Rational` instance.
    ///
    /// # Returns
    /// One as a `Rational` instance represented by 1/1.
    ///
    /// # Examples
    /// Initializes one.
    /// ```
    /// let one: Rational = Rational::one();
    /// assert_eq!(one, Rational::new(true, 1, 1));
    /// ```
    pub fn one() -> Rational {
        Rational {
            positive: true,
            numerator: 1,
            denominator: 1,
        }
    }

    /// Returns the number zero in form of a `Rational` instance.
    ///
    /// # Returns
    /// Zero as a `Rational` instance represented by 0/1.
    ///
    /// # Examples
    /// Initializes zero.
    /// ```
    /// let zero: Rational = Rational::zero();
    /// assert_eq!(zero, Rational::new(true, 0, 1));
    /// ```
    pub fn zero() -> Rational {
        Rational {
            positive: true,
            numerator: 0,
            denominator: 1,
        }
    }
}

// Display
impl Display for Rational {
    /// Displays a `Rational` instance.
    ///
    /// # Examples
    /// * Prints 3/4.
    /// ```
    /// let three_fourth: Rational = Rational::new(true, 3, 4);
    /// println!("{}", three_fourth);
    /// ```
    /// * Prints -5/7.
    /// ```
    /// let five_seventh: Rational = Rational::new(false, 5, 7);
    /// println!("{}", five_seventh);
    /// ```
    fn fmt(&self, format: &mut Formatter<'_>) -> std::fmt::Result {
        if self.positive {
            write!(format, "{} / {}", self.numerator, self.denominator)
        } else {
            write!(format, "- {} / {}", self.numerator, self.denominator)
        }
    }
}

// Partial Equation
impl PartialEq for Rational {
    /// Compares two `Rational` instances for equality.
    ///
    /// This function simplifies both rational numbers before comparing them to ensure that both are in their reduced forms.
    /// Two `Rational` instances are considered equal if their signs, numerators and denominators are equal after simplification.
    ///
    /// # Arguments
    /// * `self` - A reference to the first `Rational` instance.
    /// * `other` - A reference to the second `Rational` instance.
    ///
    /// # Returns
    /// * `true` if both `Rational` instances are equal.
    /// * `false` otherwise.
    ///
    /// # Examples
    /// * Compares if 1/2 is equal to 1/2.
    /// ```
    /// let rational_1: Rational = Rational::new(true, 1, 2);
    /// let rational_2: Rational = Rational::new(true, 1, 2);
    /// assert!(rational_1 == rational_2);
    /// ```
    /// * Compares if 1/7 is equal to -1/7.
    /// ```
    /// let rational_1: Rational = Rational::new(true, 1, 7);
    /// let rational_2: Rational = Rational::new(false, 1, 7);
    /// assert!(rational_1 != rational_2);
    /// ```
    /// * Compares if 1/3 is equal to 2/6.
    /// ```
    /// let rational_1: Rational = Rational::new(true, 1, 3);
    /// let rational_2: Rational = Rational::new(true, 2, 6);
    /// assert!(rational_1 == rational_2);
    /// ```
    fn eq(self: &Rational, other: &Rational) -> bool {
        let (rational_1, rational_2): (Rational, Rational) = self.common_denominator(other);
        rational_1.numerator == rational_2.numerator && rational_1.positive == rational_2.positive
    }
}

// Partial Order
impl PartialOrd for Rational {
    /// Compares two `Rational` instances and returns `Option<Ordering>`, indicating whether the first number is less than, equal to or greater than the second.
    ///
    /// # Arguments
    /// * `self` - A reference to the first `Rational` instance.
    /// * `other` - A reference to the second `Rational` instance.
    ///
    /// # Returns
    /// The comparison is archived by converting a `Rational` instances to floats by using the `eval` method.
    /// After this they are compared using the `partial_cmp` method for floats.
    /// * `Some(Ordering::Less)` if `self` is less than `other`.
    /// * `Some(Ordering::Equal)` if `self` is equal to `other`.
    /// * `Some(Ordering::Greater)` if `self` is greater than `other`.
    /// * `None` if the comparison is undefined.
    ///
    /// # Examples
    /// * Compares if 5/7 is less or equal to 5/7.
    /// ```
    /// let rational_1: Rational = Rational::new(true, 5, 7);
    /// let rational_2: Rational = Rational::new(true, 5, 7);
    /// assert!(rational_1 <= rational_2);
    /// ```
    /// * Compares if 1/2 is bigger than 1/3.
    /// ```
    /// let rational_1: Rational = Rational::new(true, 1, 2);
    /// let rational_2: Rational = Rational::new(true, 1, 3);
    /// assert!(rational_1 > rational_2);
    /// ```
    /// * Compares if -5/6 is less than -1/6.
    /// ```
    /// let rational_1: Rational = Rational::new(false, 5, 6);
    /// let rational_2: Rational = Rational::new(false, 1, 6);
    /// assert!(rational_1 < rational_2);
    /// ```
    fn partial_cmp(self: &Rational, other: &Rational) -> Option<Ordering> {
        self.eval().partial_cmp(&other.eval())
    }
}

// Greatest Common Divisor
impl Rational {
    /// Calculates the [greatest common divisor](https://en.wikipedia.org/wiki/Greatest_common_divisor) (gcd) of two numbers using the [Euclidean Algorithm](https://en.wikipedia.org/wiki/Euclidean_algorithm).
    /// The greatest common divisor is the biggest number dividing both numbers without remainder.
    /// This is a symmetric action, so `Rational::greatest_common_divisor(number_1, number_2) == Rational::greatest_common_divisor(number_2, number_1)`.
    ///
    /// # Arguments
    /// * `number_1` (`NumberType`) - The first number.
    /// * `number_2` (`NumberType`) - The second number.
    ///
    /// # Returns
    /// The gcd of `number_1` and `number_2`, which is also of type `NumberType`.
    ///
    /// # Examples
    /// * Calculates the gcd of 48 and 18.
    /// ```
    /// let number_1: NumberType = 48;
    /// let number_2: NumberType = 18;
    /// let gcd: NumberType = Rational::greatest_common_divisor(number_1, number_2);
    /// assert_eq!(gcd, 6);
    /// ```
    /// * Calculates the gcd of 14 and 5.
    /// ```
    /// let number_1: NumberType = 14;
    /// let number_2: NumberType = 5;
    /// let gcd: NumberType = Rational::greatest_common_divisor(number_1, number_2);
    /// assert_eq!(gcd, 1);
    /// ```
    pub fn greatest_common_divisor(mut number_1: NumberType, mut number_2: NumberType) -> NumberType {
        while number_2 != 0 {
            let auxiliary: NumberType = number_1 % number_2;
            number_1 = number_2;
            number_2 = auxiliary;
        }
        number_1
    }

    /// Calculates the greatest common divisor (gcd) of the numerator and denominator of a `Rational` instance.
    ///
    /// # Arguments
    /// `self` - A reference to a `rational` instance.
    ///
    /// # Returns
    /// The gcd of the numerator and denominator using the `greatest_common_divisor` function.
    ///
    /// # Examples
    /// * Calculates the gcd of the fraction 14/35.
    /// ```
    /// let rational: Rational = Rational::new(true, 14, 35);
    /// let gcd: NumberType = rational.gcd();
    /// assert_eq!(gcd, 7);
    /// ```
    /// * Calculates the gcd of the fraction -9/15.
    /// ```
    /// let rational: Rational = Rational::new(false, 9, 15);
    /// let gcd: NumberType = rational.gcd();
    /// assert_eq!(gcd, 3);
    /// ```
    pub fn gcd(&self) -> NumberType {
        Rational::greatest_common_divisor(self.numerator, self.denominator)
    }
}

// Common Denominator
impl Rational {
    /// Calculates the [least common multiple](https://en.wikipedia.org/wiki/Least_common_multiple) (lcm) of two numbers using the greatest common divisor.
    ///
    /// # Arguments
    /// * `number_1` (`NumberType`) - The first number.
    /// * `number_2` (`NumberType`) - The second number.
    ///
    /// # Returns
    /// The lcm of `number_1` and `number_2`, which is also of type `NumberType`.
    ///
    /// # Examples
    /// * Calculates the lcm of 15 and 3.
    /// ```
    /// let number_1: NumberType = 15;
    /// let number_2: NumberType = 3;
    /// let lcm: NumberType = Rational::least_common_multiple(number_1, number_2);
    /// assert_eq!(lcm, 15);
    /// ```
    /// * Calculates the lcm of 7 and 5.
    /// ```
    /// let number_1: NumberType = 7;
    /// let number_2: NumberType = 5;
    /// let lcm: NumberType = Rational::least_common_multiple(number_1, number_2);
    /// assert_eq!(lcm, 35);
    /// ```
    pub fn least_common_multiple(number_1: NumberType, number_2: NumberType) -> NumberType {
        number_1 * number_2 / Rational::greatest_common_divisor(number_1, number_2)
    }

    /// Calculates the least common multiple (lcm) of the denominators of two `Rational` instances.
    ///
    /// # Arguments
    /// * `self` - A reference to the first `Rational` instance.
    /// * `other` - A reference of the second `Rational` instance.
    ///
    /// # Returns
    /// The lcm of the denominators using the `least_common_multiple` function.
    ///
    /// # Examples
    /// * Calculates the lcm of the fractions 1/6 and 1/10.
    /// ```
    /// let rational_1: Rational = Rational::new(true, 1, 6);
    /// let rational_2: Rational = Rational::new(true, 1, 10);
    /// let lcm: NumberType = rational_1.lcm(&rational_2);
    /// assert_eq!(lcm, 30);
    /// ```
    /// * Calculates the lcm of the fraction -3/8 and 5/6.
    /// ```
    /// let rational_1: Rational = Rational::new(false, 3, 8);
    /// let rational_2: Rational = Rational::new(true, 5, 6);
    /// let lcm: NumberType = rational_1.lcm(&rational_2);
    /// assert_eq!(lcm, 24);
    /// ```
    pub fn lcm(self: &Rational, other: &Rational) -> NumberType {
        Rational::least_common_multiple(self.denominator, other.denominator)
    }

    /// Returns two `Rational` instances with the same denominator.
    ///
    /// # Arguments
    /// * `self` - A reference to the first `Rational` instance.
    /// * `other` - A reference to the second `Rational` instance.
    ///
    /// # Returns
    /// A tuple consisting of two `Rational` instances with the same denominator and accordingly scaled nominators.
    ///
    /// # Examples
    /// * Calculates the same denominators for 1/3 and 2/5.
    /// ```
    /// let rational_1: Rational = Rational::new(true, 1, 3);
    /// let rational_2: Rational = Rational::new(true, 2, 5);
    /// let (rational_1, rational_2) = rational_1.common_denominator(&rational_2);
    /// assert_eq!(rational_1.denominator, rational_2.denominator);
    /// ```
    /// * Calculates the same denominators for -7/6 and 3/18.
    /// ```
    /// let rational_1: Rational = Rational::new(false, 7,6);
    /// let rational_2: Rational = Rational::new(true, 3, 18);
    /// let (rational_1, rational_2) = rational_1.common_denominator(&rational_2);
    /// assert_eq!(rational_1.denominator, rational_2.denominator);
    /// ```
    pub fn common_denominator(self: &Rational, other: &Rational) -> (Rational, Rational) {
        let lcm: NumberType = self.lcm(other);
        let factor_1: NumberType = lcm / self.denominator;
        let factor_2: NumberType = lcm / other.denominator;
        let numerator_1: NumberType = self.numerator * factor_1;
        let numerator_2: NumberType = other.numerator * factor_2;
        (
            Rational {
                positive: self.positive,
                numerator: numerator_1,
                denominator: lcm,
            },
            Rational {
                positive: other.positive,
                numerator: numerator_2,
                denominator: lcm,
            }
        )
    }
}

// Simplify
impl Rational {
    /// Simplifies a `Rational` instance by dividing the numerator and denominator by the gcd.
    ///
    /// # Arguments
    /// `self` - A reference to the `rational` instance.
    ///
    /// # Returns
    /// A simplified version of a `Rational` instance.
    /// If the gcd of numerator and denominator are one, the rational number is returned unchanged.
    /// Otherwise, numerator and denominator are divided by the gcd.
    ///
    /// # Examples
    /// * Simplifies the fraction 6/8.
    /// ```
    /// let rational_1: Rational = Rational::new(true, 6, 8).simplify();
    /// assert_eq!(rational_1.numerator, 3);
    /// assert_eq!(rational_1.denominator, 4);
    /// ```
    /// * Simplifies the fraction -3/4.
    /// ```
    /// let rational_1: Rational = Rational::new(false, 3, 4).simplify();
    /// assert_eq!(rational_1.numerator, 3);
    /// assert_eq!(rational_1.denominator, 4);
    /// ```
    pub fn simplify(&self) -> Rational {
        let gcd: NumberType = self.gcd();
        if gcd != 1 {
            Rational {
                positive: self.positive,
                numerator: self.numerator / gcd,
                denominator: self.denominator / gcd,
            }
        } else {
            Rational {
                positive: self.positive,
                numerator: self.numerator,
                denominator: self.denominator,
            }
        }
    }

    /// Checks whether two numbers are coprime.
    ///
    /// # Arguments
    /// * `number_1` (`NumberType`) - The first number.
    /// * `number_2` (`NumberType`) - The second number.
    ///
    /// # Returns
    /// Two numbers are coprime if their gcd is equal to one.
    /// This function uses the `greatest_common_divisor` method to get the gcd.
    /// * `true` if gcd is equal to one.
    /// * `false` otherwise.
    ///
    /// # Examples
    /// * Checks if 5 and 7 are coprime.
    /// ```
    /// let number_1: NumberType = 5;
    /// let number_2: NumberType = 7;
    /// assert!(Rational::coprime(number_1, number_2));
    /// ```
    /// * Checks if 2 and 4 are coprime.
    /// ```
    /// let number_1: NumberType = 2;
    /// let number_2: NumberType =4;
    /// assert!(!Rational::coprime(number_1, number_2));
    /// ```
    pub fn coprime(number_1: NumberType, number_2: NumberType) -> bool {
        Rational::greatest_common_divisor(number_1, number_2) == 1
    }

    /// Checks whether a `Rational` instance is in its reduced form.
    ///
    /// # Arguments
    /// `self` - A reference to a `Rational` instance.
    ///
    /// # Returns
    /// * `true` if numerator and denominator are coprime.
    /// * `false` otherwise.
    ///
    /// # Examples
    /// * Checks if 2/3 is in its reduced form.
    /// ```
    /// let rational: Rational = Rational::new(true, 2, 3);
    /// assert!(rational.reduced_form())
    /// ```
    /// * Checks if 5/10 is in its reduced form.
    /// ```
    /// let rational: Rational = Rational::new(true, 5, 10);
    /// assert!(!rational.reduced_form())
    /// ```
    pub fn reduced_form(&self) -> bool {
        Rational::coprime(self.numerator, self.denominator)
    }
}

// Multiplication
impl Mul for Rational {
    type Output = Rational;

    /// Multiplies two `Rational` instances.
    ///
    /// # Arguments
    /// * `self` - The first factor.
    /// * `other` - The second factor.
    ///
    /// # Returns
    /// A new `Rational` instance representing the product of the two rational numbers.
    /// This is calculated by multiplying numerator by numerator and denominator by denominator.
    /// The sign is calculated by negating the xor of  both sings.
    /// So the sign is positive if they have equal sings and negative if they have different signs.
    /// Finally, the product is simplified using the `simplify` method.
    ///
    /// # Examples
    /// * Multiplies 3/4 by 7/5.
    /// ```
    /// let rational_1: Rational = Rational::new(true, 3, 4);
    /// let rational_2: Rational = Rational::new(true, 7, 5);
    /// let product: Rational = rational_1 * rational_2;
    /// assert_eq!(product, Rational::new(true, 21, 20));
    /// ```
    /// * Multiplies -1/5 by 2/6.
    /// ```
    /// let rational_1: Rational = Rational::new(false, 1, 5);
    /// let rational_2: Rational = Rational::new(true, 2, 6);
    /// let product: Rational = rational_1 * rational_2;
    /// assert_eq!(product, Rational::new(false, 1, 15));
    /// ```
    fn mul(self: Rational, other: Rational) -> Self::Output {
        let mut rational: Rational = Rational {
            positive: !(self.positive ^ other.positive),
            numerator: self.numerator * other.numerator,
            denominator: self.denominator * other.denominator,
        };
        rational.simplify();
        rational
    }
}

// Inversion
impl Rational {
    /// Inverts a `Rational` instance.
    ///
    /// # Arguments
    /// `self` - A reference to a `Rational` instance.
    ///
    /// # Returns
    /// A new `Rational` instance representing the inverse of `self`.
    /// This is calculated by making the numerator of the inputted `Rational` the denominator of the outputted one and vice versa.
    ///
    /// # Examples
    /// * Inverts 7/6.
    /// ```
    /// let rational: Rational = Rational::new(true, 7, 6).inverse();
    /// assert_eq!(rational, Rational::new(true, 6, 7));
    /// ```
    /// * Inverts -1.
    /// ```
    /// let rational: Rational = Rational::new(false, 1, 1).inverse();
    /// assert_eq!(rational, Rational::new(false, 1, 1));
    /// ```
    pub fn inverse(&self) -> Rational {
        Rational {
            positive: self.positive,
            numerator: self.denominator,
            denominator: self.numerator,
        }
    }

    /// Inverts a `Rational` instance.
    ///
    /// This method uses `inverse` internally.
    pub fn inv(&self) -> Rational {
        self.inverse()
    }
}

// Division
impl Div for Rational {
    type Output = Rational;

    /// Divides a `Rational` instance by another.
    ///
    /// # Arguments
    /// * `self` - The dividend.
    /// * `other` - The divisor.
    ///
    /// # Returns
    /// A `Rational` instance representing the Quotient of `self` divided by `other`.
    /// This uses multiplication and the `inv` method internally.
    /// So the result also is simplified using the `simplify` method.
    /// Mathematically p / q = p * q^-1.
    ///
    /// # Examples
    /// * Divides 5/6 by 2/3.
    /// ```
    /// let rational_1: Rational = Rational::new(true, 5, 6);
    /// let rational_2: Rational = Rational::new(true, 2, 3);
    /// let quotient: Rational = rational_1 / rational_2;
    /// assert_eq!(quotient, Rational::new(true, 5, 4));
    /// ```
    /// * Divides -2/7 by 1/8.
    /// ```
    /// let rational_1: Rational = Rational::new(false, 2, 7);
    /// let rational_2: Rational = Rational::new(true, 1, 8);
    /// let quotient: Rational = rational_1 / rational_2;
    /// assert_eq!(quotient, Rational::new(false, 16, 7));
    /// ```
    fn div(self: Rational, other: Rational) -> Self::Output {
        self * other.inv()
    }
}

// Addition
impl Add for Rational {
    type Output = Rational;

    /// Adds a `Rational` instance to another.
    ///
    /// # Arguments
    /// * `self` - The first summand.
    /// * `other` - The second summand.
    ///
    /// # Returns
    /// A `Rational` instance representing the sum of `self` and `other`.
    /// First the `common_denominator` method is used to get both summands on the same denominator and scale the numerators accordingly.
    /// This is implemented differentiating between all possible cases of combinations of signs and if one value is bigger than the other.
    /// In each case the sum also is simplified using the `simplify` method.
    ///
    /// # Examples
    /// * Adds 1/5 and 2/5.
    /// ```
    /// let rational_1: Rational = Rational::new(true, 1, 5);
    /// let rational_2: Rational = Rational::new(true, 2, 5);
    /// let sum: Rational = rational_1 + rational_2;
    /// assert_eq!(sum, Rational::new(true, 3, 5));
    /// ```
    /// * Adds 2/5 and 5/7.
    /// ```
    /// let rational_1: Rational = Rational::new(true, 2, 5);
    /// let rational_2: Rational = Rational::new(true, 5, 7);
    /// let sum: Rational = rational_1 + rational_2;
    /// assert_eq!(sum, Rational::new(true, 39, 35));
    /// ```
    /// * Adds 3/12 and -3/4.
    /// ```
    /// let rational_1: Rational = Rational::new(true, 3, 12);
    /// let rational_2: Rational = Rational::new(false, 3, 4);
    /// let sum: Rational = rational_1 + rational_2;
    /// assert_eq!(sum, Rational::new(false, 1, 2));
    /// ```
    ///
    /// # Notes
    /// This method can probably be simplified.
    fn add(self: Rational, other: Rational) -> Self::Output {
        let (rational_1, rational_2): (Rational, Rational) = self.common_denominator(&other);
        if rational_1.positive && rational_2.positive {
            Rational {
                positive: true,
                numerator: rational_1.numerator + rational_2.numerator,
                denominator: rational_1.denominator,
            }.simplify()
        } else if rational_1.positive && !rational_2.positive {
            if rational_1.numerator > rational_2.numerator {
                Rational {
                    positive: true,
                    numerator: rational_1.numerator - rational_2.numerator,
                    denominator: rational_1.denominator,
                }.simplify()
            } else {
                Rational {
                    positive: false,
                    numerator: rational_2.numerator - rational_1.numerator,
                    denominator: rational_1.denominator,
                }.simplify()
            }
        } else if !rational_1.positive && rational_2.positive {
            if rational_2.numerator > rational_1.numerator {
                Rational {
                    positive: true,
                    numerator: rational_2.numerator - rational_1.numerator,
                    denominator: rational_1.denominator,
                }.simplify()
            } else {
                Rational {
                    positive: false,
                    numerator: rational_1.numerator - rational_2.numerator,
                    denominator: rational_1.denominator,
                }.simplify()
            }
        } else {
            Rational {
                positive: false,
                numerator: rational_1.numerator + rational_2.numerator,
                denominator: rational_1.denominator,
            }.simplify()
        }
    }
}

// Negation
impl Neg for Rational {
    type Output = Rational;

    /// Negates a `Rational` instance.
    ///
    /// # Arguments
    /// `self` - A `Rational` instance.
    ///
    /// # Returns
    /// A `Rational` instance representing the negative of the `Rational` instance.
    /// This is achieved by just logically negating the `positive` attribute.
    /// For sake of consistency the result is simplified using the `simplify` method.
    ///
    /// # Examples
    /// * Negates 1/2.
    /// ```
    /// let rational: Rational = -Rational::new(true, 1, 2);
    /// assert_eq!(rational, Rational::new(false, 1, 2));
    /// ```
    /// * Negates -2/5.
    /// ```
    /// let rational: Rational = -Rational::new(false, 2, 5);
    /// assert_eq!(rational, Rational::new(true, 2, 5));
    /// ```
    /// * Negates 2/4.
    /// ```
    /// let rational: Rational = -Rational::new(true, 2, 4);
    /// assert_eq!(rational, Rational::new(false, 1, 2));
    /// ```
    fn neg(self: Rational) -> Self::Output {
        Rational {
            positive: !self.positive,
            numerator: self.numerator,
            denominator: self.denominator,
        }.simplify()
    }
}

// Subtraction
impl Sub for Rational {
    type Output = Rational;

    /// Subtracts a `Rational` instance from another.
    ///
    /// # Arguments
    /// * `self` - The minuend.
    /// * `other` - The subtrahend.
    ///
    /// # Returns
    /// A `Rational` instance representing the difference of `self` minus `other`.
    /// This uses addition and negation internally.
    /// So the result is also simplified using the `simplify` method.
    /// Mathematically p - q = p + (- q).
    ///
    /// # Examples
    /// * Subtracts 1/2 from 3/4.
    /// ```
    /// let rational_1: Rational = Rational::new(true, 3, 4);
    /// let rational_2: Rational = Rational::new(true, 1, 2);
    /// let difference: Rational = rational_1 - rational_2;
    /// assert_eq!(difference, Rational::new(true, 1, 4));
    /// ```
    /// * Subtracts 7/5 from 1/2.
    /// ```
    /// let rational_1: Rational = Rational::new(true, 1, 2);
    /// let rational_2: Rational = Rational::new(true, 7, 5);
    /// let difference: Rational = rational_1 - rational_2;
    /// assert_eq!(difference, Rational::new(false, 9, 10));
    /// ```
    /// * Subtracts -1/3 from 2/5.
    /// ```
    /// let rational_1: Rational = Rational::new(true, 2, 5);
    /// let rational_2: Rational = Rational::new(false, 1, 3);
    /// let difference: Rational = rational_1 - rational_2;
    /// assert_eq!(difference, Rational::new(true, 11, 15));
    /// ```
    fn sub(self: Rational, other: Rational) -> Self::Output {
        let rational_1: Rational = self;
        let rational_2: Rational = -other;
        (rational_1 + rational_2)
    }
}

// Power
impl Rational {
    /// Raises a `Rational` instance to an integer power.
    ///
    /// # Arguments
    /// * `self` - A reference to a `Rational` instance.
    /// * `power` (`IntegerType`) - The power.
    ///
    /// # Returns
    /// * If `power > 0`, both the numerator and denominator are raised to the power of the absolute value of `power`.
    /// * If `power < 0`, both the numerator and denominator are raised to the power of the absolute value of `power` and their position is flipped.
    /// * If `power == 0`, the result is 1/1.
    ///
    /// # Examples
    /// * Raises 1/2 to the second power.
    /// ```
    /// let rational: Rational = Rational::new(true, 1, 2).pow(2);
    /// assert_eq!(rational, Rational::new(true, 1, 4));
    /// ```
    /// * Raises -2/3 to the fourth power.
    /// ```
    /// let rational: Rational = Rational::new(false, 2, 3).pow(4);
    /// assert_eq!(rational, Rational::new(true, 16, 81));
    /// ```
    /// * Raises 2/3 to the negative second power.
    /// ```
    /// let rational: Rational = Rational::new(true, 2, 3).pow(-2);
    /// assert_eq!(rational, Rational::new(true, 9, 4));
    /// ```
    pub fn pow(&self, power: IntegerType) -> Rational {
        let sign: bool = if self.positive { true } else if power % 2 == 0 { true } else { false };
        if power > 0 {
            Rational {
                positive: sign,
                numerator: self.numerator.pow(power.abs() as NumberType),
                denominator: self.denominator.pow(power.abs() as NumberType),
            }
        } else if power < 0 {
            Rational {
                positive: sign,
                numerator: self.denominator.pow(power.abs() as NumberType),
                denominator: self.numerator.pow(power.abs() as NumberType),
            }
        } else {
            Rational::one()
        }
    }
}

// Evaluation
impl Rational {
    /// Evaluates a `Rational` instance.
    ///
    /// # Arguments
    /// `self` - A reference to a `Rational` instance.
    ///
    /// # Returns
    /// A float of `FloatType` representing the evaluated `Rational` instance.
    /// This is calculated by simply dividing the numerator by the denominator.
    ///
    /// # Examples
    /// * Evaluates 1/2.
    /// ```
    /// let rational: Rational = Rational::new(true, 1, 2);
    /// assert_eq!(rational.evaluate(), 0.5);
    /// ```
    /// * Evaluates -1/5.
    /// ```
    /// let rational: Rational = Rational::new(false, 1, 5);
    /// assert_eq!(rational.evaluate(), -0.2);
    /// ```
    pub fn evaluate(&self) -> FloatType {
        if self.positive {
            (self.numerator as FloatType) / (self.denominator as FloatType)
        } else {
            -(self.numerator as FloatType) / (self.denominator as FloatType)
        }
    }

    /// Evaluates a `Rational` instance.
    ///
    /// This uses the `evaluate` method internally.
    pub fn eval(&self) -> FloatType {
        self.evaluate()
    }
}

// Absolute Value
impl Rational {
    /// Calculates the absolute values of a `Rational` instance.
    ///
    /// # Arguments
    /// `self` - A reference to a `Rational` instance.
    ///
    /// # Returns
    /// The absolute value of a `Rational` instance by simply setting the `positive` Attribute to `true`.
    /// For sake of consistency the result is simplified using the `simplify` method.
    ///
    /// # Examples
    /// * Calculates the absolute value of 3/4.
    /// ```
    /// let rational: Rational = Rational::new(true, 3, 4);
    /// assert_eq!(rational.abs(), Rational::new(true, 3, 4));
    /// ```
    /// * Calculates the absolute value of -2/7.
    /// ```
    /// let rational: Rational = Rational::new(false, 2, 7);
    /// assert_eq!(rational.abs(), Rational::new(true, 2, 7));
    /// ```
    /// * Calculates the absolute value of -2/4.
    /// ```
    /// let rational: Rational = Rational::new(false, 2, 4);
    /// assert_eq!(rational.abs(), Rational::new(true, 1, 2));
    /// ```
    pub fn abs(&self) -> Rational {
        Rational {
            positive: true,
            numerator: self.numerator,
            denominator: self.denominator,
        }.simplify()
    }
}
