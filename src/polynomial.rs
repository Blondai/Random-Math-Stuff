use std::cmp::{max, PartialEq};
use std::fmt::{Display, Formatter};
use std::ops::{Add, Div, Index, Mul, Neg, Rem, Sub};

/// The number type used for the coefficients and evaluation of the `Polynomial` instances.
/// By default, this is of type `f64`.
/// It will work for every other float type,
/// but some functionality could not work for other types like complex or integers.
pub type NumberType = f64;

#[derive(Clone, Debug)]
/// A struct for calculations involving single variable [polynomials](https://en.wikipedia.org/wiki/Polynomial).
/// Stores object in form of a `Vec` of coefficients starting at the zeroth power.
/// So vec!\[a_0, a_1, ..., a_n\] is equivalent to the polynomial a_0 x^0 + a_1 x^1 + ... + a_n x^n.
pub struct Polynomial {
    /// The coefficients of type `NumberType` describing the `Polynomial` instance.
    pub coefficients: Vec<NumberType>,
}

// Creation Macro
/// Creates a new `Polynomial` instance.
///
/// # Arguments
/// Any number of coefficients a_0, ..., a_n.
///
/// # Returns
/// A `Polynomial` instance representing a_0 x^0 + ... + a_n x^n.
/// This is initialized using `vec![a_0, ..., a_n]` and the `new` method.
///
/// # Examples
/// * Initializes 2 - 3.5 x + 5 x^2.
/// ```
/// let polynomial: Polynomial = poly!(2.0, -3.5, 5.0);
/// assert_eq!(polynomial, Polynomial::new(vec![2.0, -3.5, 5.0]));
/// ```
/// * Initializes 2 x - 1.3 x^4.
/// ```
/// let polynomial: Polynomial = poly!(0.0, 2.0, 0.0, 0.0, -1.3);
/// assert_eq!(polynomial, Polynomial::new(vec![0.0, 2.0, 0.0, 0.0, -1.3]));
/// ```
#[macro_export] macro_rules! poly {
    ($($coefficients:expr), *) => {
        Polynomial::new(vec![$($coefficients), *])
    };
}

// New
impl Polynomial {
    /// Creates a new `Polynomial` instance.
    ///
    /// # Arguments
    /// `coefficients` (`Vec<NumberType>`) - The coefficients of the polynomial starting from the zeroth power.
    ///
    /// # Returns
    /// A `Polynomial` instance representing the `coefficients`.
    ///
    /// # Examples
    /// * Initializes 2 - 3.5 x + 5 x^2.
    /// ```
    /// let polynomial: Polynomial = Polynomial::new(vec![2.0, -3.5, 5.0]);
    /// ```
    /// * Initializes 2 x - 1.3 x^4.
    /// ```
    /// let polynomial: Polynomial = Polynomial::new(vec![0.0, 2.0, 0.0, 0.0, -1.3]);
    /// ```
    ///
    /// # Notes
    /// It is advised to use the `poly!` macro.
    pub fn new(coefficients: Vec<NumberType>) -> Polynomial {
        Polynomial { coefficients }
    }

    /// Creates a new `Polynom` instance from a coefficient and a degree.
    ///
    /// # Arguments
    /// * `coefficient` (`NumberType`) - A coefficient.
    /// * `degree` (`usize`) - A degree where to put the coefficient.
    ///
    /// # Returns
    /// A `Polynomial` instance representing the monom with leading coefficient `coefficient` and degree `degree`.
    /// All coefficients before the leading coefficient are set to zero.
    ///
    /// # Examples
    /// * Initializes 2.9 x^2.
    ///
    pub fn monom(coefficient: NumberType, degree: usize) -> Polynomial {
        let mut coefficients: Vec<NumberType> = vec![0 as NumberType; degree];
        coefficients.push(coefficient);
        Polynomial::new(coefficients)
    }
}

// Special Values
impl Polynomial {
    /// Returns the zero polynomial, which is everywhere zero.
    ///
    /// # Returns
    /// A `Polynomial` representing the number zero everywhere.
    /// Mathematically f(x) = 0.
    ///
    /// # Examples
    /// Initializes the zero polynomial.
    /// ```
    /// let zero: Polynomial = Polynomial::zero();
    /// assert_eq!(zero, poly!(0.0));
    /// ```
    pub fn zero() -> Polynomial {
        Polynomial { coefficients: vec![0 as NumberType] }
    }

    /// Returns the one polynomial, which is everywhere one.
    ///
    /// # Returns
    /// A `Polynomial` representing the number one everywhere.
    /// Mathematically f(x) = 1.
    ///
    /// # Examples
    /// Initializes the one polynomial.
    /// ```
    /// let one: Polynomial = Polynomial::one();
    /// assert_eq!(one, poly!(1.0));
    /// ```
    pub fn one() -> Polynomial {
        Polynomial { coefficients: vec![1 as NumberType] }
    }

    /// Returns the identity polynomial, which is x.
    ///
    /// # Returns
    /// A `Polynomial` representing the identity function.
    /// Mathematically f(x) = x.
    ///
    /// # Examples
    /// Initializes the identity.
    /// ```
    /// let identity: Polynomial = Polynomial::identity();
    /// assert_eq!(identity, poly!(0.0, 1.0));
    /// ```
    pub fn identity() -> Polynomial {
        Polynomial { coefficients: vec![0 as NumberType, 1 as NumberType] }
    }

    /// Returns the identity polynomial, which is x.
    ///
    /// This method uses `identity` internally.
    pub fn id() -> Polynomial {
        Polynomial::identity()
    }
}

// Display
impl Display for Polynomial {
    /// Displays a `Polynomial` instance.
    ///
    /// This is sensitive to zero coefficients which are not printed.
    ///
    /// # Examples
    /// * Prints `0.9 + 1.8x + 2.5x^4`.
    /// ```
    /// let polynomial: Polynomial = poly!(0.9, 1.8, 0.0, 0.0, 2.5);
    /// println!("{}", polynomial);
    /// ```
    /// * Prints `0.1 + -2x + 0.8x^3`.
    /// ```
    /// let polynomial: Polynomial = poly!(0.1, -2.0, 0.0, 0.8);
    /// println!("{}", polynomial);
    /// ```
    ///
    /// # Notes
    /// This could be enhanced to also differentiate the case where the sign of a coefficient is negative.
    /// This would avoid `0.1 + -2x + 0.8x^3` and print `0.1 - 2x + 0.8x^3` instead.
    fn fmt(&self, format: &mut Formatter<'_>) -> std::fmt::Result {
        let mut terms: Vec<String> = vec![];
        for index in 0..self.deg() + 1 {
            let coefficient: NumberType = self[index];
            if coefficient != 0 as NumberType {
                let term = match index {
                    0 => format!("{}", coefficient),
                    1 => format!("{}x", coefficient),
                    _ => format!("{}x^{}", coefficient, index),
                };
                terms.push(term);
            }
        }
        write!(format, "{}", terms.join(" + "))
    }
}

// Simplify
impl Polynomial {
    /// Deletes unnecessary coefficients in a `coefficients` vector.
    ///
    /// # Arguments
    /// `self` - A `Polynomial` instance
    ///
    /// # Reruns
    /// A `Polynomial` instance representing the shortened polynomial.
    /// This is achieved by looking at the last coefficient and checking if it is close to zero.
    /// If the last coefficient is close to zero, he is popped and the step is repeated.
    /// If the last coefficient is not zero, the loop ends and a new `Polynomial` instance is returned.
    ///
    /// # Examples
    /// * Simplifies 0 + 1.2 x + 3.5 x^2 + 0 x^3 + 2.5 x^4 + 0 x^5 + 0 x^6.
    /// ```
    /// let polynomial: Polynomial = poly!(0.0, 1.2, 3.5, 0.0, 2.5, 0.0, 0.0);
    /// let simplified: Polynomial = polynomial.simplify();
    /// assert_eq!(simplified, poly!(0.0, 1.2, 3.5, 0.0, 2.5));
    /// ```
    /// * Simplifies 1.2 + 0.0 x + 2.9 x^2.
    /// ```
    /// let polynomial: Polynomial = poly!(1.2, 0.0, 2.9);
    /// let simplified: Polynomial = polynomial.simplify();
    /// assert_eq!(simplified, poly!(1.2, 0.0, 2.9));
    /// ```
    pub fn simplify(&self) -> Polynomial {
        let mut coefficients: Vec<NumberType> = self.coefficients.clone();
        while let Some(&last) = coefficients.last() {
            if last.abs() < NumberType::EPSILON && coefficients.len() > 1 {
                coefficients.pop();
            } else {
                break;
            }
        }
        Polynomial::new(coefficients)
    }
}

// Degree and leading coefficient
impl Polynomial {
    /// Calculates the degree (deg) of a `Polynomial` instance.
    ///
    /// # Arguments
    /// `self` - A reference to a `Polynomial` instance.
    ///
    /// # Returns
    /// A number of type `usize` representing the degree of the `Polynomial` instance.
    /// This is achieved by first simplifying the polynomial by using the `simplify` method one it.
    /// Afterward the `len` method is used on the `coefficient` attribute of the simplified polynomial.
    ///
    /// # Examples
    /// * Calculates the degree of 2 x + 5.5 x^2.
    /// ```
    /// let polynomial: Polynomial = poly!(0.0, 2.0, 5.5);
    /// let degree: usize = polynomial.degree();
    /// assert_eq!(degree, 2);
    /// ```
    /// * Calculates the degree of 0.8.
    /// ```
    /// let polynomial: Polynomial = poly!(0.8);
    /// let degree: usize = polynomial.degree();
    /// assert_eq!(degree, 0);
    /// ```
    pub fn degree(&self) -> usize {
        let polynomial: Polynomial = self.simplify();
        polynomial.coefficients.len() - 1
    }

    /// Calculates the degree (deg) of a `Polynomial` instance.
    ///
    /// This method uses `degree` internally.
    pub fn deg(&self) -> usize {
        self.degree()
    }

    /// Calculates the leading coefficient (lc) of a `Polynomial` instance.
    ///
    /// # Arguments
    /// `self` - A reference to a `Polynomial` instance.
    ///
    /// # Returns
    /// A number of type `NumberType` representing the leading coefficient.
    /// This is the coefficient at the monom with the highest exponent.
    /// This is achieved by calculating the degree using the `deg` method and returning the coefficient at that index.
    ///
    /// # Examples
    /// * Calculates the lc of 2.6 x^2 + 3.9 x^4.
    /// ```
    /// let polynomial: Polynomial = poly!(0.0, 0.0, 2.6, 3.9);
    /// let leading_coefficient: NumberType = polynomial.leading_coefficient();
    /// assert_eq!(leading_coefficient, 3.9);
    /// ```
    /// * Calculates the lc of 3.1 - 2.4 x^2.
    /// ```
    /// let polynomial: Polynomial = poly!(3.1, 0.0, -2.4);
    /// let leading_coefficient: NumberType = polynomial.leading_coefficient();
    /// assert_eq!(leading_coefficient, -2.4);
    /// ```
    pub fn leading_coefficient(&self) -> NumberType {
        self[self.deg()]
    }

    /// Calculates the leading coefficient (lc) of a `Polynomial` instance.
    ///
    /// This method uses `leading_coefficient` internally.
    pub fn lc(&self) -> NumberType {
        self.leading_coefficient()
    }
}

// Indexing
impl Index<usize> for Polynomial {
    type Output = NumberType;

    /// Returns the coefficient of a `Polynomial` belonging to the exponent of `index`.
    ///
    /// # Arguments
    /// * `self` - A reference to a `Polynomial` instance.
    /// * `index` (`usize`) - The exponent.
    ///
    /// # Returns
    /// A number of type `NumberType` representing the coefficient of the `Polynomial` at the exponent of `index`.
    /// For consistency if the index is bigger than the degree of the `Polynomial` instance a zero is returned.
    /// This is mathematically consistent with adding zero to anything.
    ///
    /// # Examples
    /// * Returns the coefficient of 2.3 x - 7.9 x^2 to the exponent 2.
    /// ```
    /// let polynomial: Polynomial = poly!(0.0, 2.3, -7.9);
    /// let coefficient: NumberType = polynomial[2];
    /// assert_eq!(coefficient, -7.9);
    /// ```
    /// * Returns the coefficient of 1.9 - 7.9 x to the exponent of 3.
    /// ```
    /// let polynomial: Polynomial = poly!(1.9, -7.9);
    /// let coefficient: NumberType = polynomial[3];
    /// assert_eq!(coefficient, 0.0);
    /// ```
    fn index(&self, index: usize) -> &NumberType {
        if index > self.deg() {
            &(0 as NumberType)
        } else {
            &self.coefficients[index]
        }
    }
}

// Equality
impl PartialEq for Polynomial {
    /// Compares two `Polynomial` instances for equality.
    ///
    /// Obviously two `Polynomial` instances are equal if all their coefficients are equal.
    ///
    /// # Arguments
    /// * `self` - A reference to the first `Polynomial` instance.
    /// * `other` - A reference to the second `Polynomial` instance.
    ///
    /// # Returns
    /// * `true` if both `Polynomial` have the same coefficients.
    /// * `false` otherwise.
    /// In this context same coefficients means, that the difference of every coefficient pair is smaller than NumberType::EPSILON.
    ///
    /// # Examples
    /// * Compares if 0.1 + x^2 is equal to 0.1 + x^2.
    /// ```
    /// let polynomial_1: Polynomial = poly!(0.1, 1.0);
    /// let polynomial_2: Polynomial = poly!(0.1, 1.0);
    /// assert!(polynomial_1 == polynomial_2);
    /// ```
    /// * Compares if 1.2 + x^3 is equal to 1.2 - x^3.
    /// ```
    /// let polynomial_1: Polynomial = poly!(1.2, 0.0, 1.0);
    /// let polynomial_2: Polynomial = poly!(1.2, 0.0, -1.0);
    /// assert!(polynomial_1 != polynomial_2);
    /// ```
    fn eq(self: &Polynomial, other: &Polynomial) -> bool {
        if self.deg() != other.deg() {
            return false;
        }
        for index in 0..=self.deg() {
            if (self[index] - other[index]).abs() > NumberType::EPSILON {
                return false;
            }
        }
        true
    }
}

// Evaluation
impl Polynomial {
    /// Evaluates a `Polynomial` instance at a `x_values`.
    ///
    /// # Arguments
    /// * `self` - A reference to a `Polynomial` instance.
    /// * `x_value` (`NumberType`) - A number to be evaluated.
    ///
    /// # Returns
    /// A number of type `NumberType` representing the `y_value` of the `Polynomial` instance at the `x_value`.
    /// This is calculated somewhat efficiently by not repeatedly exponentiating the `x_value`.
    ///
    /// # Examples
    /// * Evaluates 3.1 - 2.4 x^2 at 3.7.
    /// ```
    /// let polynomial: Polynomial = poly!(3.1, 0.0, -2.4);
    /// let y_value: NumberType = polynomial.evaluate(3.7);
    /// assert_eq!(y_value, -29.756);
    /// ```
    /// * Evaluates 1.3 x + 1.5 x^2 at -0.3.
    /// ```
    /// let polynomial: Polynomial = poly!(0.0, 1.3, 1.5);
    /// let y_value: NumberType = polynomial.evaluate(-0.3);
    /// assert_eq!(y_value, -0.255);
    /// ```
    /// # Notes
    /// Could probably be improved by using a better evaluation method.
    pub fn evaluate(&self, x_value: NumberType) -> NumberType {
        let mut y_value: NumberType = 0 as NumberType;
        let mut power: NumberType = 1 as NumberType;
        for index in 0..self.deg() + 1 {
            let coefficient: NumberType = self[index];
            if coefficient != 0 as NumberType {
                y_value += power * coefficient
            }
            power *= x_value;
        }
        y_value
    }

    /// Evaluates a `Polynomial` instance at a `x_values`.
    ///
    /// This method uses `evaluate` internally.
    pub fn eval(&self, x_value: NumberType) -> NumberType {
        self.evaluate(x_value)
    }

    /// Evaluates a `Polynomial` instance at a multiple `x_values`.
    ///
    /// This method uses `evaluate` internally.
    pub fn evals(&self, x_values: Vec<NumberType>) -> Vec<NumberType> {
        let mut y_values: Vec<NumberType> = Vec::new();
        for x_value in x_values {
            y_values.push(self.evaluate(x_value))
        }
        y_values
    }
}

// Addition
impl Add for Polynomial {
    type Output = Polynomial;

    /// Adds two `Polynomial` instances.
    ///
    /// # Arguments
    /// * `self` - The first summand.
    /// * `other` - The second summand.
    ///
    /// # Returns
    /// a `Polynomial` instance representing the sum of `self` and `other`.
    /// This is achieved by first calculating the largest degree with the `max` of the `deg` methods.
    /// Afterward the coefficients are added for each monom.
    ///
    /// # Examples
    /// * Adds 3 x^2 + 1.2 x^3 and 0.1 + 2 x + 0.8 x^3.
    /// ```
    /// let polynomial_1: Polynomial = poly!(0.0, 0.0, 3.0, 1.2);
    /// let polynomial_2: Polynomial = poly!(0.1, 2.0, 0.0, 0.8);
    /// let sum: Polynomial = polynomial_1 + polynomial_2;
    /// assert_eq!(sum, poly!(0.1, 2.0, 3.0, 2.0));
    /// ```
    /// * Adds 1.2 + 3.9 x and 2.5 x - 3.9 x^4.
    /// ```
    /// let polynomial_1: Polynomial = poly!(1.2, 3.9);
    /// let polynomial_2: Polynomial = poly!(0.0, 2.5, 0.0, 0.0, -3.9);
    /// let sum: Polynomial = polynomial_1 + polynomial_2;
    /// assert_eq!(sum, poly!(1.2, 6.4, 0.0, 0.0, -3.9));
    /// ```
    ///
    /// # Notes
    /// This could probably be simplified by only adding the coefficients up to the degree of the smaller degree `Polynomial`
    /// and copying the rest of the larger degree `Polynomial`.
    fn add(self: Polynomial, other: Polynomial) -> Self::Output {
        let degree: usize = max(self.deg(), other.deg());
        let mut coefficients: Vec<NumberType> = Vec::new();
        for index in 0..=degree {
            coefficients.push(self[index] + other[index])
        }
        Polynomial::new(coefficients).simplify()
    }
}

// Negation
impl Neg for Polynomial {
    type Output = Polynomial;

    /// Negates a `Polynomial` instance.
    ///
    /// # Arguments
    /// `self` - A `Polynomial` instance.
    ///
    /// # Returns
    /// A `Polynomial` instance representing the negative of `self`.
    /// This is achieved by negating each coefficient.
    ///
    /// # Examples
    /// Negates 1.2 - 3.5 x + 0.1 x^2.
    /// ```
    /// let polynomial: Polynomial = poly!(1.2, -3.5, 0.1);
    /// let negative: Polynomial = - polynomial;
    /// assert_eq!(negative, poly!(-1.2, 3.5, -0.1));
    /// ```
    fn neg(self: Polynomial) -> Self::Output {
        let mut coefficients: Vec<NumberType> = Vec::new();
        for index in 0..=self.deg() {
            coefficients.push(-self[index]);
        }
        Polynomial::new(coefficients).simplify()
    }
}

// Subtraction
impl Sub for Polynomial {
    type Output = Polynomial;

    /// Subtracts a `Polynomial` instance from another.
    ///
    /// # Arguments
    /// * `self` - The minuend.
    /// * `other` - The subtrahend.
    ///
    /// # Returns
    /// A `Polynomial` instance representing the difference of `self` and `other`.
    /// This uses addition and negation internally.
    /// Mathematically p - q = p + (-q).
    ///
    /// # Examples
    /// Subtracts 1.2 - 3.5 x + 2.9 x^3 from 2.2 + 3.7 x - x^2.
    /// ```
    /// let polynomial_1: Polynomial = poly!(2.2, 3.7, -1.0);
    /// let polynomial_2: Polynomial = poly!(1.1, -3.5, 0.0, 2.9);
    /// let difference: Polynomial = polynomial_1 - polynomial_2;
    /// assert_eq!(difference, poly!(1.1, 7.2, -1.0, -2.9));
    /// ```
    fn sub(self: Polynomial, other: Polynomial) -> Polynomial {
        self + (-other)
    }
}

// Multiplication
impl Mul for Polynomial {
    type Output = Polynomial;

    /// Multiplies two `Polynomial` instances.
    ///
    /// # Arguments
    /// * `self` - The first factor.
    /// * `other` - The second factor.
    ///
    /// # Returns
    /// A `Polynomial` instance representing the product of `self` and `other`.
    /// This is achieved by first noting that the degree of a nth degree polynomial multiplied by a mth degree polynomial is n + m.
    /// So the length of the new coefficient vector is the sum of those degree plus one.
    /// Afterward all the coefficients for each degree are collected and added accordingly.
    ///
    /// # Examples
    /// * Multiplies 1 + 2 x by 3 + 4 x.
    /// ```
    /// let polynomial_1: Polynomial = poly!(1.0, 2.0);
    /// let polynomial_2: Polynomial = poly!(3.0, 4.0);
    /// let product: Polynomial = polynomial_1 * polynomial_2;
    /// assert_eq!(product, poly!(3.0, 10.0, 8.0));
    /// ```
    /// * Multiplies 1.3 + 3.2 x^2 + 0.6 x^3 by 1.2 x + 0.1 x^2.
    /// ```
    /// let polynomial_1: Polynomial = poly!(1.3, 0.0, 3.2, 0.6);
    /// let polynomial_2: Polynomial = poly!(0.0, 1.2, 0.1);
    /// let product: Polynomial = polynomial_1 * polynomial_2;
    /// assert_eq!(product, poly!(0.0, 1.56, 0.13, 3.84, 1.04, 0.06));
    /// ```
    fn mul(self: Polynomial, other: Polynomial) -> Self::Output {
        let degree_1: usize = self.deg();
        let degree_2: usize = other.deg();
        let mut coefficients: Vec<NumberType> = vec![0 as NumberType; degree_1 + degree_2 + 1];
        for index in 0..=degree_1 {
            for jndex in 0..=degree_2 {
                coefficients[index + jndex] += self[index] * other[jndex];
            }
        }
        Polynomial::new(coefficients).simplify()
    }
}

// Long Division
impl Polynomial {
    /// Calculates quotient and remainder of a long division of two `Polynomial` instances.
    ///
    /// # Arguments
    /// * `self` - A reference to a `Polynomial` instance representing the dividend.
    /// * `other` - A reference to a `Polynomial` instance representing the divisor.
    ///
    /// # Returns
    /// * `quotient` (`Polynomial`) - The quotient of the division.
    /// * `remainder` (`Polynomial`) - The remainder of the division.
    ///
    /// # Examples
    /// * Divides 1 - 3 x + 2 x^3 by 1 - x.
    /// ```
    /// let polynomial_1: Polynomial = poly!(1.0, -3.0, 0.0, 2.0);
    /// let polynomial_2: Polynomial = poly!(1.0, -1.0);
    /// let (quotient, remainder): (Polynomial, Polynomial) = polynomial_1.long_division(&polynomial_2);
    /// assert_eq!(quotient, poly!(1.0, -2.0, -2.0));
    /// assert_eq!(remainder, poly!(0.0));
    /// ```
    /// * Divides 3 + x + x^2 by 5.
    /// ```
    /// let polynomial_1: Polynomial = poly!(-4.0, 0.0, -2.0, 1.0);
    /// let polynomial_2: Polynomial = poly!(-3.0, 1.0);
    /// let (quotient, remainder): (Polynomial, Polynomial) = polynomial_1.long_division(&polynomial_2);
    /// assert_eq!(quotient, poly!(3.0, 1.0, 1.0));
    /// assert_eq!(remainder, poly!(5.0));
    /// ```
    pub fn long_division(self: &Polynomial, other: &Polynomial) -> (Polynomial, Polynomial) {
        if *other == Polynomial::zero() {
            panic!("Can't divide by zero polynomial.")
        } else if self.deg() < other.deg() {
            return (Polynomial::zero(), self.clone());
        }

        let mut quotient_coefficients: Vec<NumberType> = vec![0.0; self.deg() - other.deg() + 1];
        let mut remainder_coefficients: Vec<NumberType> = self.coefficients.clone();

        let lc_divisor: NumberType = *other.coefficients.last().unwrap();

        while remainder_coefficients.len() >= other.coefficients.len() {
            let lc_dividend: NumberType = *remainder_coefficients.last().unwrap();
            let factor: NumberType = lc_dividend / lc_divisor;

            let degree_diff: usize = remainder_coefficients.len() - other.coefficients.len();
            quotient_coefficients[degree_diff] = factor;

            for index in 0..=other.deg() {
                remainder_coefficients[degree_diff + index] -= factor * other[index]
            }

            while let Some(&last) = remainder_coefficients.last() {
                if last.abs() < f64::EPSILON {
                    remainder_coefficients.pop();
                } else {
                    break;
                }
            }
        }

        if remainder_coefficients.len() == 0 {
            remainder_coefficients = vec![0 as NumberType];
        }

        (
            Polynomial::new(quotient_coefficients).simplify(),
            Polynomial::new(remainder_coefficients).simplify(),
        )
    }
}

// Division
impl Div for Polynomial {
    type Output = Polynomial;

    /// Divides a `Polynomial` instance by another. This is done using long division.
    ///
    /// # Arguments
    /// * `self` - The dividend.
    /// * `other` - The divisor.
    ///
    /// # Returns
    /// A `Polynomial` instance representing the quotient of `self` and `other`.
    /// This method uses `long_division` internally and deletes the `remainder` value.
    ///
    /// # Examples
    /// * Divides 1 - 3 x + 2 x^3 by 1 - x.
    /// ```
    /// let polynomial_1: Polynomial = poly!(1.0, -3.0, 0.0, 2.0);
    /// let polynomial_2: Polynomial = poly!(1.0, -1.0);
    /// let quotient: Polynomial = polynomial_1 / polynomial_2;
    /// assert_eq!(quotient, poly!(1.0, -2.0, -2.0));
    /// ```
    /// * Divides 3 + x + x^2 by 5.
    /// ```
    /// let polynomial_1: Polynomial = poly!(-4.0, 0.0, -2.0, 1.0);
    /// let polynomial_2: Polynomial = poly!(-3.0, 1.0);
    /// let quotient: Polynomial = polynomial_1 / polynomial_2;
    /// assert_eq!(quotient, poly!(3.0, 1.0, 1.0));
    /// ```
    fn div(self: Polynomial, other: Polynomial) -> Polynomial {
        let (quotient, _): (Polynomial, Polynomial) = self.long_division(&other);
        quotient
    }
}

// Remainder
impl Rem for Polynomial {
    type Output = Polynomial;

    /// Calculates the remainder of the long division of two `Polynomial` instances.
    ///
    /// # Arguments
    /// * `self` - The dividend.
    /// * `other` - The divisor.
    ///
    /// # Returns
    /// A `Polynomial` instance representing the remainder when dividing `self` by `other`.
    /// This method uses `long_division` internally and deletes the `quotient`value.
    ///
    /// # Examples
    /// * Calculates the remainder of 1 - 3 x + 2 x^3 divided by 1 - x.
    /// ```
    /// let polynomial_1: Polynomial = poly!(1.0, -3.0, 0.0, 2.0);
    /// let polynomial_2: Polynomial = poly!(1.0, -1.0);
    /// let remainder: Polynomial = polynomial_1 % polynomial_2;
    /// assert_eq!(remainder, poly!(0.0));
    /// ```
    /// * Calculates the remainder of 3 + x + x^2 divided by 5.
    /// ```
    /// let polynomial_1: Polynomial = poly!(-4.0, 0.0, -2.0, 1.0);
    /// let polynomial_2: Polynomial = poly!(-3.0, 1.0);
    /// let remainder: Polynomial = polynomial_1 % polynomial_2;
    /// assert_eq!(remainder, poly!(5.0));
    /// ```
    fn rem(self: Polynomial, other: Polynomial) -> Polynomial {
        let (_, remainder): (Polynomial, Polynomial) = self.long_division(&other);
        remainder
    }
}

// Norm
impl Polynomial {
    /// Normalizes a `Polynomial` instance by dividing every coefficient by the leading coefficient.
    ///
    /// # Arguments
    /// `self` - A reference to a `Polynomial` instance.
    ///
    /// # Returns
    /// A `Polynomial` instance representing the normalized `Polynomial`.
    /// This is achieved by getting the leading coefficient with the `lc` method
    /// and dividing each coefficient by the leading coefficient.
    /// To safe on unnecessary calculations, if the leading coefficient already is one, the division step is skipped.
    ///
    /// # Examples
    /// * Normalizes 2.1 + x - 2 x^2.
    /// ```
    /// let polynomial: Polynomial = poly!(4.0, 1.0, -2.0);
    /// let normalized: Polynomial = polynomial.normalize();
    /// assert_eq!(normalized, poly!(-2.0, -0.5, 1.0));
    /// ```
    /// * Normalizes 3.7 + 2.1 x + x^2.
    /// ```
    /// let polynomial: Polynomial = poly!(3.7, 2.1, 1.0);
    /// let normalized: Polynomial = polynomial.normalize();
    /// assert_eq!(normalized, poly!(3.7, 2.1, 1.0));
    /// ```
    pub fn normalize(&self) -> Polynomial {
        let mut coefficients: Vec<NumberType> = self.coefficients.clone();
        let lc: NumberType = self.lc();
        if lc == 1 as NumberType {
            return Polynomial::new(coefficients);
        }
        for index in 0..coefficients.len() {
            coefficients[index] = coefficients[index] / lc;
        }
        Polynomial::new(coefficients).simplify()
    }

    /// Returns a `Polynomial` instance with all positive coefficients.
    ///
    /// # Arguments
    /// `self` - A reference to a `Polynomial` instance.
    ///
    /// # Returns
    /// A `Polynomial` instance representing the original `Polynomial` instance with all positive coefficients.
    /// This is done by using the `abs` method on every coefficient.
    ///
    /// # Examples
    /// Returns all positive coefficients of - 1.2 + 3.6 x - 0.1 x^2 - 5.7 x^3.
    /// ```
    /// let polynomial: Polynomial = poly!(-1.2, 3.6, -0.1, -5.7);
    /// let cabs: Polynomial = polynomial.cabs();
    /// assert_eq!(cabs, poly!(1.2, 3.6, 0.1, 5.7));
    /// ```
    pub fn cabs(&self) -> Polynomial {
        let mut coefficients: Vec<NumberType> = self.coefficients.clone();
        for index in 0..=self.deg() {
            coefficients[index] = coefficients[index].abs();
        }
        Polynomial::new(coefficients).simplify()
    }
}

// Greatest Common Divisor
impl Polynomial {
    /// Calculates a greatest common divisor (gcd) of two `Polynomial` instances using the Euclidean Algorithm.
    /// The greatest common divisor is the biggest number dividing both gaussian integers without remainder.
    /// This value is not unique and can be scaled by any number of type `NumberType`.
    ///
    /// # Arguments
    /// * `polynomial_1` (`Polynomial`) - The first polynomial.
    /// * `polynomial_2` (`Polynomial`) - The second polynomial.
    ///
    /// # Returns
    /// A `Polynomial` instance representing the gcd of `polynomial_1` and `polynomial_2`.
    ///
    /// # Examples
    /// Calculates the gcd of 6 + 7 x + x^2 and - 6 - 5 x + x^2.
    /// ```
    /// let polynomial_1: Polynomial = poly!(6.0, 7.0, 1.0);
    /// let polynomial_2: Polynomial = poly!(-6.0, -5.0, 1.0);
    /// let gcd: Polynomial = Polynomial::greatest_common_divisor(polynomial_1, polynomial_2);
    /// assert_eq!(gcd, poly!(12.0, 12.0));
    /// ```
    pub fn greatest_common_divisor(mut polynomial_1: Polynomial, mut polynomial_2: Polynomial) -> Polynomial {
        while polynomial_2 != Polynomial::zero() {
            let auxiliary: Polynomial = polynomial_1 % polynomial_2.clone();
            polynomial_1 = polynomial_2;
            polynomial_2 = auxiliary
        }
        polynomial_1.simplify()
    }

    /// Calculates the canonical greatest common divisor.
    ///
    /// # Arguments
    /// * `self` - A reference to the first `Polynomial` instance.
    /// * `other` - A reference to the second `Polynomial` instance.
    ///
    /// # Result
    /// A `Polynomial` instance representing the canonical representation of the greatest common divisor.
    /// This is the greatest common divisor with leading coefficient one.
    /// It is calculated by using the `greatest_common_divisor` method to get a greatest common divisor
    /// and normalizing it with the `normalize` method.
    ///
    /// # Examples
    /// Calculates the gcd of 6 + 7 x + x^2 and - 6 - 5 x + x^2.
    /// ```
    /// let polynomial_1: Polynomial = poly!(6.0, 7.0, 1.0);
    /// let polynomial_2: Polynomial = poly!(-6.0, -5.0, 1.0);
    /// let gcd: Polynomial = polynomial_1.gcd(&polynomial_2);
    /// assert_eq!(gcd, poly!(1.0, 1.0));
    /// ```
    pub fn gcd(self: &Polynomial, other: &Polynomial) -> Polynomial {
        let polynomial_1: Polynomial = self.clone();
        let polynomial_2: Polynomial = other.clone();
        let gcd: Polynomial = Polynomial::greatest_common_divisor(polynomial_1, polynomial_2);
        gcd.normalize()
    }
}

// Least Common Multiple
impl Polynomial {
    /// Calculates the canonical least common multiple of two `Polynomial` instances.
    ///
    /// # Arguments
    /// * `polynomial_1` (`Polynomial`) - The first polynomial.
    /// * `polynomial_2` (`Polynomial`) - The second polynomial.
    ///
    /// # Returns
    /// A `Polynomial` instance representing the canonical least common multiple.
    /// This is calculated by calculating one greatest common divisor with the `greatest_common_divisor` method
    /// and using its definition.
    ///
    /// # Examples
    /// Calculates the lcm of 6 + 7 x + x^2 and - 6 - 5 x + x^2.
    /// ```
    /// let polynomial_1: Polynomial = poly!(6.0, 7.0, 1.0);
    /// let polynomial_2: Polynomial = poly!(-6.0, -5.0, 1.0);
    /// let lcm: Polynomial = polynomial_1.least_common_multiple(&polynomial_2);
    /// assert_eq!(lcm, poly!(-36.0, -36.0, 1.0, 1.0));
    /// ```
    pub fn least_common_multiple(self: &Polynomial, other: &Polynomial) -> Polynomial {
        (self.clone() * other.clone() / self.gcd(other)).simplify()
    }

    /// Calculates the canonical least common multiple of two `Polynomial` instances.
    ///
    /// This method uses `least_common_multiple` internally.
    pub fn lcm(self: &Polynomial, other: &Polynomial) -> Polynomial {
        self.least_common_multiple(other)
    }
}

// Differentiation
impl Polynomial {
    /// Differentiates a `Polynomial` instance.
    ///
    /// # Arguments
    /// `self` - A reference to a `Polynomial` instance.
    ///
    /// # Returns
    /// A `Polynomial` instance representing the derivative of the `Polynomial` instance.
    /// If the degree of `self` ist less than one, the zero `Polynomial` is returned.
    /// Otherwise, the coefficients are shifted one to the left and multiplied by there old index.
    ///
    /// # Examples
    /// * Differentiates 6 + 7 x + x^2 + 2 x^3 + 3 x^4.
    /// ```
    /// let polynomial: Polynomial = poly!(6.0, 7.0, 1.0, 2.0, 3.0);
    /// let derivative: Polynomial = polynomial.differentiate();
    /// assert_eq!(derivative, poly!(7.0, 2.0, 6.0, 12.0));
    /// ```
    /// * Differentiates 5.
    /// ```
    /// let polynomial: Polynomial = poly!(5.0);
    /// let derivative: Polynomial = polynomial.differentiate();
    /// assert_eq!(derivative, poly!(0.0));
    /// ```
    pub fn differentiate(&self) -> Polynomial {
        let degree: usize = self.deg();
        if degree < 1 {
            return Polynomial::zero();
        }
        let mut coefficients: Vec<NumberType> = Vec::new();
        for index in 1..=degree {
            coefficients.push(self[index] * index as NumberType);
        }
        Polynomial::new(coefficients).simplify()
    }

    /// Differentiates a `Polynomial` instance.
    ///
    /// This method uses `differentiate` internally.
    pub fn diff(&self) -> Polynomial {
        self.differentiate()
    }

    /// Differentiates a `Polynomial` instance multiple times.
    ///
    /// # Arguments
    /// * `self` - A reference to a `Polynomial` instance.
    /// * `number` (`usize`) - The number of differentiations.
    ///
    /// # Returns
    /// A `Polynomial` instance representing the `number`th derivative of a `Polynomial` instance.
    /// This is achieved by calling the `differentiate` method `number` times.
    ///
    /// # Examples
    /// Differentiates 2.9 + x + 5 x^2 + 3 x^3 + 1.5 x^4 + x^5 + 0.25 x^6 three times.
    /// ```
    /// let polynomial: Polynomial = poly!(2.9, 1.0, 5.0, 3.0, 1.5, 1.0, 0.25);
    /// let derivative: Polynomial = polynomial.diffs(3);
    /// assert_eq!(derivative, poly!(18.0, 36.0, 60.0, 30.0));
    /// ```
    pub fn diffs(&self, number: usize) -> Polynomial {
        let mut derivative: Polynomial = self.clone();
        for _ in 0..number {
            derivative = derivative.differentiate()
        }
        derivative
    }
}

// Integration
impl Polynomial {
    /// Returns the canonical antiderivative of a `Polynomial` instance.
    ///
    /// # Arguments
    /// `self` - A reference to a `Polynomial` instance.
    ///
    /// # Returns
    /// A `Polynomial` instance representing the canonical antiderivative of the `Polynomial` instance.
    /// Canonical means in this case, that the constant added is zero.
    ///
    /// # Examples
    /// * Integrates 1 + 2 x + 3 x^2 + 4 x^3.
    /// ```
    /// let polynomial: Polynomial = poly!(1.0, 2.0, 3.0, 4.0);
    /// let antiderivative: Polynomial = polynomial.integrate();
    /// assert_eq!(antiderivative, poly!(0.0, 1.0, 1.0, 1.0, 1.0));
    /// ```
    /// * Integrate 4.
    /// ```
    /// let polynomial: Polynomial = poly!(4.0);
    /// let antiderivative: Polynomial = polynomial.integrate();
    /// assert_eq!(antiderivative, poly!(0.0, 4.0));
    /// ```
    /// * Integrate 0.
    /// ```
    /// let polynomial: Polynomial = poly!(0.0);
    /// let antiderivative: Polynomial = polynomial.integrate();
    /// assert_eq!(antiderivative, poly!(0.0));
    /// ```
    pub fn integrate(&self) -> Polynomial {
        let degree: usize = self.deg();
        let mut coefficients: Vec<NumberType> = vec![0 as NumberType];
        for index in 1..=degree + 1 {
            coefficients.push(self[index - 1] / index as NumberType);
        }
        Polynomial::new(coefficients).simplify()
    }

    /// Returns the canonical antiderivative of a `Polynomial` instance.
    ///
    /// This method uses `integrate` internally.
    pub fn int(&self) -> Polynomial {
        self.integrate()
    }

    /// Integrates a `Polynomial` instance multiple times.
    ///
    /// # Arguments
    /// * `self` - A reference to a `Polynomial` instance.
    /// * `number` (`usize`) - The number of integrations.
    ///
    /// # Returns
    /// A `Polynomial` instance representing the `number`th antiderivative of a `Polynomial` instance.
    /// This is achieved by calling the `integrate` method `number` times.
    ///
    /// # Examples
    /// Integrate 0.7 + 6 x^2 + 12 x^3 two times.
    /// ```
    /// let polynomial: Polynomial = poly!(0.7, 6.0, 24.0);
    /// let antiderivative: Polynomial = polynomial.ints(2);
    /// assert_eq!(antiderivative, poly!(0.0, 0.0, 0.35, 1.0, 2.0));
    /// ```
    pub fn ints(&self, number: usize) -> Polynomial {
        let mut antiderivative: Polynomial = self.clone();
        for _ in 0..number {
            antiderivative = antiderivative.int()
        }
        antiderivative
    }

    /// Returns the antiderivative of a `Polynomial` instance with a constant.
    ///
    /// # Arguments
    /// * `self` - A reference to a `Polynomial` instance.
    /// * `constant` (`NumberType`) - The constant to add to the canonical antiderivative.
    ///
    /// # Returns
    /// A `Polynomial` instance representing the antiderivative with `constant` as a constant term.
    /// This is achieved by getting the antiderivative with the `integrate` method
    /// and setting the constant coefficient to `constant`.
    ///
    /// # Examples
    /// * Calculates the antiderivative of 1 + 2 x + 3 x^2 + 4 x^4 with con constant 1.3.
    /// ```
    /// let polynomial: Polynomial = poly!(1.0, 2.0, 3.0, 4.0);
    /// let antiderivative: Polynomial = polynomial.const_int(1.3);
    /// assert_eq!(antiderivative, poly!(1.3, 1.0, 1.0, 1.0, 1.0));
    /// ```
    /// * Calculates the antiderivative of 0 with con constant 5.5.
    /// ```
    /// let polynomial: Polynomial = poly!(0.0);
    /// let antiderivative: Polynomial = polynomial.const_int(5.5);
    /// assert_eq!(antiderivative, poly!(5.5));
    /// ```
    pub fn const_int(&self, constant: NumberType) -> Polynomial {
        let mut antiderivative: Polynomial = self.integrate();
        antiderivative.coefficients[0] = constant;
        antiderivative
    }

    /// Returns the canonical antiderivative of a `Polynomial` instance.
    ///
    /// This method uses `integrate` internally.
    pub fn antiderivative(&self) -> Polynomial {
        self.integrate()
    }

    /// Returns the area between the graph of a `Polynomial` instance and the x-axis.
    ///
    /// # Arguments
    /// * `self` - A reference to a `Polynomial` instance.
    /// * `lower_bound` (`NumberType`) - The lower integration boundary.
    /// * `upper_bound` (`NumberType`) - The upper integration boundary.
    ///
    /// # Returns
    /// A number of type `NumberType` representing the area between the graph of a `Polynomial` instance and the x-axis.
    /// This is calculated by getting the antiderivative using the `integrate` method
    /// and evaluating it at the upper- and lower bound using the `evaluate` method.
    ///
    /// # Examples
    /// * Calculates the integral of x from -1 to 1.
    /// ```
    /// let polynomial: Polynomial = poly!(0.0, 1.0);
    /// let area: NumberType = polynomial.area(-1.0, 1.0);
    /// assert_eq!(area, 0.0);
    /// ```
    /// * Calculates the integral of 1 - x^2 from -1 to 1.
    /// ```
    /// let polynomial: Polynomial = poly!(1.0, -1.0);
    /// let area: NumberType = polynomial.area(-1.0, 1.0);
    /// assert_eq!(area, 2.0);
    /// ```
    pub fn area(&self, lower_bound: NumberType, upper_bound: NumberType) -> NumberType {
        let antiderivative: Polynomial = self.integrate();
        antiderivative.evaluate(upper_bound) - antiderivative.evaluate(lower_bound)
    }
}
