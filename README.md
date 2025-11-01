# Random Math Stuff in Rust

This project does not have any goals.
I will add some more or less useful math related stuff to this, so it can be reused in other projects.

## Overview
Currently implemented structs and methods.
- `Rational` struct
  - Basic arithmetic operations (+, -, *, /, ^)
  - Equations and orders (==, <=, >=, <, >)
  - Greatest common divisor and least common multiple
  - Simplification for reducible fractions
  - Evaluation
- `GaussianIntegers` struct
  - Basic arithmetic operations (+, -, *, /, %)
  - Equations (==)
  - Norm and complex conjugate
  - Greatest common divisors and least common multiples
- `Polynomials` struct
  - Basic arithmetic operations (+, -, *, /, %)
  - Equations (==)
  - Normalization
  - Greatest common divisors and least common multiples
  - Differentiation and integration

## Future Additions
- Complex numbers
- Matrices
- Trigonometric functions

## TODOs
- `is_prime` method for `GaussianIntegers`.
- `solve` method for `Polynomial`.
- `numeric_solve` for `Polynomial`.
- `approximate` for `Polynomial`.
- `factorice` for `Polynomial`.
