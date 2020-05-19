//! Factorial module.
//!
//! Since calculate fatorial is simple enought, we will only implement the iterator that
//! keeps giving a ever increasing number.
//!
//! _Only implement for big numbers cause the number grows big super fast._

use num::{BigUint, One};

/// Factorial iterator using big numbers.
///
/// # Example
/// Print the 100 first factorial numbers.
///
/// ```rust
/// # use algos::numerics::BigFactorial;
/// # fn main() {
/// BigFactorial::new().enumerate().take(100).for_each(|(i, v)| println!("{}!: {}", i, v));
/// # }
/// ```
#[derive(Debug, Clone)]
pub struct BigFactorial {
    /// Index we are in.
    index: u128,

    /// Last value calculated.
    ///
    /// We can do it without this value, but using it, we increase memory consuption, but
    /// the iterator became faster.
    last: BigUint,
}

impl BigFactorial {
    /// Creates a new iterator starting at the first number of the sequence.
    pub fn new() -> Self { BigFactorial { last: BigUint::one(), index: 0 } }

    /// Create a new iterator with the first factorial number beeing the `nth` factorial
    /// number.
    pub fn at(nth: impl Into<u128>) -> Self {
        let index = nth.into();
        BigFactorial { index, last: (1..index).map(BigUint::from).product() }
    }
}

impl Iterator for BigFactorial {
    type Item = BigUint;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index == 0 {
            self.index += 1;
            Some(BigUint::one())
        } else {
            self.last *= self.index;
            self.index += 1;
            Some(self.last.clone())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn iterator_bignum_test() {
        let sure: Vec<_> = vec![1, 1, 2, 6, 24, 120, 720, 5040, 40320, 362_880, 3_628_800]
            .iter()
            .map(|&x| BigUint::from(x as u64))
            .collect();

        let test: Vec<_> = BigFactorial::new().take(sure.len()).collect();
        assert_eq!(sure, test);
    }

    #[test]
    fn iterator_bignum_at_test() {
        let sure: Vec<_> = vec![120, 720, 5040, 40320, 362_880, 3_628_800]
            .iter()
            .map(|&x| BigUint::from(x as u64))
            .collect();

        let test: Vec<_> = BigFactorial::at(5u32).take(sure.len()).collect();
        assert_eq!(sure, test);
    }
}
