//! Factorial module.
//!
//! Since calculate fatorial is simple enought, we will only implement a iterator that
//! keeps giving a ever increasing factorial

use num::{BigUint, One};

/// Factorial iterator using big numbers;
#[derive(Debug, Clone)]
pub struct BigFactorial {
    /// Index we are in.
    index: u128,

    /// Last value calculated.
    ///
    /// We can do it without this value, but using it, we increase memory consuption, but
    /// the iterator became faster.
    value: BigUint,
}

impl BigFactorial {
    /// Creates a new iterator starting at 0;
    pub fn new() -> Self { BigFactorial { value: BigUint::one(), index: 0 } }

    pub fn at(index: u128) -> Self {
        BigFactorial { index, value: (1..index).map(BigUint::from).product() }
    }
}

impl Iterator for BigFactorial {
    type Item = BigUint;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index == 0 {
            self.index += 1;
            Some(BigUint::one())
        } else {
            self.value *= self.index;
            self.index += 1;
            Some(self.value.clone())
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
            .map(|x| BigUint::from(*x as u64))
            .collect();

        let test: Vec<_> = BigFactorial::new().take(sure.len()).collect();
        assert_eq!(sure, test);
    }

    #[test]
    fn iterator_bignum_at_test() {
        let sure: Vec<_> = vec![120, 720, 5040, 40320, 362_880, 3_628_800]
            .iter()
            .map(|x| BigUint::from(*x as u64))
            .collect();

        let test: Vec<_> = BigFactorial::at(5).take(sure.len()).collect();
        assert_eq!(sure, test);
    }
}
