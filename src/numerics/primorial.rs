//! Primorial
#[cfg(feature = "big_num")]
use num::{BigUint, One, Zero};

/// Primorial iterator using big numbers.
///
/// # Example
/// Print the 100 first primorial numbers.
///
/// ```rust
/// # use algos::numerics::BigPrimorial;
/// # fn main() {
/// BigPrimorial::new().enumerate().take(100).for_each(|(i, v)| println!("{}#: {}", i, v));
/// # }
/// ```
#[cfg(feature = "big_num")]
#[derive(Debug, Clone)]
pub struct BigPrimorial {
    /// Index we are in.
    index: u128,
    /// Last value calculated.
    ///
    /// We can do it without this value, but using it, we increase memory consuption, but
    /// the iterator became faster.
    last:  BigUint,
}

#[cfg(feature = "big_num")]
impl BigPrimorial {
    /// Creates a new iterator starting at the first number of the sequence.
    pub fn new() -> Self { BigPrimorial { index: 0, last: BigUint::one() } }

    /// Create a new iterator with the first factorial number beeing the `nth` factorial
    /// number.
    pub fn at(nth: impl Into<u128>) -> Self {
        let index = nth.into();
        BigPrimorial { index, last: primorial_big(index) }
    }
}

#[cfg(feature = "big_num")]
impl Iterator for BigPrimorial {
    type Item = BigUint;

    fn next(&mut self) -> Option<Self::Item> {
        let next = self.last.clone();

        self.index += 1;
        if is_prime_big(self.index) {
            self.last *= self.index;
        }

        Some(next)
    }
}

/// Return the nth primorial number using big numbers.
///
/// # Panics
/// This function may panic if there the computer run out of memory.
#[cfg(feature = "big_num")]
pub fn primorial_big(index: impl Into<BigUint>) -> BigUint {
    let index = index.into();

    num::range_inclusive(BigUint::one(), index).filter(|x| is_prime_big(x.clone())).product()
}

/// Return the nth primorial number using big numbers.
///
/// # Panics
/// This function may panic if there the computer run out of memory.
#[cfg(feature = "big_num")]
pub fn recursive_primorial_big(index: impl Into<BigUint>) -> BigUint {
    let index = index.into();

    if index.is_zero() || index.is_one() {
        return BigUint::one();
    }

    if is_prime_big(index.clone()) {
        return &index * primorial_big((&index) - BigUint::one());
    }

    primorial_big((&index) - BigUint::one())
}


/// Check if given `num`ber is a prime number.
#[cfg(feature = "big_num")]
pub fn is_prime_big(num: impl Into<BigUint>) -> bool {
    let num = num.into();

    if num.is_zero() || num.is_one() {
        return false;
    }

    num::range_inclusive(BigUint::from(2u8), num.sqrt()).all(|x| &num % x != BigUint::zero())
}


/// Return the nth primorial number using the biggest integer primitive.
///
/// # Panics
/// This function may panic in debug mode if there is a operation with overflow. It will
/// happen when `index` ≥ 103.
pub fn primorial(index: u128) -> u128 { (1..=index).filter(|&x| is_prime(x)).product() }

/// Return the nth primorial number using the biggest integer primitive.
///
/// # Panics
/// This function may panic in debug mode if there is a operation with overflow. It will
/// happen when `index` ≥ 103.
/// This also may panic it it reachest stack overflow due it's recursive nature and Rust
/// lack of tail call optimization. _Note that there is a change that LLVM generate a code
/// that this doesn't happen when in release mode_
pub fn recursive_primorial(index: u128) -> u128 {
    match index {
        0 | 1 => 1,
        _ if is_prime(index) => index * primorial(index - 1),
        _ => primorial(index - 1),
    }
}

/// Check if given `num`ber is a prime number.
pub fn is_prime(num: u128) -> bool {
    match num {
        0 | 1 => false,
        _ => (2..=isqrt(num)).all(|a| num % a != 0),
    }
}

/// Calculate integer sqrt aproximation for u128.
// TODO(grayjack): Optimize this function.
pub fn isqrt(num: u128) -> u128 {
    let mut shift = 2;
    let mut nshifted = num >> shift;

    while nshifted != 0 && nshifted != num {
        shift += 2;
        nshifted = num >> shift;
    }

    shift -= 2;

    let mut result = 0;
    while shift >= 0 {
        result <<= 1;
        let candidate_res = result + 1;

        if candidate_res * candidate_res <= num >> shift {
            result = candidate_res
        }

        shift -= 2
    }

    result
}


#[cfg(test)]
mod tests {
    use super::*;
    use num::BigUint;

    #[test]
    fn iterator_test() {
        let sure: Vec<_> = vec![1u16, 1, 2, 6, 6, 30, 30, 210, 210, 210, 210, 2310]
            .iter()
            .map(|&x| BigUint::from(x))
            .collect();

        let test: Vec<_> = BigPrimorial::new().take(sure.len()).collect();

        assert_eq!(sure, test)
    }

    #[test]
    fn primorial_big_test() {
        let sure: Vec<_> = vec![1u16, 1, 2, 6, 6, 30, 30, 210, 210, 210, 210, 2310]
            .iter()
            .map(|&x| BigUint::from(x))
            .collect();

        let tests: Vec<_> = (0..sure.len() as u128).map(primorial_big).collect();

        assert_eq!(sure, tests)
    }

    #[test]
    fn recursive_primorial_big_test() {
        let sure: Vec<_> = vec![1u16, 1, 2, 6, 6, 30, 30, 210, 210, 210, 210, 2310]
            .iter()
            .map(|&x| BigUint::from(x))
            .collect();

        let tests: Vec<_> = (0..sure.len() as u128).map(recursive_primorial_big).collect();

        assert_eq!(sure, tests)
    }

    #[test]
    fn is_prime_big_test() {
        let sure: Vec<_> = vec![
            2u8, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79,
            83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173,
            179, 181, 191, 193, 197, 199,
        ]
        .iter()
        .map(|&x| BigUint::from(x))
        .collect();

        for x in sure {
            assert_eq!(true, is_prime_big(x))
        }

        let not_primes: Vec<_> = vec![4u8, 6, 8, 9, 10, 12, 14, 15, 16, 18, 20]
            .iter()
            .map(|&x| BigUint::from(x))
            .collect();

        for x in not_primes {
            assert_eq!(false, is_prime_big(x))
        }
    }

    #[test]
    fn primorial_test() {
        let sure = vec![1, 1, 2, 6, 6, 30, 30, 210, 210, 210, 210, 2310];
        let tests: Vec<_> = (0..sure.len() as u128).map(primorial).collect();

        assert_eq!(sure, tests)
    }

    #[test]
    fn recursive_primorial_test() {
        let sure = vec![1, 1, 2, 6, 6, 30, 30, 210, 210, 210, 210, 2310];
        let tests: Vec<_> = (0..sure.len() as u128).map(recursive_primorial).collect();

        assert_eq!(sure, tests)
    }

    #[test]
    fn is_prime_test() {
        let sure = vec![
            2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83,
            89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179,
            181, 191, 193, 197, 199,
        ];

        for x in sure {
            assert_eq!(true, is_prime(x))
        }

        let not_primes = vec![4, 6, 8, 9, 10, 12, 14, 15, 16, 18, 20];

        for x in not_primes {
            assert_eq!(false, is_prime(x), "{}", x)
        }
    }
}
