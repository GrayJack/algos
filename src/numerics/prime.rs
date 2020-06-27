use num::{integer::Roots, One, Zero};

#[cfg(feature = "big_num")]
use num::{BigInt, BigUint};

/// Trait to be implemented by types that makes sense having prime numbers
pub trait IsPrime {
    /// Check if the number is prime
    fn is_prime(&self) -> bool;
}

/// Simple implementation for the sqrt for integers (for educational porpuses)
/// All other parts of the code uses the `num` crate implementation, that have better
/// performance.
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

#[cfg(feature = "big_num")]
impl IsPrime for BigUint {
    fn is_prime(&self) -> bool {
        if self.is_zero() || self.is_one() {
            return false;
        }

        num::range_inclusive(BigUint::from(2u8), self.sqrt()).all(|x| self % x != BigUint::zero())
    }
}

#[cfg(feature = "big_num")]
impl IsPrime for BigInt {
    fn is_prime(&self) -> bool {
        if self.is_zero() || self.is_one() || *self < BigInt::zero() {
            return false;
        }

        num::range_inclusive(BigInt::from(2u8), self.sqrt()).all(|x| self % x != BigInt::zero())
    }
}

macro_rules! impl_is_prime_unsigned {
    ($($t:ty)+) => {
        $(
        impl IsPrime for $t {
            fn is_prime(&self) -> bool {
                match self {
                    0 | 1 => false,
                    _ => (2..=self.sqrt()).all(|a| *self % a != 0),
                }
            }
        }
        )+
    };
}

macro_rules! impl_is_prime_signed {
    ($($t:ty)+) => {
        $(
        impl IsPrime for $t {
            fn is_prime(&self) -> bool {
                match self {
                    0 | 1 => false,
                    _ if self < &0 => false,
                    _ => (2..=self.sqrt()).all(|a| *self % a != 0),
                }
            }
        }
        )+
    };
}

impl_is_prime_signed!(i8 i16 i32 i64 i128);
impl_is_prime_unsigned!(u8 u16 u32 u64 u128);

#[cfg(test)]
mod tests {
    use super::*;

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
            assert_eq!(true, x.is_prime())
        }

        let not_primes: Vec<_> = vec![4u8, 6, 8, 9, 10, 12, 14, 15, 16, 18, 20]
            .iter()
            .map(|&x| BigUint::from(x))
            .collect();

        for x in not_primes {
            assert_eq!(false, x.is_prime())
        }
    }

    #[test]
    fn is_prime_test() {
        let sure = vec![
            2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83,
            89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179,
            181, 191, 193, 197, 199,
        ];

        for x in sure {
            assert_eq!(true, x.is_prime())
        }

        let not_primes = vec![4, 6, 8, 9, 10, 12, 14, 15, 16, 18, 20];

        for x in not_primes {
            assert_eq!(false, x.is_prime(), "{}", x)
        }
    }
}
