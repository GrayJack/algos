/**************************************************************************************************
* Copyright 2018 GrayJack
* All rights reserved.
*
* This Source Code Form is subject to the terms of the BSD 3-Clause License.
**************************************************************************************************/

//! A module for using searching algorithms.
//!
//! The array **must** be crescent ordered.

use std::cmp::*;

/// **Linear Search:** Search for the value 'x' in an array.
///
/// Returns `Err` holding the last iterator if 'x' not found and array[i] > x.
///
///
/// |   Case    | Time complexity | Space complexity |
/// |:----------|:---------------:|:----------------:|
/// | Best:     | Ω(1)            |                  |
/// | Avrg:     | θ(n)            |                  |
/// | Worst:    | O(n)            | O(1)             |
///
/// # Example
/// ```rust
/// use algos::search;
///
/// let v = [1, 3, 4, 8, 11, 17, 23];
///
/// let find = search::linear(&v, &11);
/// assert_eq!(find, Ok(4));
///
/// let find2 = search::linear(&v, &19);
/// assert_eq!(find2, Err(6));
/// ```
pub fn linear<T: Ord>(a: &[T], x: &T) -> Result<usize,usize> {
    for (i, e) in a.iter().enumerate() {
        if e == x {
            return Ok(i);
        }
        else if e > x {
            return Err(i);
        }
    }
    Err(0)
}

/// **Binary Search:** Search for the value 'x' in an array.
///
/// Returns `Err` holding the leftmost term if 'x' not found.
///
///
/// |   Case    | Time complexity | Space complexity |
/// |:----------|:---------------:|:----------------:|
/// | Best:     | Ω(1)            |                  |
/// | Avrg:     | θ(log(n))       |                  |
/// | Worst:    | O(log(n))       | O(1)             |
///
/// # Example
/// ```rust
/// use algos::search;
///
/// let v = [1, 3, 4, 8, 11, 17, 23];
///
/// let find = search::binary(&v, 11);
/// assert_eq!(find, Ok(4));
///
/// let find2 = search::binary(&v, 19);
/// assert_eq!(find2, Err(6));
/// ```
pub fn binary<T: Ord>(a: &[T], x: T) -> Result<usize,usize> {
    let (mut l, mut r) = (0, a.len());
    // Looks like I'm unable to make a recursive implementation, so I made interative.
    while l <= r {
        // This has the same result as (l+r)/2, but it's probably the same or faster.
        let mid = (l+r) >> 1;

        if a[mid] > x {
            r = mid - 1;
        }
        else if a[mid] < x {
            l = mid + 1;
        }
        else {
            return Ok(mid);
        }
    }
    Err(l)
}

/// **Exponential Search:** Search for the value 'x' in an array.
///
/// Returns `Err` holding the leftmost term if 'x' not found.
///
/// **Obs.:** Variation of binary search.
///
/// |   Case    | Time complexity | Space complexity |
/// |:----------|:---------------:|:----------------:|
/// | Best:     | Ω(1)            |                  |
/// | Avrg:     | θ(log(n))       |                  |
/// | Worst:    | O(log(n))       | O(1)             |
///
/// # Example
/// ```rust
/// use algos::search;
///
/// let v = [1, 3, 4, 8, 11, 17, 23];
///
/// let find = search::exponential(&v, 11);
/// assert_eq!(find, Ok(4));
///
/// let find2 = search::exponential(&v, 19);
/// assert_eq!(find2, Err(6));
/// ```
pub fn exponential<T: Ord>(a: &[T], x: T) -> Result<usize,usize> {
    if a[0] == x {
        return Ok(0);
    }

    let mut range = 1;
    while range < a.len() && a[range] <= x {
        range *= 2;
    }

    let (mut l, mut r) = (range/2, range.min(a.len()));
    while l <= r {
        // This has the same result as (l+r)/2, but it's probably the same or faster.
        let mid = (l+r) >> 1;

        if a[mid] > x {
            r = mid - 1;
        }
        else if a[mid] < x {
            l = mid + 1;
        }
        else {
            return Ok(mid);
        }
    }
    Err(l)
}

/// **Fibonacci Search:** Search for the value 'x' in an array.
///
/// Returns `Err` holding the leftmost term if 'x' not found.
///
/// **Obs.:** Variation of binary search.
///
/// |   Case    | Time complexity | Space complexity |
/// |:----------|:---------------:|:----------------:|
/// | Best:     | Ω(1)            |                  |
/// | Avrg:     | θ(log(n))       |                  |
/// | Worst:    | O(log(n))       | O(1)             |
///
/// # Example
/// ```rust
/// use algos::search;
///
/// let v = [1, 3, 4, 8, 11, 17, 23];
///
/// let find = search::fibonacci(&v, 11);
/// assert_eq!(find, Ok(4));
///
/// let find2 = search::fibonacci(&v, 19);
/// assert_eq!(find2, Err(3));
/// ```
pub fn fibonacci<T: Ord>(a: &[T], x: T) -> Result<usize,usize> {
    let (mut fib1, mut fib2) = (0, 1);
    let mut fibn = fib1 + fib2;

    // We are recalculating numbers, we can do better using dynamic programming.
    // Stores the smallest Fibonacci Number greater than or equal to a.len().
    while fibn < a.len() {
        fib1 = fib2;
        fib2 = fibn;
        fibn = fib1 + fib2;
    }

    let mut off = 0;
    while fibn > 1 {
        let i = (off+fib1-1).min(a.len());

        if a[i] < x {
            fibn = fib2;
            fib2 = fib1;
            fib1 = fibn - fib2;
            off = i;
        }
        else if a[i] > x {
            fibn = fib1;
            fib2 -= fib1;
            fib1 = fibn - fib2;
        }
        else {
            return Ok(i)
        }
    }

    if fib2 == 1 && a[off+1] == x {
        return Ok(off+1)
    }

    Err(off)
}


#[cfg(test)]
pub mod test {
    use search::*;

    #[test]
    pub fn linear_test() {
        let v = [1, 3, 4, 8, 11, 17, 23];

        let find = linear(&v, &11);
        assert_eq!(find, Ok(4));

        let find2 = linear(&v, &19);
        assert_eq!(find2, Err(6));
    }
    #[test]
    pub fn binary_test() {
        let v = [1, 3, 4, 8, 11, 17, 23];

        let find = binary(&v, 11);
        assert_eq!(find, Ok(4));

        let find2 = binary(&v, 19);
        assert_eq!(find2, Err(6));
    }
    #[test]
    pub fn exponential_test() {
        let v = [1, 3, 4, 8, 11, 17, 23];

        let find = exponential(&v, 11);
        assert_eq!(find, Ok(4));

        let find2 = exponential(&v, 19);
        assert_eq!(find2, Err(6));
    }
    #[test]
    pub fn fibonacci_test() {
        let v = [1, 3, 4, 8, 11, 17, 23];

        let find = fibonacci(&v, 11);
        assert_eq!(find, Ok(4));

        let find2 = fibonacci(&v, 19);
        assert_eq!(find2, Err(3));
    }

}
