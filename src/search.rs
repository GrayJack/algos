//! A module for using searching algorithms.
//!
//! The array **must** be crescent ordered.

/// **Linear Search:** Search for the value `x` in an array.
///
/// If the value is found then `Ok` is returned, containing the index of the matching
/// element; if the value is not found then `Err` is returned, containing the index where
/// a matching element could be inserted while maintaining sorted order.
///
/// Returns `Err` holding the last iterator if `x` not found and `v[i] > x`.
///
///
/// |   Case    | Time complexity | Space complexity |
/// |:----------|:---------------:|:----------------:|
/// | Best:     | Ω(1)            |                  |
/// | Avrg:     | Θ(n)            |                  |
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
pub fn linear<T: PartialOrd>(v: &[T], x: &T) -> Result<usize, usize> {
    for (i, e) in v.iter().enumerate() {
        if e == x {
            return Ok(i);
        } else if e > x {
            return Err(i);
        }
    }
    Err(0)
}

/// **Binary Search:** Search for the value `x` in an array.
///
/// If the value is found then `Ok` is returned, containing the index of the matching
/// element; if the value is not found then `Err` is returned, containing the index where
/// a matching element could be inserted while maintaining sorted order.
///
/// Returns `Err` holding the leftmost term if `x` not found.
///
///
/// |   Case    | Time complexity | Space complexity |
/// |:----------|:---------------:|:----------------:|
/// | Best:     | Ω(1)            |                  |
/// | Avrg:     | Θ(log(n))       |                  |
/// | Worst:    | O(log(n))       | O(1)             |
///
/// # Example
/// ```rust
/// use algos::search;
///
/// let v = [1, 3, 4, 8, 11, 17, 23];
///
/// let find = search::binary(&v, &11);
/// assert_eq!(find, Ok(4));
///
/// let find2 = search::binary(&v, &19);
/// assert_eq!(find2, Err(6));
/// ```
pub fn binary<T: PartialOrd>(v: &[T], x: &T) -> Result<usize, usize> {
    let (mut l, mut r) = (0, v.len());
    // Looks like I'm unable to make v recursive implementation, so I made interative.
    while l <= r {
        // This has the same result as (l+r)/2, but it's probably the same or faster.
        let mid = (l + r) >> 1;

        if v[mid] > *x {
            r = mid - 1;
        } else if v[mid] < *x {
            l = mid + 1;
        } else {
            return Ok(mid);
        }
    }
    Err(l)
}

/// **Exponential Search:** Search for the value `x` in an array.
///
/// If the value is found then `Ok` is returned, containing the index of the matching
/// element; if the value is not found then `Err` is returned, containing the index where
/// a matching element could be inserted while maintaining sorted order.
///
/// Returns `Err` holding the leftmost term if `x` not found.
///
/// **Obs.:** Variation of binary search.
///
/// |   Case    | Time complexity | Space complexity |
/// |:----------|:---------------:|:----------------:|
/// | Best:     | Ω(1)            |                  |
/// | Avrg:     | Θ(log(n))       |                  |
/// | Worst:    | O(log(n))       | O(1)             |
///
/// # Example
/// ```rust
/// use algos::search;
///
/// let v = [1, 3, 4, 8, 11, 17, 23];
///
/// let find = search::exponential(&v, &11);
/// assert_eq!(find, Ok(4));
///
/// let find2 = search::exponential(&v, &19);
/// assert_eq!(find2, Err(6));
/// ```
pub fn exponential<T: PartialOrd>(v: &[T], x: &T) -> Result<usize, usize> {
    if v[0] == *x {
        return Ok(0);
    }

    let mut range = 1;
    while range < v.len() && v[range] <= *x {
        range *= 2;
    }

    let (mut l, mut r) = (range / 2, range.min(v.len()));
    while l <= r {
        // This has the same result as (l+r)/2, but it's probably the same or faster.
        let mid = (l + r) >> 1;

        if v[mid] > *x {
            r = mid - 1;
        } else if v[mid] < *x {
            l = mid + 1;
        } else {
            return Ok(mid);
        }
    }
    Err(l)
}

/// **Fibonacci Search:** Search for the value `x` in an array.
///
/// If the value is found then `Ok` is returned, containing the index of the matching
/// element; if the value is not found then `Err` is returned, containing the index where
/// a matching element could be inserted while maintaining sorted order.
///
///
/// **Obs.:** Variation of binary search.
///
/// |   Case    | Time complexity | Space complexity |
/// |:----------|:---------------:|:----------------:|
/// | Best:     | Ω(1)            |                  |
/// | Avrg:     | Θ(log(n))       |                  |
/// | Worst:    | O(log(n))       | O(1)             |
///
/// # Example
/// ```rust
/// use algos::search;
///
/// let v = [1, 3, 4, 8, 11, 17, 23];
///
/// let find = search::fibonacci(&v, &11);
/// assert_eq!(find, Ok(4));
///
/// let find2 = search::fibonacci(&v, &19);
/// assert_eq!(find2, Err(3));
/// ```
pub fn fibonacci<T: PartialOrd>(v: &[T], x: &T) -> Result<usize, usize> {
    let (mut fib1, mut fib2) = (0, 1);
    let mut fibn = fib1 + fib2;

    // We are recalculating numbers, we can do better using dynamic programming.
    // Stores the smallest Fibonacci Number greater than or equal to v.len().
    while fibn < v.len() {
        fib1 = fib2;
        fib2 = fibn;
        fibn = fib1 + fib2;
    }

    let mut off = 0;
    while fibn > 1 {
        let i = (off + fib1 - 1).min(v.len());

        if v[i] < *x {
            fibn = fib2;
            fib2 = fib1;
            fib1 = fibn - fib2;
            off = i;
        } else if v[i] > *x {
            fibn = fib1;
            fib2 -= fib1;
            fib1 = fibn - fib2;
        } else {
            return Ok(i);
        }
    }

    if fib2 == 1 && v[off + 1] == *x {
        return Ok(off + 1);
    }

    Err(off)
}


#[cfg(test)]
pub mod test {
    use super::*;

    #[test]
    pub fn linear_test() {
        let v = [1, 3, 4, 8, 11, 17, 23];

        let ok1 = linear(&v, &1);
        let ok2 = linear(&v, &11);
        assert_eq!(ok1, Ok(0));
        assert_eq!(ok2, Ok(4));

        let err1 = linear(&v, &19);
        let err2 = linear(&v, &13);
        assert_eq!(err1, Err(6));
        assert_eq!(err2, Err(5));
    }
    #[test]
    pub fn binary_test() {
        let v = [1, 3, 4, 8, 11, 17, 23];

        let ok1 = binary(&v, &1);
        let ok2 = binary(&v, &11);
        assert_eq!(ok1, Ok(0));
        assert_eq!(ok2, Ok(4));

        let err1 = binary(&v, &19);
        let err2 = binary(&v, &13);
        assert_eq!(err1, Err(6));
        assert_eq!(err2, Err(5));
    }
    #[test]
    pub fn exponential_test() {
        let v = [1, 3, 4, 8, 11, 17, 23];

        let ok1 = exponential(&v, &1);
        let ok2 = exponential(&v, &11);
        assert_eq!(ok1, Ok(0));
        assert_eq!(ok2, Ok(4));

        let err1 = exponential(&v, &19);
        let err2 = exponential(&v, &13);
        assert_eq!(err1, Err(6));
        assert_eq!(err2, Err(5));
    }
    #[test]
    pub fn fibonacci_test() {
        let v = [1, 3, 4, 8, 11, 17, 23];

        let ok1 = fibonacci(&v, &1);
        let ok2 = fibonacci(&v, &11);
        assert_eq!(ok1, Ok(0));
        assert_eq!(ok2, Ok(4));

        let err1 = fibonacci(&v, &19);
        let err2 = fibonacci(&v, &13);
        assert_eq!(err1, Err(3));
        assert_eq!(err2, Err(3));
    }
}
