/**************************************************************************************************
* Copyright 2018 GrayJack
* All rights reserved.
*
* This Source Code Form is subject to the terms of the BSD 3-Clause License.
**************************************************************************************************/

//! A module for using pattern matching algorithms.
//!

/// Brute Force: Search for the pattern in the `find` parameter in a slice.
/// it returns `Ok` the start where the first character of `find` was found
/// or `Err` if not find.
///
/// |:----------|:---------------:|:----------------:|
/// |           | Time Complexity | Space Complexity |
/// |:----------|:---------------:|:----------------:|
/// | Best:     | Ω(m*(n-m+1))    |                  |
/// | Avrg:     | θ(m*(n-m+1))    |                  |
/// | Worst:    | O(m*(n-m+1))    | O(1)             |
///
/// #Examples
/// ```rust
/// use algos::pattern;
///
/// let p = "ATCGGATTTCAGAAGCT".as_bytes();
///
/// let find = pattern::bruteforce(&p, &"TTT".as_bytes());
/// assert_eq!(find, Ok(6));
/// ```
pub fn bruteforce(pattern: &[u8], find: &[u8]) -> Result<usize,usize> {
    let (size_patt, size_find) = (pattern.len()-1, find.len()-1);
    let mut cnt = 0; // counter
    for i in 0..=size_patt-size_find {
        for j in 0..size_find {
            if pattern[i+j] != find[j] {
                break;
            }
            else {
                cnt += 1;
            }
        }
    }
    if cnt != 0 {
        return Ok(cnt);
    }
    Err(cnt)
}

/// Karp-Rabin: Search for the pattern in the `find` parameter in a slice.
/// it returns `Ok` the start where the first character of `find` was found
/// or `Err` if not find.
///
/// |:----------|:---------------:|:----------------:|
/// |           | Time complexity | Space complexity |
/// |:----------|:---------------:|:----------------:|
/// | Best:     | Ω(n-m)          |                  |
/// | Avrg:     | θ(n-m)          |                  |
/// | Worst:    | O(m*(n-m+1))    | O(1)             |
///
/// #Examples
/// ```rust
/// use algos::pattern;
///
/// let p = "ATCGGATTTCAGAAGCT".as_bytes();
///
/// let find = pattern::karp_rabin(&p, &"TTT".as_bytes());
/// assert_eq!(find, Ok(6));
/// ```
pub fn karp_rabin(pattern: &[u8], find: &[u8]) -> Result<usize,usize> {
    let (size_patt, size_find) = (pattern.len()-1, find.len()-1);

    // Preprocessing
    // TODO: There is a way to do the preprocessing using dynamic programming, making the
    // preprocessing time linear, making the worst case O(n-m+1)
    // Using closure cause rust let us use it FUNCTIONAL PROGRAMMING HELL YEAH
    let rehash = |a, b, hash, base| (((hash - a*base) << 1) + b);

    // 2^(m-1)
    let base = {
        let mut x = 1;
        for _ in 1..size_find { x = x<<1 }
        x
    };
    // Calculate the hashes
    let (mut hash_patt, hash_find) = {
        let (mut x, mut y) = (0, 0);
        for i in 0..size_find {
            y = (y << 1) + find[i];
            x = (x << 1) + pattern[i];
        }
        (x, y)
    };

    // Searching
    let (mut i, mut j) = (0, 0);
    while i <= size_patt-size_find {
        if hash_patt == hash_find {
            // Check byte by byte
            while j < size_find {
                if pattern[i+j] != find[j] {
                    break;
                }
                j += 1;
            }

            if j == size_find {
                return Ok(i);
            }
        }

        hash_patt = rehash(pattern[i], pattern[i+size_find], hash_patt, base);
        i += 1;
    }
    Err(i)
}


#[cfg(test)]
pub mod test {
    use pattern::*;

    #[test]
    pub fn test_bruteforce() {
        let p = "ATCGGATTTCAGAAGCT".as_bytes();

        let find = bruteforce(&p, &"TTT".as_bytes());
        assert_eq!(find, Ok(6));
    }

    #[test]
    pub fn test_karp_rabin() {
        let p = "ATCGGATTTCAGAAGCT".as_bytes();

        let find = karp_rabin(&p, &"TTT".as_bytes());
        assert_eq!(find, Ok(6));
    }
}
