/**************************************************************************************************
* Copyright 2018 GrayJack
* All rights reserved.
*
* This Source Code Form is subject to the terms of the BSD 3-Clause License.
**************************************************************************************************/

//! A module for using pattern matching algorithms.
//!

/// **Brute Force:** Search for the pattern in the `find` parameter in a slice.
///
/// It returns `Ok` holding the index of the first character of `find` that was found
/// or `Err` holding the last index it searched if not find.
///
/// |   Case    | Time complexity | Space complexity |
/// |:----------|:---------------:|:----------------:|
/// | Best:     | Ω(m*(n-m+1))    |                  |
/// | Avrg:     | θ(m*(n-m+1))    |                  |
/// | Worst:    | O(m*(n-m+1))    | O(1)             |
///
/// # Example
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
        let mut j = 0;
        while j < size_find && find[j] == pattern[i+j] {
            if pattern[i+j] != find[j] {
                break;
            }
            j += 1;
        }
        if j == size_find {
            return Ok(i);
        }
        cnt += 1;
    }
    Err(cnt)
}

/// **Karp-Rabin:** Search for the pattern in the `find` parameter in a slice.
///
/// It returns `Ok` holding the index of the first character of `find` that was found
/// or `Err` holding the last index it searched if not find.
///
/// |   Case    | Time complexity | Space complexity |
/// |:----------|:---------------:|:----------------:|
/// | Best:     | Ω(n+m)          |                  |
/// | Avrg:     | θ(n+m)          |                  |
/// | Worst:    | O(m*(n+m))      | O(1)             |
///
/// # Example
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
    // preprocessing time linear, making the worst case O(n+m)
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
            // Check one by one
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

/// **Boyer-Moore:** Search for the pattern in the `find` parameter in a slice.
///
/// It returns `Ok` holding the index of the first character of `find` that was found
/// or `Err` holding the last index it searched if not find.
///
/// |   Case    | Time complexity | Space complexity |
/// |:----------|:---------------:|:----------------:|
/// | Best:     | Ω(n/m)          |                  |
/// | Avrg:     | θ(n+m)          |                  |
/// | Worst:    | O(nm)           | O(m+δ)           |
///
///
/// **Obs.:** δ is the max size of u8.
///
/// # Example
/// ```rust
/// use algos::pattern;
///
/// let p = "ATCGGATTTCAGAAGCT".as_bytes();
///
/// let find = pattern::boyer_moore(&p, &"TTT".as_bytes());
/// assert_eq!(find, Ok(6));
/// ```
pub fn boyer_moore(pattern: &[u8], find: &[u8]) -> Result<usize,usize> {
    let (size_patt, size_find) = (pattern.len()-1, find.len());
    let mut good_sufix_table = vec![0usize; size_find];
    let mut bad_char_table   = vec![0usize; 256];

    // Preprocessing
    // Good sufix
    preprocess_good_sufix(find, &mut good_sufix_table[..]);
    preprocess_bad_char(find, &mut bad_char_table[..]);

    // Searching
    let (mut i, mut j) = (size_find-1, 0);
    while j <= size_patt - size_find {
        while find[i] == pattern[i + j] && i > 0 {
            i -= 1;
        }
        if i == 0 {
            let mut k = 0;
            while k < size_find && find[k] == pattern[j+k] {
                k += 1;
            }
            if k == size_find {
                return Ok(j);
            }
            else {
                j += good_sufix_table[0];
            }
        }
        else {
            j += good_sufix_table[i].max(bad_char_table[pattern[i + j] as usize - size_find + 1 + i]);
        }
    }

    Err(j)
}

/// **Horspool:** Search for the pattern in the `find` parameter in a slice.
///
/// It returns `Ok` holding the index of the first character of `find` that was found
/// or `Err` holding the last index it searched if not find.
///
/// It is a variation of the Boyer-Moore algorithm.
///
/// |   Case    | Time complexity | Space complexity |
/// |:----------|:---------------:|:----------------:|
/// | Best:     | Ω(n/m)          |                  |
/// | Avrg:     | θ(n+m)          |                  |
/// | Worst:    | O(nm)           | O(δ)             |
///
///
/// **Obs.:** δ is the max size of u8.
///
/// # Example
/// ```rust
/// use algos::pattern;
///
/// let p = "ATCGGATTTCAGAAGCT".as_bytes();
///
/// let find = pattern::horspool(&p, &"TTT".as_bytes());
/// assert_eq!(find, Ok(6));
/// ```
pub fn horspool(pattern: &[u8], find: &[u8]) -> Result<usize,usize> {
    let (size_patt, size_find) = (pattern.len()-1, find.len()-1);
    let mut bad_char_table = vec![0usize; 256];

    // Preprocessing
    preprocess_bad_char(find, &mut bad_char_table[..]);

    // Searching
    let (mut i, mut j) = (0, 0);
    while i <= size_patt - size_find {
        let c = pattern[i + size_find - 1];
        if find[size_find - 1] == c {
            // Check one by one
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

        i += bad_char_table[c as usize];
    }

    Err(i)
}

fn preprocess_good_sufix(find: &[u8], good_sufix_table: &mut [usize]) {
    let size = find.len() - 1;
    // Good sufix
    let mut suff = vec![0; size];
    let mut good = size-1;
    let mut f    = 0;
    suff[size-1] = size;
    for i in (0..suff.len()).rev() {
        if i > good && suff[i + size-1 + f] < i - good {
            suff[i] = suff[i + size-1 + f];
        }
        else {
            good = if (good) < i { i } else { good };
            f = i;
            while good == 0 && find[good] == find[good + size-1 -f] {
                good -= 1;
            }
            suff[i] = good-f;
        }
    }

    for i in 0..size {
        good_sufix_table[i] = size;
    }
    for i in (0..=size-1).rev() {
        if suff[i] == i+1 {
            for j in 0..size-1 {
                if good_sufix_table[j] == size {
                    good_sufix_table[j] = size - i - 1;
                }
            }
        }
    }
    for i in 0..=size-1 {
        good_sufix_table[size - 1 - suff[i] as usize] = size - 1 - i;
    }
}

fn preprocess_bad_char(find: &[u8], bad_char_table: &mut [usize]) {
    let size = find.len()-1;

    for i in 0..256 {
        bad_char_table[i] = size;
    }
    for i in 0..size-1 {
        bad_char_table[find[i] as usize] = size - i - 1;
    }
}

/// **Quick:** Search for the pattern in the `find` parameter in a slice.
///
/// It returns `Ok` holding the index of the first character of `find` that was found
/// or `Err` holding the last index it searched if not find.
///
/// It is a simplification of the Boyer-Moore algorithm.
///
/// |   Case    | Time complexity | Space complexity |
/// |:----------|:---------------:|:----------------:|
/// | Best:     | Ω(n/m)          |                  |
/// | Avrg:     | θ(n+m)          |                  |
/// | Worst:    | O(nm)           | O(δ)             |
///
///
/// **Obs.:** δ is the max size of u8.
///
/// # Example
/// ```rust
/// use algos::pattern;
///
/// let p = "ATCGGATTTCAGAAGCT".as_bytes();
///
/// let find = pattern::horspool(&p, &"TTT".as_bytes());
/// assert_eq!(find, Ok(6));
/// ```
pub fn quick_matching(pattern: &[u8], find: &[u8]) -> Result<usize,usize> {
    let (size_patt, size_find) = (pattern.len()-1, find.len()-1);
    let mut bad_char_table = vec![0usize; 256];

    // Preprocessing
    preprocess_quick_bad_char(&find, &mut bad_char_table);

    // Searching
    let mut i = 0;
    while i <= size_patt - size_find {
        // Check one by one
        let mut j = 0;
        while j < size_find {
            if pattern[i+j] != find[j] {
                break;
            }
            j += 1;
        }

        if j == size_find {
            return Ok(i);
        }

        i += bad_char_table[pattern[i + size_find] as usize];
    }

    Err(i)
}

fn preprocess_quick_bad_char(find: &[u8], bad_char_table: &mut [usize]) {
    for i in 0..256 {
        bad_char_table[i] = find.len() + 1;
    }
    for i in 0..find.len() {
        bad_char_table[find[i] as usize] = find.len() - i;
    }
}


#[cfg(test)]
pub mod test {
    use pattern::*;

    #[test]
    pub fn test_bruteforce() {
        let p = "ATCGGATTTCAGAAGCT".as_bytes();

        let find = bruteforce(&p, &"TTT".as_bytes());
        let find2 = bruteforce(&p, &"AAG".as_bytes());
        assert_eq!(find, Ok(6));
        assert_eq!(find2, Ok(12));
    }

    #[test]
    pub fn test_karp_rabin() {
        let p = "ATCGGATTTCAGAAGCT".as_bytes();

        let find = karp_rabin(&p, &"TTT".as_bytes());
        let find2 = karp_rabin(&p, &"AAG".as_bytes());
        assert_eq!(find, Ok(6));
        assert_eq!(find2, Ok(12));
    }

    #[test]
    pub fn test_boyer_moore() {
        let p = "ATCGGATTTCAGAAGCT".as_bytes();

        let find = boyer_moore(&p, &"TTT".as_bytes());
        let find2 = boyer_moore(&p, &"AAG".as_bytes());
        assert_eq!(find, Ok(6));
        assert_eq!(find2, Ok(12));
    }

    #[test]
    pub fn test_horspool() {
        let p = "ATCGGATTTCAGAAGCT".as_bytes();

        let find = horspool(&p, &"TTT".as_bytes());
        let find2 = horspool(&p, &"AAG".as_bytes());
        assert_eq!(find, Ok(6));
        assert_eq!(find2, Ok(12));
    }

    #[test]
    pub fn test_quick() {
        let p = "ATCGGATTTCAGAAGCT".as_bytes();

        let find = quick_matching(&p, &"TTT".as_bytes());
        let find2 = quick_matching(&p, &"AAG".as_bytes());
        assert_eq!(find, Ok(6));
        assert_eq!(find2, Ok(12));
    }
}
