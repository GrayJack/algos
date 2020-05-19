//! A module for using pattern matching algorithms.

/// **Brute Force:** Search for the pattern in the `find` parameter in a slice.
///
/// It returns `Some` holding the index of the first character of `find` that was found
/// or `None` if not find.
///
/// |   Case    | Time complexity | Space complexity |
/// |:----------|:---------------:|:----------------:|
/// | Best:     | Ω(m*(n-m+1))    |                  |
/// | Avrg:     | Θ(m*(n-m+1))    |                  |
/// | Worst:    | O(m*(n-m+1))    | O(1)             |
///
/// # Example
/// ```rust
/// use algos::pattern;
///
/// let p = b"ATCGGATTTCAGAAGCT";
///
/// let find = pattern::bruteforce(p, b"TTT");
/// assert_eq!(find, Some(6));
/// ```
pub fn bruteforce(pattern: &[u8], find: &[u8]) -> Option<usize> {
    let (size_patt, size_find) = (pattern.len(), find.len());
    for i in 0..=size_patt - size_find {
        if &pattern[i..(i + size_find)] == find {
            return Some(i);
        }
    }

    None
}

/// **Karp-Rabin:** Search for the pattern in the `find` parameter in a slice.
///
/// It returns `Some` holding the index of the first character of `find` that was found
/// or `None` if not find.
///
/// |   Case    | Time complexity | Space complexity |
/// |:----------|:---------------:|:----------------:|
/// | Best:     | Ω(n+m)          |                  |
/// | Avrg:     | Θ(n+m)          |                  |
/// | Worst:    | O(m*(n+m))      | O(1)             |
///
/// # Example
/// ```rust
/// use algos::pattern;
///
/// let p = b"ATCGGATTTCAGAAGCT";
///
/// let find = pattern::karp_rabin(p, b"TTT");
/// assert_eq!(find, Some(6));
/// ```
pub fn karp_rabin(pattern: &[u8], find: &[u8]) -> Option<usize> {
    let (size_patt, size_find) = (pattern.len() - 1, find.len());

    // Preprocessing
    // TODO: There is a way to do the preprocessing using dynamic programming, making the
    // preprocessing time linear, making the worst case O(n+m)
    let rehash = |a, b, hash, base| (((hash - a * base) << 1) + b);

    // 2^(m-1)
    let base: u64 = 1 << (size_find - 1);

    // Calculate the hashes
    let (hash_find, mut hash_patt) = find.iter().take(size_find).zip(pattern.iter()).fold(
        (0_u64, 0_u64),
        |(hash_find, hash_patt), (&find, &patt)| {
            ((hash_find << 1) + u64::from(find), (hash_patt << 1) + u64::from(patt))
        },
    );

    // Searching
    let mut i = 0;
    while i <= size_patt - size_find {
        if hash_patt == hash_find && &pattern[i..(i + size_find)] == find {
            return Some(i);
        }

        hash_patt =
            rehash(u64::from(pattern[i]), u64::from(pattern[i + size_find]), hash_patt, base);
        i += 1;
    }
    // Check again after the loops end.
    if hash_patt == hash_find && &pattern[i..(i + size_find)] == find {
        return Some(i);
    }

    None
}

/// **Boyer-Moore:** Search for the pattern in the `find` parameter in a slice.
///
/// It returns `Some` holding the index of the first character of `find` that was found
/// or `None` if not find.
///
/// |   Case    | Time complexity | Space complexity |
/// |:----------|:---------------:|:----------------:|
/// | Best:     | Ω(n/m)          |                  |
/// | Avrg:     | Θ(n+m)          |                  |
/// | Worst:    | O(nm)           | O(m+δ)           |
///
///
/// **Obs.:** δ is the max size of u8.
///
/// # Example
/// ```rust
/// use algos::pattern;
///
/// let p = b"ATCGGATTTCAGAAGCT";
///
/// let find = pattern::boyer_moore(p, b"TTT");
/// assert_eq!(find, Some(6));
/// ```
pub fn boyer_moore(pattern: &[u8], find: &[u8]) -> Option<usize> {
    let (size_patt, size_find) = (pattern.len() - 1, find.len());
    let mut good_sufix_table = vec![0_usize; size_find];
    let mut bad_char_table = [0_usize; 256];

    // Preprocessing
    preprocess_good_sufix(find, &mut good_sufix_table[..]);
    preprocess_bad_char(find, &mut bad_char_table[..]);

    // Searching
    let mut i = 0;
    while i <= size_patt - size_find {
        let mut j = size_find - 1;
        while find[j] == pattern[j + i] && j > 0 {
            j -= 1;
        }
        if j == 0 {
            if &pattern[i..(i + size_find)] == find {
                return Some(i);
            }
            i += good_sufix_table[0];
        } else {
            i += good_sufix_table[j]
                .max(bad_char_table[pattern[j + i] as usize - size_find + 1 + j]);
        }
    }

    None
}

/// **Horspool:** Search for the pattern in the `find` parameter in a slice.
///
/// It returns `Some` holding the index of the first character of `find` that was found
/// or `None` if not find.
///
/// It is a variation of the Boyer-Moore algorithm.
///
/// |   Case    | Time complexity | Space complexity |
/// |:----------|:---------------:|:----------------:|
/// | Best:     | Ω(n/m)          |                  |
/// | Avrg:     | Θ(n+m)          |                  |
/// | Worst:    | O(nm)           | O(δ)             |
///
///
/// **Obs.:** δ is the max size of u8.
///
/// # Example
/// ```rust
/// use algos::pattern;
///
/// let p = b"ATCGGATTTCAGAAGCT";
///
/// let find = pattern::horspool(p, b"TTT");
/// assert_eq!(find, Some(6));
/// ```
pub fn horspool(pattern: &[u8], find: &[u8]) -> Option<usize> {
    let (size_patt, size_find) = (pattern.len(), find.len());
    let mut bad_char_table = [0_usize; 256];

    // Preprocessing
    preprocess_bad_char(find, &mut bad_char_table[..]);

    // Searching
    let mut i = 0;
    while i <= size_patt - size_find {
        let c = pattern[i + size_find - 1];
        if find[size_find - 1] == c && &pattern[i..(i + size_find)] == find {
            return Some(i);
        }

        i += bad_char_table[c as usize];
    }

    None
}

fn preprocess_good_sufix(find: &[u8], good_sufix_table: &mut [usize]) {
    let size = find.len();

    // Good sufix
    let mut suff = vec![0; size];
    let mut good = size - 1;
    let mut f = 0;
    suff[size - 1] = size;
    for i in (0..suff.len()).rev() {
        if i > good && suff[i + size - 1 + f] < i - good {
            suff[i] = suff[i + size - 1 + f];
        } else {
            good = if (good) < i { i } else { good };
            f = i;
            while good == 0 && find[good] == find[good + size - 1 - f] {
                good -= 1;
            }
            suff[i] = good - f;
        }
    }

    for i in good_sufix_table.iter_mut().take(size) {
        *i = size;
    }
    for i in (0..size).rev() {
        if suff[i] == i + 1 {
            for j in good_sufix_table.iter_mut().take(size - 1) {
                if *j == size {
                    *j = size - i - 1;
                }
            }
        }
    }
    for i in 0..size {
        good_sufix_table[size - 1 - suff[i] as usize] = size - 1 - i;
    }
}

fn preprocess_bad_char(find: &[u8], bad_char_table: &mut [usize]) {
    let size: usize = find.len();

    for i in bad_char_table.iter_mut() {
        *i = size;
    }
    for i in 0..size - 1 {
        bad_char_table[find[i] as usize] = size - i - 1;
    }
}

/// **Quick:** Search for the pattern in the `find` parameter in a slice.
///
/// It returns `Some` holding the index of the first character of `find` that was found
/// or `None` if not find.
///
/// It is a simplification of the Boyer-Moore algorithm.
///
/// |   Case    | Time complexity | Space complexity |
/// |:----------|:---------------:|:----------------:|
/// | Best:     | Ω(n/m)          |                  |
/// | Avrg:     | Θ(n+m)          |                  |
/// | Worst:    | O(nm)           | O(δ)             |
///
///
/// **Obs.:** δ is the max size of u8.
///
/// # Example
/// ```rust
/// use algos::pattern;
///
/// let p = b"ATCGGATTTCAGAAGCT";
///
/// let find = pattern::quick_matching(p, b"TTT");
/// assert_eq!(find, Some(6));
/// ```
pub fn quick_matching(pattern: &[u8], find: &[u8]) -> Option<usize> {
    let (size_patt, size_find) = (pattern.len(), find.len());
    let mut bad_char_table = [0_usize; 256];

    // Preprocessing
    preprocess_quick_bad_char(&find, &mut bad_char_table);

    // Searching
    let mut i = 0;
    while i <= size_patt - size_find {
        if &pattern[i..(i + size_find)] == find {
            return Some(i);
        }

        i += bad_char_table[pattern[i + size_find] as usize];
    }

    None
}

fn preprocess_quick_bad_char(find: &[u8], bad_char_table: &mut [usize]) {
    for i in bad_char_table.iter_mut() {
        *i = find.len() + 1;
    }
    for i in 0..find.len() {
        bad_char_table[find[i] as usize] = find.len() - i;
    }
}


#[cfg(test)]
pub mod test {
    use super::*;

    #[test]
    pub fn bruteforce_cases() {
        let p = b"ATCGGATTTCAGAAGCT";

        let start = bruteforce(p, b"ATC");
        let middle1 = bruteforce(p, b"TTT");
        let middle2 = bruteforce(p, b"AAG");
        let end = bruteforce(p, b"GCT");
        let none = bruteforce(p, b"TTTT");
        assert_eq!(start, Some(0));
        assert_eq!(middle1, Some(6));
        assert_eq!(middle2, Some(12));
        assert_eq!(end, Some(14));
        assert_eq!(none, None);
    }

    #[test]
    pub fn karp_rabin_cases() {
        let p = b"ATCGGATTTCAGAAGCT";

        let start = karp_rabin(p, b"ATC");
        let middle1 = karp_rabin(p, b"TTT");
        let middle2 = karp_rabin(p, b"AAG");
        let end = karp_rabin(p, b"GCT");
        let none = karp_rabin(p, b"TTTT");
        assert_eq!(start, Some(0));
        assert_eq!(middle1, Some(6));
        assert_eq!(middle2, Some(12));
        assert_eq!(end, Some(14));
        assert_eq!(none, None);
    }

    #[test]
    #[ignore]
    pub fn boyer_moore_cases() {
        let p = b"ATCGGATTTCAGAAGCT";

        let start = boyer_moore(p, b"ATC");
        let middle1 = boyer_moore(p, b"TTT");
        let middle2 = boyer_moore(p, b"AAG");
        let end = boyer_moore(p, b"GCT");
        let none = boyer_moore(p, b"TTTT");
        assert_eq!(start, Some(0));
        assert_eq!(middle1, Some(6));
        assert_eq!(middle2, Some(12));
        assert_eq!(end, Some(14));
        assert_eq!(none, None);
    }

    #[test]
    pub fn horspool_cases() {
        let p = b"ATCGGATTTCAGAAGCT";

        let start = horspool(p, b"ATC");
        let middle1 = horspool(p, b"TTT");
        let middle2 = horspool(p, b"AAG");
        let end = horspool(p, b"GCT");
        let none = horspool(p, b"TTTT");
        assert_eq!(start, Some(0));
        assert_eq!(middle1, Some(6));
        assert_eq!(middle2, Some(12));
        assert_eq!(end, Some(14));
        assert_eq!(none, None);
    }

    #[test]
    pub fn quick_cases() {
        let p = b"ATCGGATTTCAGAAGCT";

        let start = quick_matching(p, b"ATC");
        let middle1 = quick_matching(p, b"TTT");
        let middle2 = quick_matching(p, b"AAG");
        let end = quick_matching(p, b"GCT");
        let none = quick_matching(p, b"TTTT");
        assert_eq!(start, Some(0));
        assert_eq!(middle1, Some(6));
        assert_eq!(middle2, Some(12));
        assert_eq!(end, Some(14));
        assert_eq!(none, None);
    }
}
