# **Algos**

[![Crates.io](https://img.shields.io/crates/v/algos.svg)](https://crates.io/crates/algos)
[![Documentation](https://docs.rs/algos/badge.svg)](https://docs.rs/algos)
[![Build Status](https://github.com/GrayJack/algos/workflows/Build/badge.svg)](https://github.com/GrayJack/algos/actions)
[![dependency status](https://deps.rs/repo/github/GrayJack/algos/status.svg)](https://deps.rs/repo/github/GrayJack/algos)
[![GitHub license](https://img.shields.io/github/license/GrayJack/algos.svg)](https://github.com/GrayJack/algos/blob/master/LICENSE)

A Rust library with a collection of algorithms. Mostly intended as learning exercises for Rust.

Only sort, search and pattern matching algorithms for now.
It is planned to add graph algorithms as well.

## **Usage**

Add this to your `Cargo.toml`:

```toml
[dependencies]
algos = "0.3"
```

and this to your crate root if on 2015 edition:

```rust
extern crate algos;
```

### Sorts Algorithms
Add this to your crate root:

```rust
use algos::sort;
```

and create an array and use like this:

```rust
fn fn main() {
    let mut v = [2, 3, 1, 9, 8, 4];
    // Crescent sorting
    sort::heap(&mut v, &|a,b| a<b);
    // For decreasing sorting, change the signal in &|a,b| a>b.
}
```

It can also work in an array of Strings, sorting by the length of the string:

```rust
fn main() {
    let mut v = ["bc", "a", "def", "klmno", "ghij", "pqrstu"];
    // Crescent sorting
    sort::merge(&mut v, &|a,b| a.len()<b.len())
}
```

### Search Algorithms
Add this to your crate root:

```rust
use algos::search;
```

and create an array and use like this:

```rust
fn fn main() {
    // Remember that your array must be crescent sorted.
    let mut v = [1, 2, 3, 4, 5, 7, 9];

    let find = search::binary(&v, &5);
}
```

### Pattern Matching algorithms
Add this to your crate root:

```rust
use algos::pattern;
```

and use like this:

```rust
fn fn main() {
    let p = "ATCGGATTTCAGAAGCT".as_bytes();
    let find = karp_rabin(&p, &"TTT".as_bytes()); // Type Return<usize, usize>
}
```

## **Implemented**
### Sorts
- [X] Selection Sort
- [X] Bubble Sort
- [X] Cocktail Sort
- [X] Insertion Sort
- [X] Merge Sort
- [X] Quick Sort
- [X] Heap Sort

### Searches
- [X] Linear Search
- [X] Binary Search
- [X] Exponential Search
- [X] Fibonacci Search

### String Matching
- [X] Bruteforce
- [X] Karp-Rabin
- [ ] Boyer-Moore
- [X] Horspool
- [X] Quick
- [ ] Two-Way
