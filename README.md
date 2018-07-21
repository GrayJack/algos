# **Algo**

A rust library with a collection of algorithms.

Only sort algorithms for now.
It is planned to add search and graph algorithms as well.

## **Usage**

Add this to your `Cargo.toml`:

```toml
[dependencies]
algo = "0.1"
```

and this to your crate root:

```rust
extern crate algo;
```

### Sorts algorithms
Add this to your crate root:

```rust
use algo::sort;
```

and create a array and use like this:

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

## **Implemented**
### Sorts
- [x] Selection Sort
- [x] Bubble Sort
- [x] Cocktail Sort
- [x] Insertion Sort
- [x] Merge Sort
- [x] Quick Sort
- [x] Heap Sort
