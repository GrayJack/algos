/**************************************************************************************************
* Copyright 2018 GrayJack
* All rights reserved.
*
* This Source Code Form is subject to the terms of the BSD 3-Clause License.
**************************************************************************************************/
// TODO: Create basic methods (crescent sort)
// TODO: Create methods to [sort]_by -> Look std docs
// TODO: Create methods [sort]_by_key -> Look std docs

//! A module for using sorting algorithms.
//!
//! It contains all major sorting algorithms.

use std::cmp::*;
use rand::prelude::{Rng, thread_rng};

/// **Selection Sort:** Sort `v` slice according to the way you define the `cmp` parameter.
///
/// This sort is stable.
///
/// |   Case    | Time complexity | Space complexity |
/// |:----------|:---------------:|:----------------:|
/// | Best:     | Ω(n²)           |                  |
/// | Avrg:     | θ(n²)           |                  |
/// | Worst:    | O(n²)           | O(1)             |
///
/// # Example
/// ```rust
/// use algos::sort;
///
/// let mut v = [9, 3, 5, 7, 8, 7];
/// // Crescent sorting
/// sort::selection(&mut v, &|v,b| v<b);
/// ```
pub fn selection<T: Ord, C: Fn(&T, &T) -> bool>(v: &mut [T], cmp: &C) {
    for i in 0..=v.len() {
        let mut i_min = i;
        for j in i+1..v.len() {
            if cmp(&v[j],&v[i_min]) {
                i_min = j;
            }
        }
        if i_min!=i {
            v.swap(i_min, i);
        }
    }
}

/// **Bubble Sort:** Sort `v` slice according to the way you define the `cmp` parameter.
///
/// This sort is stable.
///
/// |   Case    | Time complexity | Space complexity |
/// |:----------|:---------------:|:----------------:|
/// | Best:     | Ω(n)            |                  |
/// | Avrg:     | θ(n²)           |                  |
/// | Worst:    | O(n²)           | O(1)             |
///
/// # Example
/// ```rust
/// use algos::sort;
///
/// let mut v = [9, 3, 5, 7, 8, 7];
/// // Crescent sorting
/// sort::bubble(&mut v, &|v,b| v<b);
/// ```
pub fn bubble<T: Ord, C: Fn(&T, &T) -> bool>(v: &mut [T], cmp: &C) {
    for i in (0..v.len()).rev() {
        for j in 0..i {
            if cmp(&v[j+1],&v[j]) {
                v.swap(j,j+1);
            }
        }
    }
}

/// **Cocktail Sort:** Sort `v` slice according to the way you define the `cmp` parameter.
/// It's a variation of Bubble Sort.
///
/// This sort is stable.
///
/// |   Case    | Time complexity | Space complexity |
/// |:----------|:---------------:|:----------------:|
/// | Best:     | Ω(n)            |                  |
/// | Avrg:     | θ(n²)           |                  |
/// | Worst:    | O(n²)           | O(1)             |
///
/// # Example
/// ```rust
/// use algos::sort;
///
/// let mut v = [9, 3, 5, 7, 8, 7];
/// // Crescent sorting
/// sort::cocktail(&mut v, &|v,b| v<b);
/// ```
pub fn cocktail<T: Ord, C: Fn(&T, &T) -> bool>(v: &mut [T], cmp: &C) {
    let mut changed: bool = true;
    let mut start = 0;
    let mut end = v.len()-1;
    while changed {
        changed = false;
        for i in start..end {
            if cmp(&v[i+1],&v[i]) {
                v.swap(i, i+1);
                changed = true;
            }
        }
        end -= 1;

        if !changed {
            break;
        }

        changed = true;
        for i in (start..end-1).rev() {
            if cmp(&v[i+1],&v[i]) {
                v.swap(i, i+1);
                changed = true;
            }
        }
        start += 1;
    }
}

/// **Insection Sort:** Sort `v` slice according to the way you define the `cmp` parameter.
///
/// This sort is stable.
///
/// |   Case    | Time complexity | Space complexity |
/// |:----------|:---------------:|:----------------:|
/// | Best:     | Ω(n)            |                  |
/// | Avrg:     | θ(n²)           |                  |
/// | Worst:    | O(n²)           | O(1)             |
///
/// # Example
/// ```rust
/// use algos::sort;
///
/// let mut v = [9, 3, 5, 7, 8, 7];
/// // Crescent sorting
/// sort::insection(&mut v, &|v,b| v<b);
/// ```
pub fn insection<T: Ord, C: Fn(&T, &T) -> bool>(v: &mut [T], cmp: &C) {
    for i in 1..v.len() {
        for j in (0..i).rev() {
            if cmp(&v[j+1],&v[j]) {
                v.swap(j, j+1);
            }
        }
    }
}

/// **Merge Sort:** Sort `v` slice according to the way you define the `cmp` parameter.
///
/// This sort is stable.
///
/// |   Case    | Time complexity | Space complexity |
/// |:----------|:---------------:|:----------------:|
/// | Best:     | Ω(nlog(n))      |                  |
/// | Avrg:     | θ(nlog(n))      |                  |
/// | Worst:    | O(nlog(n))      | O(n)             |
///
/// # Example
/// ```rust
/// use algos::sort;
///
/// let mut v = [9, 3, 5, 7, 8, 7];
/// // Crescent sorting
/// sort::merge(&mut v, &|v,b| v<b);
/// ```
pub fn merge<T: Copy + Ord, C: Fn(&T, &T) -> bool>(v: &mut [T], cmp: &C) {
    let (start, mid, end) = (0, v.len()/2, v.len());
    if end<=1 {
        return;
    }
    merge(&mut v[start..mid], cmp);
    merge(&mut v[mid..end], cmp);
    // Copy array "v" to auxiliar array "o"
    let mut o: Vec<T> = v.to_vec();
    combine(&v[start..mid], &v[mid..end], &mut o[..], cmp);
    // Copy itens of "o" into "v"
    v.copy_from_slice(&o);
}

/// Combines `l` and `r` arrays into `o`
fn combine<T: Copy + Ord, C: Fn(&T, &T) -> bool>(l: &[T], r: &[T], o: &mut [T], cmp: &C) {
    assert_eq!(r.len()+l.len(), o.len());
    let (mut i, mut j, mut k) = (0, 0, 0);
    while i<l.len() && j<r.len() {
        if cmp(&l[i],&r[j]) {
            o[k] = l[i];
            k += 1;
            i += 1;
        }
        else {
            o[k] = r[j];
            k += 1;
            j += 1;
        }
    }
    if i<l.len() {
        o[k..].copy_from_slice(&l[i..]);
    }
    if j<r.len() {
        o[k..].copy_from_slice(&r[j..]);
    }
}


/// **Quick Sort:** Sort `v` slice according to the way you define the `cmp` parameter.
///
/// This sort is unstable.
///
/// |   Case    | Time complexity | Space complexity |
/// |:----------|:---------------:|:----------------:|
/// | Best:     | Ω(nlog(n))      |                  |
/// | Avrg:     | θ(nlog(n))      |                  |
/// | Worst:    | O(n²)           | O(log(n))        |
///
/// # Example
/// ```rust
/// use algos::sort;
///
/// let mut v = [9, 3, 5, 7, 8, 7];
/// // Crescent sorting
/// sort::quick(&mut v, &|v,b| v<b);
/// ```
pub fn quick<T: Copy+Ord, C: Fn(&T, &T) -> bool>(v: &mut [T], cmp: &C) {
    let (start, end) = (0, v.len());
    if end<=1 {
        return;
    }
    let mid = partition(v, cmp);
    quick(&mut v[start..mid-1], cmp);
    quick(&mut v[mid..end], cmp);
}

/// Establish where is the middle of `v` and returns it.
fn partition<T: Copy+Ord, C: Fn(&T, &T) -> bool>(v: &mut [T], cmp: &C) -> usize {
    let (start, end) = (0, v.len()-1);
    // We randomize the choice of the pivot so we have less probability to have Worst case.
    // Then we swap the random element to the end of the array.
    let rand = thread_rng().gen_range(start, end);
    let pivot = v[rand];
    v.swap(rand, end);

    let mut i = start;
    for j in start..end {
        if cmp(&v[j],&pivot) {
            v.swap(i, j);
            i += 1;
        }
    }
    v.swap(i, end);
    i+1
}

/// **Heap Sort:** Sort `v` slice according to the way you define the `cmp` parameter.
///
/// This sort is unstable.
///
/// |   Case    | Time complexity | Space complexity |
/// |:----------|:---------------:|:----------------:|
/// | Best:     | Ω(nlog(n))      |                  |
/// | Avrg:     | θ(nlog(n))      |                  |
/// | Worst:    | O(nlog(n))      | O(1)             |
///
/// # Example
/// ```rust
/// use algos::sort;
///
/// let mut v = [9, 3, 5, 7, 8, 7];
/// // Crescent sorting
/// sort::heap(&mut v, &|v,b| v<b);
/// ```
pub fn heap<T: Copy+Ord, C: Fn(&T, &T) -> bool>(v: &mut [T], cmp: &C) {
    let (start, end) = (0, v.len());
    for i in (start..end/2).rev() {
        heapify(&mut v[..], cmp, i);
    }
    for i in (0..end).rev() {
        v.swap(0, i);
        heapify(&mut v[..i], cmp, 0);
    }
}

/// Creates a heap with `node` which is an index in `v`.
fn heapify<T: Copy+Ord, C: Fn(&T, &T) -> bool>(v: &mut [T], cmp: &C, node: usize) {
    let end = v.len();
    let mut root = node;
    let (left_child, right_child) = (2*node, 2*node+1);
    if left_child < end && cmp(&v[root], &v[left_child]) {
        root = left_child;
    }
    if right_child < end && cmp(&v[root], &v[right_child]) {
        root = right_child;
    }
    if root != node {
        v.swap(node, root);
        heapify(v, cmp, root);
    }
}


#[cfg(test)]
pub mod test {
    use sort::*;

    #[test]
    pub fn selection_test() {
        let p = [3, 5, 7, 7, 8, 9, 12, 15, 23, 30, 99];
        let mut v = [9, 3, 5, 7, 8, 7, 99, 30, 23, 15, 12];

        selection(&mut v, &|a,b| a<b);
        assert_eq!(v, p);
    }
    #[test]
    pub fn bubble_test() {
        let p = [3, 5, 7, 7, 8, 9, 12, 15, 23, 30, 99];
        let mut v = [9, 3, 5, 7, 8, 7, 99, 30, 23, 15, 12];

        bubble(&mut v, &|a,b| a<b);
        assert_eq!(v, p);
    }
    #[test]
    pub fn cocktail_test() {
        let p = [3, 5, 7, 7, 8, 9, 12, 15, 23, 30, 99];
        let mut v = [9, 3, 5, 7, 8, 7, 99, 30, 23, 15, 12];

        cocktail(&mut v, &|a,b| a<b);
        assert_eq!(v, p);
    }
    #[test]
    pub fn insection_test() {
        let p = [3, 5, 7, 7, 8, 9, 12, 15, 23, 30, 99];
        let mut v = [9, 3, 5, 7, 8, 7, 99, 30, 23, 15, 12];

        insection(&mut v, &|a,b| a<b);
        assert_eq!(v, p);
    }
    #[test]
    pub fn merge_test() {
        let p = [3, 5, 7, 7, 8, 9, 12, 15, 23, 30, 99];
        let mut v = [9, 3, 5, 7, 8, 7, 99, 30, 23, 15, 12];

        merge(&mut v, &|a,b| a<b);
        assert_eq!(v, p);
    }
    #[test]
    pub fn quick_test() {
        let p = [3, 5, 7, 7, 8, 9, 12, 15, 23, 30, 99];
        let mut v = [9, 3, 5, 7, 8, 7, 99, 30, 23, 15, 12];

        quick(&mut v, &|a,b| a<b);
        assert_eq!(v, p);
    }
    #[test]
    pub fn heap_test() {
        let p = [3, 5, 7, 7, 8, 9, 12, 15, 23, 30, 99];
        let mut v = [9, 3, 5, 7, 8, 7, 99, 30, 23, 15, 12];

        heap(&mut v, &|a,b| a<b);
        assert_eq!(v, p);
    }
}
