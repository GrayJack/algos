/*******************************************************************************
* Copyright 2017 Eric Shimizu Karbstein
* All rights reserved.
*
* This Source Code Form is subject to the terms of the BSD 3-Clause License.
******************************************************************************/

//! This crate is a collection of algorithms.
//! For now only sorting algorithms were implemented.
//! It is planned to implement searching and graphs algorithms.

extern crate rand;

pub mod sort {
    //! A module for using sorting algorithms.
    //!
    //! It contains all major sorting algorithms.

    use std::cmp::*;
    use rand::prelude::*;

    /// Selection Sort: Sort a slice according to the way you define the cmp parameter.
    ///
    /// |           | Time complexity | Space complexity |
    /// |:----------|:---------------:|:----------------:|
    /// | Best:     | Ω(n^2)          |                  |
    /// | Avrg:     | θ(n^2)          |                  |
    /// | Worst:    | O(n^2)          | O(1)             |
    ///
    /// #Examples
    /// ```rust
    /// use algo::sort;
    ///
    /// let mut v = [9, 3, 5, 7, 8, 7];
    /// // Crescent sorting
    /// sort::selection(&mut v, &|a,b| a<b);
    /// ```
    pub fn selection<T: Ord, C: Fn(&T, &T) -> bool>(a: &mut [T], cmp: &C) {
        for i in 0..=a.len() {
            let mut i_min = i;
            for j in i+1..a.len() {
                if cmp(&a[i_min],&a[j]) {
                    i_min = j;
                }
            }
            if i_min!=i {
                a.swap(i_min, i);
            }
        }
    }

    /// Bubble Sort: Sort a slice according to the way you define the cmp parameter.
    ///
    /// |           | Time complexity | Space complexity |
    /// |:----------|:---------------:|:----------------:|
    /// | Best:     | Ω(n)            |                  |
    /// | Avrg:     | θ(n^2)          |                  |
    /// | Worst:    | O(n^2)          | O(1)             |
    ///
    /// #Examples
    /// ```rust
    /// use algo::sort;
    ///
    /// let mut v = [9, 3, 5, 7, 8, 7];
    /// // Crescent sorting
    /// sort::bubble(&mut v, &|a,b| a<b);
    /// ```
    pub fn bubble<T: Ord, C: Fn(&T, &T) -> bool>(a: &mut [T], cmp: &C) {
        for i in (0..a.len()).rev() {
            for j in 0..i {
                if cmp(&a[j],&a[j+1]) {
                    a.swap(j,j+1);
                }
            }
        }
    }

    /// Cocktail Sort: Sort a slice according to the way you define the cmp parameter.
    /// It's a variation of Bubble Sort.
    ///
    /// |           | Time complexity | Space complexity |
    /// |:----------|:---------------:|:----------------:|
    /// | Best:     | Ω(n)            |                  |
    /// | Avrg:     | θ(n^2)          |                  |
    /// | Worst:    | O(n^2)          | O(1)             |
    ///
    /// #Examples
    /// ```rust
    /// use algo::sort;
    ///
    /// let mut v = [9, 3, 5, 7, 8, 7];
    /// // Crescent sorting
    /// sort::cocktail(&mut v, &|a,b| a<b);
    /// ```
    pub fn cocktail<T: Ord, C: Fn(&T, &T) -> bool>(a: &mut [T], cmp: &C) {
        let mut changed: bool = true;
        let mut start = 0;
        let mut end = a.len()-1;
        while changed {
            changed = false;
            for i in start..end {
                if cmp(&a[i],&a[i+1]) {
                    a.swap(i, i+1);
                    changed = true;
                }
            }
            end -= 1;

            if !changed {
                break;
            }

            changed = true;
            for i in (start..end-1).rev() {
                if cmp(&a[i],&a[i+1]) {
                    a.swap(i, i+1);
                    changed = true;
                }
            }
            start += 1;
        }
    }

    /// Insection Sort: Sort a slice according to the way you define the cmp parameter.
    ///
    /// |           | Time complexity | Space complexity |
    /// |:----------|:---------------:|:----------------:|
    /// | Best:     | Ω(n)            |                  |
    /// | Avrg:     | θ(n^2)          |                  |
    /// | Worst:    | O(n^2)          | O(1)             |
    ///
    /// #Examples
    /// ```rust
    /// use algo::sort;
    ///
    /// let mut v = [9, 3, 5, 7, 8, 7];
    /// // Crescent sorting
    /// sort::insection(&mut v, &|a,b| a<b);
    /// ```
    pub fn insection<T: Ord, C: Fn(&T, &T) -> bool>(a: &mut [T], cmp: &C) {
        for i in 1..a.len() {
            for j in (0..i).rev() {
                if cmp(&a[j],&a[j+1]) {
                    a.swap(j, j+1);
                }
            }
        }
    }

    /// Merge Sort: Sort a slice according to the way you define the cmp parameter.
    ///
    /// |           | Time complexity | Space complexity |
    /// |:----------|:---------------:|:----------------:|
    /// | Best:     | Ω(nlog(n))      |                  |
    /// | Avrg:     | θ(nlog(n))      |                  |
    /// | Worst:    | O(nlog(n))      | O(n)             |
    ///
    /// #Examples
    /// ```rust
    /// use algo::sort;
    ///
    /// let mut v = [9, 3, 5, 7, 8, 7];
    /// // Crescent sorting
    /// sort::merge(&mut v, &|a,b| a<b);
    /// ```
    pub fn merge<T: Copy + Ord, C: Fn(&T, &T) -> bool>(a: &mut [T], cmp: &C) {
        let (start, mid, end) = (0, a.len()/2, a.len());
        if end<=1 {
            return;
        }
        merge(&mut a[start..mid], cmp);
        merge(&mut a[mid..end], cmp);
        // Copy array "a" to auxiliar array "o"
        let mut o: Vec<T> = a.to_vec();
        combine(&a[start..mid], &a[mid..end], &mut o[..], cmp);
        // Copy itens of "o" into "a"
        a.copy_from_slice(&o);
    }
    fn combine<T: Copy + PartialOrd, C: Fn(&T, &T) -> bool>(l: &[T], r: &[T], o: &mut [T], cmp: &C) {
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


    /// Quick Sort: Sort a slice according to the way you define the cmp parameter.
    ///
    /// |           | Time complexity | Space complexity |
    /// |:----------|:---------------:|:----------------:|
    /// | Best:     | Ω(nlog(n))      |                  |
    /// | Avrg:     | θ(nlog(n))      |                  |
    /// | Worst:    | O(n^2)          | O(log(n))        |
    ///
    /// #Examples
    /// ```rust
    /// use algo::sort;
    ///
    /// let mut v = [9, 3, 5, 7, 8, 7];
    /// // Crescent sorting
    /// sort::quick(&mut v, &|a,b| a<b);
    /// ```
    pub fn quick<T: Copy+Ord, C: Fn(&T, &T) -> bool>(a: &mut [T], cmp: &C) {
        let (start, end) = (0, a.len());
        if end<=1 {
            return;
        }
        let mid = partition(a, cmp);
        quick(&mut a[start..mid-1], cmp);
        quick(&mut a[mid..end], cmp);
    }
    fn partition<T: Copy+Ord, C: Fn(&T, &T) -> bool>(a: &mut [T], cmp: &C) -> usize {
        let (start, end) = (0, a.len()-1);
        // We randomize the choice of the pivot so we have less probability to have Worst case.
        // Then we swap the random element to the end of the array.
        let rand = thread_rng().gen_range(start, end);
        let pivot = a[rand];
        a.swap(rand, end);

        let mut i = start;
        for j in start..end {
            if cmp(&a[j],&pivot) {
                a.swap(i, j);
                i += 1;
            }
        }
        a.swap(i, end);
        i+1
    }

    ///Heap Sort: Sort a slice according to the way you define the cmp parameter.
    ///
    /// |           | Time complexity | Space complexity |
    /// |:----------|:---------------:|:----------------:|
    /// | Best:     | Ω(nlog(n))      |                  |
    /// | Avrg:     | θ(nlog(n))      |                  |
    /// | Worst:    | O(nlog(n))      | O(1)             |
    ///
    /// #Examples
    /// ```rust
    /// use algo::sort;
    ///
    /// let mut v = [9, 3, 5, 7, 8, 7];
    /// // Crescent sorting
    /// sort::heap(&mut v, &|a,b| a<b);
    /// ```
    pub fn heap<T: Copy+Ord, C: Fn(&T, &T) -> bool>(a: &mut [T], cmp: &C) {
        let (start, end) = (0, a.len());
        for i in (start..end/2).rev() {
            heapify(&mut a[..], cmp, i);
        }
        for i in (0..end).rev() {
            a.swap(0, i);
            heapify(&mut a[..i], cmp, 0);
        }
    }
    fn heapify<T: Copy+Ord, C: Fn(&T, &T) -> bool>(a: &mut [T], cmp: &C, aux: usize) {
        let end = a.len();
        let mut root = aux;
        let (left_child, right_child) = (2*aux, 2*aux+1);
        if left_child < end && cmp(&a[root], &a[left_child]) {
            root = left_child;
        }
        if right_child < end && cmp(&a[root], &a[right_child]) {
            root = right_child;
        }
        if root != aux {
            a.swap(aux, root);
            heapify(a, cmp, root);
        }
    }


}

#[cfg(test)]
pub mod test {
    use rand::prelude::*;

    use super::sort::*;

    // TODO: Fix tests!!
    #[test]
    pub fn selection_test() {
        let mut rng = thread_rng();
        for _ in 0u32 .. 50000u32 {
            let len: usize = rng.gen();
            let mut v: Vec<isize> = rng.gen_iter::<isize>().take((len % 32) + 1).collect();
            selection(&mut v, &|a,b| a<=b);
            for i in 0 .. v.len() - 1 {
                assert!(v[i] <= v[i + 1])
            }
            let mut u: Vec<isize> = rng.gen_iter::<isize>().take((len % 32) + 1).collect();
            selection(&mut u, &|a,b| a>b);
            for i in 0 .. u.len() - 1 {
                assert!(u[i] >= u[i + 1])
            }
        }
    }
    #[test]
    pub fn bubble_test() {
        let mut rng = thread_rng();
        for _ in 0u32 .. 50000u32 {
            let len: usize = rng.gen();
            let mut v: Vec<isize> = rng.gen_iter::<isize>().take((len % 32) + 1).collect();
            bubble(&mut v, &|a,b| a<b);
            for i in 0 .. v.len() - 1 {
                assert!(v[i] <= v[i + 1])
            }
            let mut u: Vec<isize> = rng.gen_iter::<isize>().take((len % 32) + 1).collect();
            bubble(&mut u, &|a,b| a>b);
            for i in 0 .. u.len() - 1 {
                assert!(u[i] >= u[i + 1])
            }
        }
    }
    #[test]
    pub fn cocktail_test() {
        let mut rng = thread_rng();
        for _ in 0u32 .. 50000u32 {
            let len: usize = rng.gen();
            let mut v: Vec<isize> = rng.gen_iter::<isize>().take((len % 32) + 1).collect();
            cocktail(&mut v, &|a,b| a<b);
            for i in 0 .. v.len() - 1 {
                assert!(v[i] <= v[i + 1])
            }
            let mut u: Vec<isize> = rng.gen_iter::<isize>().take((len % 32) + 1).collect();
            cocktail(&mut u, &|a,b| a>b);
            for i in 0 .. u.len() - 1 {
                assert!(u[i] >= u[i + 1])
            }
        }
    }
    #[test]
    pub fn insection_test() {
        let mut rng = thread_rng();
        for _ in 0u32 .. 50000u32 {
            let len: usize = rng.gen();
            let mut v: Vec<isize> = rng.gen_iter::<isize>().take((len % 32) + 1).collect();
            insection(&mut v, &|a,b| a<b);
            for i in 0 .. v.len() - 1 {
                assert!(v[i] <= v[i + 1])
            }
            let mut u: Vec<isize> = rng.gen_iter::<isize>().take((len % 32) + 1).collect();
            insection(&mut u, &|a,b| a>b);
            for i in 0 .. u.len() - 1 {
                assert!(u[i] >= u[i + 1])
            }
        }
    }
    #[test]
    pub fn merge_test() {
        let mut rng = thread_rng();
        for _ in 0u32 .. 50000u32 {
            let len: usize = rng.gen();
            let mut v: Vec<isize> = rng.gen_iter::<isize>().take((len % 32) + 1).collect();
            merge(&mut v, &|a,b| a<b);
            for i in 0 .. v.len() - 1 {
                assert!(v[i] <= v[i + 1])
            }
            let mut u: Vec<isize> = rng.gen_iter::<isize>().take((len % 32) + 1).collect();
            merge(&mut u, &|a,b| a>b);
            for i in 0 .. u.len() - 1 {
                assert!(u[i] >= u[i + 1])
            }
        }
    }
    #[test]
    pub fn quick_test() {
        let mut rng = thread_rng();
        for _ in 0u32 .. 50000u32 {
            let len: usize = rng.gen();
            let mut v: Vec<isize> = rng.gen_iter::<isize>().take((len % 32) + 1).collect();
            quick(&mut v, &|a,b| a<b);
            for i in 0 .. v.len() - 1 {
                assert!(v[i] <= v[i + 1])
            }
            let mut u: Vec<isize> = rng.gen_iter::<isize>().take((len % 32) + 1).collect();
            quick(&mut u, &|a,b| a>b);
            for i in 0 .. u.len() - 1 {
                assert!(u[i] >= u[i + 1])
            }
        }
    }
    #[test]
    pub fn heap_test() {
        let mut rng = thread_rng();
        for _ in 0u32 .. 50000u32 {
            let len: usize = rng.gen();
            let mut v: Vec<isize> = rng.gen_iter::<isize>().take((len % 32) + 1).collect();
            heap(&mut v, &|a,b| a<b);
            for i in 0 .. v.len() - 2 {
                assert!(v[i] <= v[i + 1])
            }
            let mut u: Vec<isize> = rng.gen_iter::<isize>().take((len % 32) + 1).collect();
            heap(&mut u, &|a,b| a>b);
            for i in 0 .. u.len() - 1 {
                assert!(u[i] >= u[i + 1])
            }
        }
    }
}
