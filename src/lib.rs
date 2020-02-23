//! This crate is a collection of algorithms, mostly intended as learning exercise.
//!
//! ## What is implemented:
//!  - Several sort algorithms
//!  - Some search algorithms
//!  - Some pattern algorithms
//!  - Some numeric sequence algorithms
//!
//! ## Features
//! This crate have a feature called `big_num` and it is active by default.
//!
//! In case your needs don't require using big numbers and you want to reduce the crate
//! numbers to be compiled and the compile time, you can disactivate the default features.

pub mod numerics;
pub mod pattern;
pub mod search;
pub mod sort;
