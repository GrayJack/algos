//! Module for numeric algorithms ans some iterators

#[cfg(feature = "big_num")]
pub mod factorial;
pub mod fibonacci;
pub mod prime;
pub mod primorial;

#[cfg(feature = "big_num")]
pub use factorial::BigFactorial;
#[cfg(feature = "big_num")]
pub use fibonacci::BigFib;
#[cfg(feature = "big_num")]
pub use primorial::BigPrimorial;

pub use fibonacci::Fib;
pub use prime::IsPrime;
