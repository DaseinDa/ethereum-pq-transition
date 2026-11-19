//! Research option-C aggregate verifier and C ABI. Keys and proof parameters are fixed at build time.
#![allow(dead_code)]
mod childpin;
mod fkernel;
mod material;
pub mod aggregate_native;
pub mod corpus;
pub use aggregate_native::{verify, VerifyError, TrustedParams, TRUSTED_PARAMS};
pub mod sparse_periodic;
