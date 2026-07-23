//! Language-agnostic pattern-match usefulness and exhaustiveness analysis.
//!
//! This crate implements the pattern-matrix algorithm from Luc Maranget's
//! [*Warnings for pattern matching*][paper]. The core only knows about typed
//! pattern structure and constructor families. Source spans, names, type
//! inference, literal canonicalization, and diagnostics remain in a compiler
//! adapter.
//!
//! [paper]: http://moscova.inria.fr/~maranget/papers/warn/warn.pdf

#![forbid(unsafe_code)]

mod engine;
mod matrix;
mod model;

pub use engine::{analyze, analyze_with_config, usefulness, usefulness_with_config};
pub use matrix::{ColumnSignature, MatrixError, PatternMatrix, PatternRow};
pub use model::{
    Analysis, Arm, Config, ConstructorFields, ConstructorOracle, ConstructorSpace, Exhaustiveness,
    Guard, InconclusiveReason, InputError, MissingHead, Pattern, Reachability, UnreachableReason,
    Usefulness, Witness,
};
