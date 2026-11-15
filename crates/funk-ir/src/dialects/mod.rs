//! The dialects that `funk-ir` defines. Each one registers its ops and types
//! with the [`Registry`](crate::Registry); an extension dialect does the same
//! from outside this crate. `core` is the core dialect, and `gpu` the
//! second dialect in tree (ADR-2026-11-09-1545).

pub mod core;
pub mod gpu;
