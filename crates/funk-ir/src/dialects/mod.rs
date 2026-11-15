//! The dialects that `funk-ir` defines. Each one registers its ops and types
//! with the [`Registry`](crate::Registry); an extension dialect does the same
//! from outside this crate. `core` is the core dialect, and `gpu` the
//! second dialect in tree (ADR-2026-11-09-1545).

pub mod core;
pub mod gpu;

use crate::Registry;

/// The dialects in tree, registered: the core and `gpu`. `funk` reads these,
/// as `fir-ref fmt` and `fir-ref validate` read `CoreGpu`.
pub fn in_tree() -> Registry {
    let mut r = Registry::core();
    r.register(gpu::dialect())
        .expect("the gpu dialect registers beside the core");
    r
}
