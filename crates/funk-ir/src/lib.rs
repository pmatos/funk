//! `funk-ir`: fir's in-memory IR, with its op registry, builder, parser,
//! printer and verifier.
//!
//! The merged fir v0 spec in `lean/` is the reference for every rule here;
//! each module names the part of the spec it follows. Ops and types are
//! generic data checked through a [`Registry`] of dialects (G0,
//! ADR-2026-10-29-2016; ADR-2026-10-30-1146), so an extension dialect adds
//! ops and types without a change to the IR, the parser or the printer.
//!
//! fir has no limit on how deeply attributes, regions and items nest
//! (ADR-2026-10-30-1549), so nothing here recurses once per level: every
//! walk keeps its path on the heap, and any text or module parses, prints,
//! verifies, compares and drops on a small stack (ADR-2026-10-30-1333).
//!
//! ```
//! use funk_ir::{Registry, parse, print, verify};
//!
//! let text = "func @seven() -> i8 {\n^entry:\n  %c: i8 = const 7 @0\n  ret %c @0\n}\n\nlocs {\n  @0 = unknown\n}\n";
//! let reg = Registry::core();
//! let m = parse(text, &reg).unwrap();
//! assert!(verify(&m, &reg).is_empty());
//! assert_eq!(print(&m), text);
//! ```

// Cargo does not pass [lints] to doctests (ADR-2026-11-03-0808).
#![doc(test(attr(forbid(unsafe_code))))]

pub mod dialects;
pub mod effects;
pub mod fuzz;
pub mod generate;
pub mod ir;
pub mod registry;
pub mod text;
pub mod verify;

pub use effects::{Effects, MemSet};
pub use ir::{
    Attr, Block, Def, DialectItem, Func, FuncType, Int, Item, LocRef, LocTable, Location, Module,
    NestedModule, Op, Region, Succ, SymbolTable, Type,
};
pub use registry::{
    Dialect, FuncContext, FuncSpec, ItemKindSpec, OpContext, OpShape, OpSpec, OpTypes,
    RegionKindSpec, Registry, TypeCheck, TypeSpec,
};
pub use text::{ParseError, TextPos, parse, print};
pub use verify::{Diagnostic, verify};
