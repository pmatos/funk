//! `funk-ir`: fir's in-memory IR, with its op registry, builder, parser,
//! printer and verifier.
//!
//! The merged fir v0 spec in `lean/` is the reference for every rule here;
//! each module names the part of the spec it follows. Ops and types are
//! generic data checked through a [`Registry`] of dialects (G0,
//! ADR-2026-10-29-2016; ADR-2026-10-30-1031), so an extension dialect adds
//! ops and types without a change to the IR, the parser or the printer.
//!
//! The parser, the printer and the verifier recurse once per level of
//! nesting of attributes, regions and items, so a deeply nested text needs a
//! deep stack: the `funk` binary runs them on a 1 GiB stack (#36).
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

pub mod dialects;
pub mod generate;
pub mod ir;
pub mod registry;
pub mod text;
pub mod verify;

pub use ir::{
    Attr, Block, Def, Func, FuncType, Int, Item, LocRef, LocTable, Location, Module, Op, Region,
    Succ, SymbolTable, Type,
};
pub use registry::{Dialect, OpContext, OpShape, OpSpec, OpTypes, Registry, TypeCheck, TypeSpec};
pub use text::{ParseError, TextPos, parse, print};
pub use verify::{Diagnostic, verify};
