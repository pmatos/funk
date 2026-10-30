//! The in-memory IR: the abstract syntax of `lean/Fir/Syntax/`, with the
//! builder.

mod attr;
mod build;
mod int;
mod location;
mod module;
pub mod names;

pub use attr::{Attr, Type};
pub use int::{Int, Nat};
pub use location::{LocRef, LocTable, Location};
pub use module::{Block, Def, Func, FuncType, Item, Module, Op, Region, Succ, SymbolTable};
