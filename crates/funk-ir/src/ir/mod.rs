//! The in-memory IR: the abstract syntax of `lean/Fir/Syntax/`, with the
//! builder.

mod attr;
mod build;
mod debug;
mod int;
mod location;
mod module;
pub mod names;
mod nested;
mod region;
pub(crate) mod tree;

pub use attr::{Attr, Type};
pub use int::{Int, Nat};
pub use location::{LocRef, LocTable, Location};
pub use module::{
    Block, Def, DialectItem, Func, FuncType, Item, Module, Op, Region, Succ, SymbolTable,
};
pub use nested::NestedModule;
pub(crate) use nested::Table;
pub(crate) use region::Part;
