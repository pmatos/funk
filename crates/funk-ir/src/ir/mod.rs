//! The in-memory IR: the abstract syntax of `lean/Fir/Syntax/`, with the
//! builder.

mod aggregate;
mod attr;
mod build;
mod debug;
mod extern_decl;
mod global;
mod int;
pub mod layout;
mod location;
mod module;
pub mod names;
mod nested;
mod region;
pub(crate) mod tree;

pub use aggregate::{Aggregate, AggregateFault, Field};
pub use attr::{Attr, Type};
pub use extern_decl::Extern;
pub use global::{Global, GlobalFault, InitPiece, Linkage};
pub use int::{Int, Nat};
pub use layout::{ByteOrder, MemLayout};
pub use location::{LocRef, LocTable, Location};
pub use module::{
    Block, Def, DialectItem, Func, FuncType, Item, Module, Op, Region, Succ, SymbolTable,
    attrs_trimmed, trim_attrs,
};
pub use nested::NestedModule;
pub(crate) use nested::Table;
pub(crate) use region::Part;
