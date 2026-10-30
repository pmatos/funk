//! Modules, items, functions, blocks and generic ops
//! (`lean/Fir/Syntax/Module.lean`).
//!
//! Every op has the same shape, whatever its dialect (G0): results, a name,
//! attributes, operands, successors, regions and a location reference. Ops are
//! data checked through the op registry, not a closed Rust `enum`
//! (ADR-2026-10-30-1146). Values, labels and symbols are referred to by name,
//! stored without their sigils, exactly as the producer wrote them.

use std::collections::HashMap;

use super::attr::{Attr, Type};
use super::location::{LocRef, LocTable};

/// A definition of a value: its name, without `%`, and its type.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Def {
    /// The value's name.
    pub name: String,
    /// The value's type.
    pub ty: Type,
}

impl Def {
    /// The definition `%name: ty`.
    pub fn new(name: impl Into<String>, ty: Type) -> Def {
        Def {
            name: name.into(),
            ty,
        }
    }
}

/// A successor of a terminator: the label of the block control may go to,
/// and the values passed to that block's arguments (H1).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Succ {
    /// The target block's label, without `^`.
    pub label: String,
    /// One value for each argument of the target block.
    pub args: Vec<String>,
}

impl Succ {
    /// The successor `^label(args)`.
    pub fn new(label: impl Into<String>, args: Vec<String>) -> Succ {
        Succ {
            label: label.into(),
            args,
        }
    }
}

/// An op in place, in a block, in the spec's order of parts.
///
/// `loc` is a plain field, not an `Option`: no op exists without a location
/// (H8). `unknown` is a location like any other entry of the table.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Op {
    /// The values the op defines, with their types.
    pub results: Vec<Def>,
    /// The op's name, such as `add` or `toy.mix`.
    pub name: String,
    /// The op's attributes, such as the value of a `const`.
    pub attrs: Vec<Attr>,
    /// The values the op uses, by name.
    pub operands: Vec<String>,
    /// The blocks a terminator may go to. Only terminators have them.
    pub succs: Vec<Succ>,
    /// The regions the op owns. No core op has one.
    pub regions: Vec<Region>,
    /// The op's location reference into the module's location table.
    pub loc: LocRef,
}

/// A block: a label, typed arguments, and ops whose last op is the block's
/// terminator.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Block {
    /// The block's label, without `^`.
    pub label: String,
    /// The block's arguments.
    pub params: Vec<Def>,
    /// The block's ops.
    pub ops: Vec<Op>,
}

/// A region: a list of blocks, the first of which is its entry.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Region {
    /// The region's blocks.
    pub blocks: Vec<Block>,
}

/// A function: a region isolated from above (H2, ADR-2026-10-29-2011).
///
/// A function owns its blocks and holds no reference to its module or to
/// other functions, so a pass that holds `&mut Func` cannot reach another
/// function: Rust's ownership enforces the isolation. Functions refer to each
/// other only by symbol.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Func {
    /// The function's symbol, without `@`. Any string.
    pub name: String,
    /// The parameters: the arguments of the entry block.
    pub params: Vec<Def>,
    /// The types the function returns: any number, none included.
    pub results: Vec<Type>,
    /// The function's blocks.
    pub body: Region,
}

/// The type of a function: what it takes and what it returns.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FuncType {
    /// The parameter types.
    pub params: Vec<Type>,
    /// The result types.
    pub results: Vec<Type>,
}

impl Func {
    /// The function's type.
    pub fn func_type(&self) -> FuncType {
        FuncType {
            params: self.params.iter().map(|d| d.ty.clone()).collect(),
            results: self.results.clone(),
        }
    }
}

/// An item of a module. Every item is written
/// `kind @sym(params) -> results attrs { body }` (N2). M0 has one kind,
/// `func`. A nested module, a global or an external declaration would each be
/// a new kind, and a new variant here; how dialects add kinds is H4 and H5.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Item {
    /// A function.
    Func(Func),
}

impl Item {
    /// The item's symbol.
    pub fn name(&self) -> &str {
        match self {
            Item::Func(f) => &f.name,
        }
    }

    /// The item's function, if it is one.
    pub fn as_func(&self) -> Option<&Func> {
        match self {
            Item::Func(f) => Some(f),
        }
    }

    /// The item's function, mutably, if it is one.
    pub fn as_func_mut(&mut self) -> Option<&mut Func> {
        match self {
            Item::Func(f) => Some(f),
        }
    }
}

/// A module: its items, then its location table.
///
/// A module is a symbol table over its own items. A nested module would be
/// an item holding a `Module` with a symbol table of its own, so nothing here
/// assumes one global table.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Module {
    /// The items, in order.
    pub items: Vec<Item>,
    /// The location table.
    pub locs: LocTable,
}

impl Module {
    /// The module's functions, in order.
    pub fn funcs(&self) -> impl Iterator<Item = &Func> {
        self.items.iter().filter_map(Item::as_func)
    }

    /// The symbol table of this module's own items.
    pub fn symbols(&self) -> SymbolTable<'_> {
        let mut map = HashMap::new();
        for item in &self.items {
            map.entry(item.name()).or_insert(item);
        }
        SymbolTable { map }
    }
}

/// The items of one module, by symbol. When two items share a symbol, which
/// validation rejects, the first one wins.
#[derive(Clone, Debug)]
pub struct SymbolTable<'m> {
    map: HashMap<&'m str, &'m Item>,
}

impl<'m> SymbolTable<'m> {
    /// The item that `name` names.
    pub fn get(&self, name: &str) -> Option<&'m Item> {
        self.map.get(name).copied()
    }

    /// The type of the function that `name` names.
    pub fn func_type(&self, name: &str) -> Option<FuncType> {
        self.get(name).and_then(Item::as_func).map(Func::func_type)
    }
}
