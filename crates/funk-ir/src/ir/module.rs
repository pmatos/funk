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
use super::layout::MemLayout;
use super::location::{LocRef, LocTable};
use super::nested::NestedModule;
use super::region::Part;

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
    /// The regions the op owns, of the kinds that its registration states.
    /// No core op has one.
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

/// A region: its kind and a list of blocks, the first of which is its entry.
///
/// A region names its kind (ADR-2026-11-09-1543). `None` is the core's
/// kind, a control-flow graph whose ops run in order (ADR-2026-10-29-2005);
/// a dialect's kind is a word of that dialect, such as `toy.graph`.
///
/// Regions nest to any depth, so `Region` writes its `Clone`, `PartialEq`,
/// `Hash`, `Debug` and `Drop` without recursion
/// (`docs/decisions/rust-ir-and-tools.md#nesting`).
/// Because it implements `Drop`, its blocks cannot be moved out of an owned
/// `Region`: take them with [`std::mem::take`].
#[derive(Default)]
pub struct Region {
    /// The region's kind, or `None` for the core's kind.
    pub kind: Option<String>,
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

    /// Every type that the function states (`Func.types`): its results,
    /// its parameters, then the arguments and op results of each block, at
    /// any depth.
    pub fn types(&self) -> impl Iterator<Item = &Type> {
        let defs = self.body.parts().flat_map(|part| match part {
            Part::Block(b) => Some(b.params.iter().chain(b.ops.iter().flat_map(|o| &o.results))),
            _ => None,
        });
        self.results
            .iter()
            .chain(self.params.iter().map(|p| &p.ty))
            .chain(defs.flatten().map(|d| &d.ty))
    }
}

/// An item of a kind that a dialect registers (`DialectItem` in
/// `lean/Fir/Syntax/Module.lean`, ADR-2026-11-09-1543): what the one
/// production of an item writes, `kind @sym(params) -> results attrs { }`,
/// with an empty body. Its kind is a word of the dialect, such as
/// `toy.cell`, and the dialect's [`ItemKindSpec`](crate::registry::ItemKindSpec)
/// for the kind says what its parameters, results and attributes must be.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct DialectItem {
    /// The item's kind: a word of a dialect, `name.word`.
    pub kind: String,
    /// The item's symbol, without `@`. Any string.
    pub name: String,
    /// The item's parameters.
    pub params: Vec<Def>,
    /// The item's result types.
    pub results: Vec<Type>,
    /// The item's attributes, as the text writes them.
    pub attrs: Vec<Attr>,
}

impl DialectItem {
    /// The item of kind `kind` with symbol `name`, and no parameters,
    /// results or attributes.
    pub fn new(kind: impl Into<String>, name: impl Into<String>) -> DialectItem {
        DialectItem {
            kind: kind.into(),
            name: name.into(),
            params: Vec::new(),
            results: Vec::new(),
            attrs: Vec::new(),
        }
    }

    /// Every type that the item states: its parameters' types, then its
    /// results (`DialectItem.types`).
    pub fn types(&self) -> impl Iterator<Item = &Type> {
        self.params.iter().map(|p| &p.ty).chain(&self.results)
    }
}

/// An item of a module. Every item is written
/// `kind @sym(params) -> results attrs { body }` (N2). The core's kinds are
/// `func` and `module` (ADR-2026-11-10-1510), and a dialect registers kinds
/// of its own (ADR-2026-11-09-1543).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Item {
    /// A function.
    Func(Func),
    /// A nested module: a symbol table of its own, with its own dialect set.
    Module(NestedModule),
    /// An item of a kind that a dialect registers.
    Dialect(DialectItem),
}

impl Item {
    /// The item's symbol.
    pub fn name(&self) -> &str {
        match self {
            Item::Func(f) => &f.name,
            Item::Module(m) => &m.name,
            Item::Dialect(i) => &i.name,
        }
    }

    /// The item's function, if it is one.
    pub fn as_func(&self) -> Option<&Func> {
        match self {
            Item::Func(f) => Some(f),
            _ => None,
        }
    }

    /// The item's function, mutably, if it is one.
    pub fn as_func_mut(&mut self) -> Option<&mut Func> {
        match self {
            Item::Func(f) => Some(f),
            _ => None,
        }
    }

    /// The item of a dialect's kind that this item is, if it is one.
    pub fn as_dialect(&self) -> Option<&DialectItem> {
        match self {
            Item::Dialect(i) => Some(i),
            _ => None,
        }
    }
}

/// A module: its dialect set, its data layout, its items, then its location
/// table.
///
/// A module is a symbol table over its own items. A nested module is an
/// item, [`NestedModule`], with a symbol table of its own, so nothing here
/// assumes one global table.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Module {
    /// The dialect set: the names of the dialects other than the core whose
    /// words the module writes, in the order the text writes them. Empty
    /// for a module of the core alone (ADR-2026-11-10-1306).
    pub dialects: Vec<String>,
    /// The data layout: an entry for each memory it declares, in the order
    /// the text writes them (ADR-2026-11-12-1821). Empty for a module with
    /// the default memory alone. A nested module has none of its own.
    pub layout: Vec<MemLayout>,
    /// The items, in order.
    pub items: Vec<Item>,
    /// The location table.
    pub locs: LocTable,
}

impl Module {
    /// The module's own functions, in order. Those of a nested module are
    /// not among them.
    pub fn funcs(&self) -> impl Iterator<Item = &Func> {
        self.table().funcs()
    }

    /// The symbol table of this module's own items.
    pub fn symbols(&self) -> SymbolTable<'_> {
        SymbolTable::of(&self.items)
    }
}

/// The items of one symbol table, by symbol. When two items share a symbol,
/// which validation rejects, the first function wins, or else the first
/// item.
#[derive(Clone, Debug)]
pub struct SymbolTable<'m> {
    map: HashMap<&'m str, &'m Item>,
}

impl<'m> SymbolTable<'m> {
    /// The symbol table of the items `items`: those of a module, or of a
    /// module nested in one.
    ///
    /// A symbol names its first function, as `SymbolTable.symbols` in
    /// `lean/Fir/Validation/Scope.lean` does, and otherwise its first item.
    pub fn of(items: &'m [Item]) -> SymbolTable<'m> {
        let mut map: HashMap<&str, &Item> = HashMap::new();
        for item in items {
            let first = map.entry(item.name()).or_insert(item);
            if first.as_func().is_none() && item.as_func().is_some() {
                *first = item;
            }
        }
        SymbolTable { map }
    }

    /// The item that `name` names.
    pub fn get(&self, name: &str) -> Option<&'m Item> {
        self.map.get(name).copied()
    }

    /// The type of the function that `name` names.
    pub fn func_type(&self, name: &str) -> Option<FuncType> {
        self.get(name).and_then(Item::as_func).map(Func::func_type)
    }
}
