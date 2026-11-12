//! Modules nest to any depth (ADR-2026-11-10-1510,
//! `docs/decisions/rust-ir-and-tools.md#nesting`): a
//! [`NestedModule`] holds items, which may be modules in turn.
//!
//! `NestedModule` is where the nesting of items turns, so it writes by
//! hand, from walks over its [`Entry`]s, the traits that `#[derive]` would
//! write recursively: `Clone`, `PartialEq`, `Hash`, `Debug` and `Drop`.
//! `Item` derives its own, which call the nested module's and so never
//! recurse. A function and an item of a dialect's kind are leaves of the
//! walk.

use std::fmt;
use std::hash::{Hash, Hasher};

use super::debug::{Bracket, DebugTree};
use super::module::{DialectItem, Func, Item, Module};
use super::tree::{self, Nest, Node, Step, walk};

/// A module nested in another, as an item of kind `module`
/// (ADR-2026-11-10-1510). Its symbols and its dialect set are its own, not
/// its parent's, and the module's one location table serves its ops too.
#[derive(Default)]
pub struct NestedModule {
    /// The module's symbol, without `@`. Any string.
    pub name: String,
    /// The module's own dialect set, in the order the text writes it.
    pub dialects: Vec<String>,
    /// The module's items, in order. `NestedModule` implements `Drop`, so
    /// take them with [`std::mem::take`].
    pub items: Vec<Item>,
}

impl NestedModule {
    /// A nested module with no dialect set and no items.
    pub fn new(name: impl Into<String>) -> NestedModule {
        NestedModule {
            name: name.into(),
            dialects: Vec::new(),
            items: Vec::new(),
        }
    }
}

/// A symbol table of a module (`SymbolTable` in
/// `lean/Fir/Validation/Scope.lean`): the dialect set and the items of the
/// module, or of a module nested in it.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Table<'a> {
    pub dialects: &'a [String],
    pub items: &'a [Item],
}

impl<'a> Table<'a> {
    /// The table of a nested module.
    fn of(m: &'a NestedModule) -> Table<'a> {
        Table {
            dialects: &m.dialects,
            items: &m.items,
        }
    }

    /// The table's functions, in order. A nested module's are its own.
    pub fn funcs(self) -> impl Iterator<Item = &'a Func> {
        self.items.iter().filter_map(Item::as_func)
    }

    /// The table's items of a dialect's kind, in order
    /// (`SymbolTable.dialectItems`).
    pub fn dialect_items(self) -> impl Iterator<Item = &'a DialectItem> {
        self.items.iter().filter_map(Item::as_dialect)
    }
}

impl Module {
    /// The module's own symbol table: its dialect set and its items.
    pub(crate) fn table(&self) -> Table<'_> {
        Table {
            dialects: &self.dialects,
            items: &self.items,
        }
    }

    /// Every symbol table of the module, in the order of `Module.tables`:
    /// its own, then that of each nested module, at any depth, each before
    /// the tables nested in it. A walk keeps the path on the heap, so this
    /// takes no stack per level of nesting.
    pub(crate) fn tables(&self) -> Vec<Table<'_>> {
        let nested = self.items.iter().flat_map(|i| match i {
            Item::Module(n) => Some(walk(Entry::Module(n)).filter_map(Step::entered)),
            Item::Func(_) | Item::Dialect(_) => None,
        });
        std::iter::once(self.table())
            .chain(nested.flatten().filter_map(|e| match e {
                Entry::Module(m) => Some(Table::of(m)),
                Entry::Func(_) | Entry::Dialect(_) => None,
            }))
            .collect()
    }
}

/// A nested module, a function or an item of a dialect's kind: a node of a
/// walk over nested modules.
#[derive(Clone, Copy)]
pub(crate) enum Entry<'a> {
    Module(&'a NestedModule),
    Func(&'a Func),
    Dialect(&'a DialectItem),
}

/// The items of a nested module, as entries.
pub(crate) struct Entries<'a>(std::slice::Iter<'a, Item>);

impl<'a> Iterator for Entries<'a> {
    type Item = Entry<'a>;

    fn next(&mut self) -> Option<Entry<'a>> {
        self.0.next().map(|i| match i {
            Item::Func(f) => Entry::Func(f),
            Item::Module(m) => Entry::Module(m),
            Item::Dialect(i) => Entry::Dialect(i),
        })
    }
}

impl<'a> Node for Entry<'a> {
    type Children = Entries<'a>;

    fn children(self) -> Entries<'a> {
        match self {
            Entry::Module(m) => Entries(m.items.iter()),
            Entry::Func(_) | Entry::Dialect(_) => Entries([].iter()),
        }
    }

    fn is_leaf(self) -> bool {
        match self {
            Entry::Module(m) => m.items.is_empty(),
            Entry::Func(_) | Entry::Dialect(_) => true,
        }
    }
}

/// A nested module with the symbol and dialect set of `m`, and room for its
/// items.
fn module_head(m: &NestedModule) -> NestedModule {
    NestedModule {
        name: m.name.clone(),
        dialects: m.dialects.clone(),
        items: Vec::with_capacity(m.items.len()),
    }
}

/// Items built top down, as the decoder and `NestedModule::clone` build
/// them: the items of the last nested module are built in the nest's inner
/// lists.
impl Nest<Item> {
    /// Ends the items being built and gives them to the nested module that
    /// owns them. Returns false, and does nothing, for the outermost items.
    pub(crate) fn close_module(&mut self) -> bool {
        let Some((items, owner)) = self.close() else {
            return false;
        };
        if let Item::Module(m) = owner {
            m.items = items;
        }
        true
    }
}

impl Clone for NestedModule {
    fn clone(&self) -> NestedModule {
        let mut items = Nest::new(self.items.len());
        for step in walk(Entry::Module(self)).skip(1) {
            match step {
                Step::Enter(Entry::Func(f)) => items.push(Item::Func(f.clone())),
                Step::Enter(Entry::Dialect(i)) => items.push(Item::Dialect(i.clone())),
                Step::Enter(Entry::Module(m)) => {
                    items.push(Item::Module(module_head(m)));
                    items.open(m.items.len());
                }
                Step::Leave(Entry::Module(_)) => {
                    items.close_module();
                }
                Step::Leave(Entry::Func(_) | Entry::Dialect(_)) => {}
            }
        }
        let mut m = module_head(self);
        m.items = items.finish();
        m
    }
}

impl PartialEq for NestedModule {
    fn eq(&self, other: &NestedModule) -> bool {
        tree::equal(Entry::Module(self), Entry::Module(other), |a, b| {
            match (a, b) {
                (Entry::Module(x), Entry::Module(y)) => {
                    x.name == y.name && x.dialects == y.dialects
                }
                (Entry::Func(x), Entry::Func(y)) => x == y,
                (Entry::Dialect(x), Entry::Dialect(y)) => x == y,
                _ => false,
            }
        })
    }
}

impl Eq for NestedModule {}

impl Hash for NestedModule {
    fn hash<H: Hasher>(&self, state: &mut H) {
        tree::hash(Entry::Module(self), state, |e, state| match e {
            Entry::Module(m) => {
                state.write_u8(0);
                (&m.name, &m.dialects).hash(state);
            }
            Entry::Func(f) => {
                state.write_u8(1);
                f.hash(state);
            }
            Entry::Dialect(i) => {
                state.write_u8(2);
                i.hash(state);
            }
        });
    }
}

impl fmt::Debug for NestedModule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut out = DebugTree::new(f);
        for step in walk(Entry::Module(self)) {
            let root = matches!(step, Step::Enter(Entry::Module(m)) | Step::Leave(Entry::Module(m))
                if std::ptr::eq(m, self));
            match step {
                Step::Enter(Entry::Func(func)) => {
                    out.open(None, "Func", Bracket::Tuple)?;
                    out.value(None, func)?;
                    out.close()?;
                }
                Step::Enter(Entry::Dialect(item)) => {
                    out.open(None, "Dialect", Bracket::Tuple)?;
                    out.value(None, item)?;
                    out.close()?;
                }
                Step::Enter(Entry::Module(m)) => {
                    if !root {
                        out.open(None, "Module", Bracket::Tuple)?;
                    }
                    out.open(None, "NestedModule", Bracket::Struct)?;
                    out.value(Some("name"), &m.name)?;
                    out.value(Some("dialects"), &m.dialects)?;
                    out.open(Some("items"), "", Bracket::List)?;
                }
                Step::Leave(Entry::Module(_)) => {
                    out.close()?;
                    out.close()?;
                    if !root {
                        out.close()?;
                    }
                }
                Step::Leave(Entry::Func(_) | Entry::Dialect(_)) => {}
            }
        }
        Ok(())
    }
}

impl Drop for NestedModule {
    fn drop(&mut self) {
        tree::drop_all(std::mem::take(&mut self.items), |i, rest| {
            if let Item::Module(m) = i {
                rest.append(&mut m.items);
            }
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Block, LocRef, Op};

    fn sample() -> NestedModule {
        let k = Func::new("k").block(Block::new("e").op(Op::new("ret", LocRef(0))));
        let inner = NestedModule {
            name: "inner".into(),
            dialects: vec!["toy".into()],
            items: vec![Item::Func(k.clone())],
        };
        NestedModule {
            name: "dev".into(),
            dialects: vec![],
            items: vec![
                Item::Module(inner),
                Item::Func(k),
                Item::Module(NestedModule::default()),
            ],
        }
    }

    #[test]
    fn clone_equals_and_debug_writes_what_derive_would() {
        let m = sample();
        let c = m.clone();
        assert!(m == c);
        let derived = "NestedModule { name: \"dev\", dialects: [], items: [Module(NestedModule { \
                       name: \"inner\", dialects: [\"toy\"], items: [Func(";
        assert!(format!("{m:?}").starts_with(derived), "{m:?}");
        assert!(
            format!("{m:#?}").contains("    items: [\n        Module(\n"),
            "{m:#?}"
        );
        let mut other = sample();
        other.items.pop();
        assert!(m != other);
    }
}
