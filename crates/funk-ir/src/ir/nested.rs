//! Modules nest to any depth (ADR-2026-11-10-1510, ADR-2026-10-30-1333): a
//! [`NestedModule`] holds items, which may be modules in turn.
//!
//! `NestedModule` is where the nesting of items turns, so it writes by
//! hand, from walks over its [`Entry`]s, the traits that `#[derive]` would
//! write recursively: `Clone`, `PartialEq`, `Hash`, `Debug` and `Drop`.
//! `Item` derives its own, which call the nested module's and so never
//! recurse.

use std::fmt;
use std::hash::{Hash, Hasher};

use super::debug::{Bracket, DebugTree};
use super::module::{Func, Item};
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

/// A nested module or a function: a node of a walk over nested modules.
#[derive(Clone, Copy)]
pub(crate) enum Entry<'a> {
    Module(&'a NestedModule),
    Func(&'a Func),
}

/// The items of a nested module, as entries.
pub(crate) struct Entries<'a>(std::slice::Iter<'a, Item>);

impl<'a> Iterator for Entries<'a> {
    type Item = Entry<'a>;

    fn next(&mut self) -> Option<Entry<'a>> {
        self.0.next().map(|i| match i {
            Item::Func(f) => Entry::Func(f),
            Item::Module(m) => Entry::Module(m),
        })
    }
}

impl<'a> Node for Entry<'a> {
    type Children = Entries<'a>;

    fn children(self) -> Entries<'a> {
        match self {
            Entry::Module(m) => Entries(m.items.iter()),
            Entry::Func(_) => Entries([].iter()),
        }
    }

    fn is_leaf(self) -> bool {
        match self {
            Entry::Module(m) => m.items.is_empty(),
            Entry::Func(_) => true,
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
                Step::Enter(Entry::Module(m)) => {
                    items.push(Item::Module(module_head(m)));
                    items.open(m.items.len());
                }
                Step::Leave(Entry::Module(_)) => {
                    items.close_module();
                }
                Step::Leave(Entry::Func(_)) => {}
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
                Step::Leave(Entry::Func(_)) => {}
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
