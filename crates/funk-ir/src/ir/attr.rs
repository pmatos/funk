//! Attributes and types, as generic terms (`Attr` in
//! `lean/Fir/Text/Grammar.lean`).
//!
//! An attribute is a constant part of an op that is not a value. Attributes
//! and types are written as generic terms, so a new dialect needs no new
//! syntax and no change to these types (G0, ADR-2026-10-29-2016).
//!
//! Attributes nest to any depth (ADR-2026-10-30-1333), so `Attr` writes by
//! hand, without recursion, the traits that `#[derive]` would write
//! recursively: `Clone`, `PartialEq`, `Hash`, `Debug` and `Drop`. A type
//! holds attributes, and derives its traits from theirs.

use std::fmt;
use std::hash::{Hash, Hasher};

use super::debug::{Bracket, DebugTree};
use super::int::Int;
use super::tree::{self, Nest, Node, Step, walk};

/// An attribute: a word such as `nsw`, an integer, a string, a symbol
/// reference such as `@sum`, or a word applied to attributes, such as
/// `vec(4, i32)`. A word applied to no attributes, `h()`, is not the word `h`.
///
/// `Attr` implements `Drop`, so a field cannot be moved out of an owned
/// `Attr`: borrow it, clone it, or take it with [`std::mem::take`].
pub enum Attr {
    /// A word, such as a flag or a predicate.
    Word(String),
    /// An integer, of any size.
    Int(Int),
    /// A string.
    Str(String),
    /// A reference to a symbol, without its `@`.
    Sym(String),
    /// A word applied to attributes.
    App(String, Vec<Attr>),
}

impl Attr {
    /// The word attribute `w`.
    pub fn word(w: impl Into<String>) -> Attr {
        Attr::Word(w.into())
    }

    /// The integer attribute `v`.
    pub fn int(v: i128) -> Attr {
        Attr::Int(Int::from(v))
    }
}

impl<'a> Node for &'a Attr {
    type Children = std::slice::Iter<'a, Attr>;

    fn children(self) -> Self::Children {
        match self {
            Attr::App(_, args) => args.iter(),
            _ => [].iter(),
        }
    }

    fn is_leaf(self) -> bool {
        match self {
            Attr::App(_, args) => args.is_empty(),
            _ => true,
        }
    }
}

/// Arguments built top down, as the parser reads them and `Attr::clone`
/// copies them.
impl Nest<Attr> {
    /// Ends the list of arguments being built and gives it to the applied
    /// word that owns it. Returns false, and does nothing, for the outermost
    /// list.
    pub(crate) fn close_app(&mut self) -> bool {
        let Some((args, owner)) = self.close() else {
            return false;
        };
        if let Attr::App(_, owned) = owner {
            *owned = args;
        }
        true
    }
}

impl Attr {
    /// A copy of this attribute without its arguments.
    fn head(&self) -> Attr {
        match self {
            Attr::Word(w) => Attr::Word(w.clone()),
            Attr::Int(i) => Attr::Int(i.clone()),
            Attr::Str(s) => Attr::Str(s.clone()),
            Attr::Sym(s) => Attr::Sym(s.clone()),
            Attr::App(h, _) => Attr::App(h.clone(), Vec::new()),
        }
    }
}

impl Clone for Attr {
    fn clone(&self) -> Attr {
        if self.is_leaf() {
            return self.head();
        }
        let mut nest = Nest::new(1);
        for step in walk(self) {
            match step {
                Step::Enter(a) => {
                    nest.push(a.head());
                    if let Attr::App(_, args) = a {
                        nest.open(args.len());
                    }
                }
                Step::Leave(Attr::App(..)) => {
                    nest.close_app();
                }
                Step::Leave(_) => {}
            }
        }
        nest.finish().pop().expect("a walk copies its root")
    }
}

impl PartialEq for Attr {
    fn eq(&self, other: &Attr) -> bool {
        tree::equal(self, other, |a, b| match (a, b) {
            (Attr::Word(x), Attr::Word(y))
            | (Attr::Str(x), Attr::Str(y))
            | (Attr::Sym(x), Attr::Sym(y))
            | (Attr::App(x, _), Attr::App(y, _)) => x == y,
            (Attr::Int(x), Attr::Int(y)) => x == y,
            _ => false,
        })
    }
}

impl Eq for Attr {}

impl Hash for Attr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        tree::hash(self, state, |a, state| {
            std::mem::discriminant(a).hash(state);
            match a {
                Attr::Word(s) | Attr::Str(s) | Attr::Sym(s) | Attr::App(s, _) => s.hash(state),
                Attr::Int(i) => i.hash(state),
            }
        });
    }
}

impl fmt::Debug for Attr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut out = DebugTree::new(f);
        for step in walk(self) {
            let (name, value): (&str, &dyn fmt::Debug) = match step {
                Step::Enter(Attr::App(h, _)) => {
                    out.open(None, "App", Bracket::Tuple)?;
                    out.value(None, h)?;
                    out.open(None, "", Bracket::List)?;
                    continue;
                }
                Step::Leave(Attr::App(..)) => {
                    out.close()?;
                    out.close()?;
                    continue;
                }
                Step::Leave(_) => continue,
                Step::Enter(Attr::Word(w)) => ("Word", w),
                Step::Enter(Attr::Int(i)) => ("Int", i),
                Step::Enter(Attr::Str(s)) => ("Str", s),
                Step::Enter(Attr::Sym(s)) => ("Sym", s),
            };
            out.open(None, name, Bracket::Tuple)?;
            out.value(None, value)?;
            out.close()?;
        }
        Ok(())
    }
}

impl Drop for Attr {
    fn drop(&mut self) {
        if let Attr::App(_, args) = self {
            tree::drop_all(std::mem::take(args), |a, rest| {
                if let Attr::App(_, args) = a {
                    rest.append(args);
                }
            });
        }
    }
}

/// A type, as written in text: a word such as `i32`, or a word applied to
/// attributes. Which terms are types, and which types are valid, is up to the
/// dialects in the registry: the core dialect's `iN` and `ptr` are one
/// dialect's types, not the whole type system.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Type {
    /// The word that heads the type, such as `i32`.
    pub name: String,
    /// The attributes the word is applied to, if it is applied.
    pub args: Option<Vec<Attr>>,
}

impl Type {
    /// The type written as the word `w`.
    pub fn word(w: impl Into<String>) -> Type {
        Type {
            name: w.into(),
            args: None,
        }
    }

    /// The type written as the word `h` applied to `args`.
    pub fn app(h: impl Into<String>, args: Vec<Attr>) -> Type {
        Type {
            name: h.into(),
            args: Some(args),
        }
    }
}
