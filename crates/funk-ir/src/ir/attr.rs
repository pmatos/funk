//! Attributes and types, as generic terms (`Attr` in
//! `lean/Fir/Text/Grammar.lean`).
//!
//! An attribute is a constant part of an op that is not a value. Attributes
//! and types are written as generic terms, so a new dialect needs no new
//! syntax and no change to these types (G0, ADR-2026-10-29-2016).

use super::int::Int;

/// An attribute: a word such as `nsw`, an integer, a string, a symbol
/// reference such as `@sum`, or a word applied to attributes, such as
/// `vec(4, i32)`. A word applied to no attributes, `h()`, is not the word `h`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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

    /// The type that this attribute writes, if it is a word or an applied
    /// word.
    pub fn as_type(&self) -> Option<Type> {
        match self {
            Attr::Word(w) => Some(Type::word(w.clone())),
            Attr::App(h, args) => Some(Type::app(h.clone(), args.clone())),
            _ => None,
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

    /// The type as an attribute term.
    pub fn to_attr(&self) -> Attr {
        match &self.args {
            None => Attr::Word(self.name.clone()),
            Some(args) => Attr::App(self.name.clone(), args.clone()),
        }
    }
}
