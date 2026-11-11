//! Kinds of item that a dialect registers (ADR-2026-11-10-2224): the
//! `itemKindNames` and `validItem` of `DialectValidation`, in
//! `lean/Fir/Validation/Scope.lean`.
//!
//! A kind is a word of its dialect, `name.word`, as an op of the dialect is,
//! and the core registers none: its kinds, `func` and `module`, are items
//! of their own. The parser decodes an item of any word of a dialect, so a
//! new kind needs no parser change, and the verifier asks the kind's
//! [`ItemKindSpec`] whether the item obeys the dialect's rule for it.

use std::fmt;

use super::FuncContext;
use crate::ir::DialectItem;

/// A kind of item and its rule.
pub trait ItemKindSpec: Send + Sync {
    /// The kind's word, such as `toy.cell`: the dialect's name, a `.` and a
    /// word.
    fn name(&self) -> &str;

    /// The dialect's rule for an item of this kind, or why `item` breaks
    /// it: what its parameters, results and attributes must be. The
    /// verifier calls it on every item of the kind, also on one that breaks
    /// the general rules, so it must hold no assumption about the item.
    fn check(&self, cx: &FuncContext<'_>, item: &DialectItem) -> Result<(), String>;
}

/// Why a dialect's kinds of item could not be registered.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ItemKindError {
    /// The kind is not a word, so the text cannot write it.
    NotAWord(String),
    /// The kind does not name the dialect that registers it: a dialect's
    /// kinds are `name.word`, and the core registers none.
    OutsideDialect {
        /// The dialect being registered.
        dialect: String,
        /// The kind's word.
        kind: String,
    },
    /// A kind of item of this name is already registered.
    Duplicate(String),
}

impl fmt::Display for ItemKindError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ItemKindError::NotAWord(k) => write!(f, "kind of item {k:?} is not a word"),
            ItemKindError::OutsideDialect { dialect, kind } => write!(
                f,
                "kind of item {kind} of dialect {dialect} is not written {dialect}.WORD"
            ),
            ItemKindError::Duplicate(k) => write!(f, "kind of item {k} is already registered"),
        }
    }
}
