//! Why a dialect could not be registered: each check of
//! [`Registry::register`](super::Registry::register) that fails.

use std::fmt;

use super::CORE;
use super::item_kind::ItemKindError;

/// Why a dialect could not be registered.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RegistryError {
    /// The dialect's name is not a word with no `.`, so no word can name it.
    DialectNameNotAPrefix(String),
    /// A dialect of this name is already registered.
    DuplicateDialect(String),
    /// The dialect depends on one that is not registered.
    MissingDependency {
        /// The dialect being registered.
        dialect: String,
        /// The dependency that no registered dialect has as its name.
        dependency: String,
    },
    /// The op's name does not name the dialect that registers it: a
    /// prefixed dialect's ops are `name.word`, and the core's are bare.
    OpOutsideDialect {
        /// The dialect being registered.
        dialect: String,
        /// The op's name.
        op: String,
    },
    /// An op of this name is already registered.
    DuplicateOp(String),
    /// The op's name is not a word, so the text cannot write it.
    OpNameNotAWord(String),
    /// The region kind is not a word.
    KindNotAWord(String),
    /// The region kind does not name the dialect that registers it: a
    /// dialect's kinds are `name.word`, and the core registers none, since
    /// its own kind is the control-flow graph of a function's body.
    KindOutsideDialect {
        /// The dialect being registered.
        dialect: String,
        /// The kind's word.
        kind: String,
    },
    /// A region kind of this name is already registered.
    DuplicateKind(String),
    /// A kind of item that the dialect registers is not a word of the
    /// dialect, or is already registered.
    ItemKind(ItemKindError),
}

impl fmt::Display for RegistryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RegistryError::DialectNameNotAPrefix(d) => {
                write!(f, "dialect name {d:?} is not a word without a dot")
            }
            RegistryError::DuplicateDialect(d) => write!(f, "dialect {d} is already registered"),
            RegistryError::MissingDependency {
                dialect,
                dependency,
            } => write!(
                f,
                "dialect {dialect} depends on {dependency}, which is not registered"
            ),
            RegistryError::OpOutsideDialect { dialect, op } if dialect == CORE => {
                write!(f, "op {op} of the core is not a bare word")
            }
            RegistryError::OpOutsideDialect { dialect, op } => {
                write!(
                    f,
                    "op {op} of dialect {dialect} is not written {dialect}.WORD"
                )
            }
            RegistryError::DuplicateOp(o) => write!(f, "op {o} is already registered"),
            RegistryError::OpNameNotAWord(o) => write!(f, "op name {o:?} is not a word"),
            RegistryError::KindNotAWord(k) => write!(f, "region kind {k:?} is not a word"),
            RegistryError::KindOutsideDialect { dialect, kind } => write!(
                f,
                "region kind {kind} of dialect {dialect} is not written {dialect}.WORD"
            ),
            RegistryError::DuplicateKind(k) => write!(f, "region kind {k} is already registered"),
            RegistryError::ItemKind(e) => e.fmt(f),
        }
    }
}

impl std::error::Error for RegistryError {}
