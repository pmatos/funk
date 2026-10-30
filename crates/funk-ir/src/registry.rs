//! The op registry: how `funk-ir` checks generic ops and types
//! (G0, ADR-2026-10-29-2016; ADR-2026-10-30-1031).
//!
//! An op is data: a name, attributes, operands, successors, regions and a
//! location. Each dialect registers its ops and its types here, and the
//! parser and the verifier ask the registry what each op and type means. The
//! traits mirror the spec's dialect classes: [`OpSpec::decode`] is
//! `decodeOp` with the op's signature (`DialectText`, `DialectSignature`),
//! [`OpSpec::check`] is `validOp`, and [`TypeSpec`] is `decodeTy` with
//! `validTy` (`DialectValidation`).

use std::collections::HashMap;
use std::fmt;

use crate::dialects;
use crate::ir::names::is_word;
use crate::ir::{Attr, SymbolTable, Type};

/// What an op instance is used at: its attributes and the types of its
/// operands and results. The parser finds the types where the values are
/// defined; the verifier looks them up in the function.
#[derive(Clone, Copy, Debug)]
pub struct OpTypes<'a> {
    /// The op's attributes.
    pub attrs: &'a [Attr],
    /// The types of the op's operands, in order.
    pub operands: &'a [Type],
    /// The types of the op's results, in order.
    pub results: &'a [Type],
}

/// What a decoded op instance says about itself: the rest of its
/// `DialectSignature` and the symbols it refers to.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct OpShape {
    /// Whether the op ends a block.
    pub terminator: bool,
    /// How many successors the op has. Only terminators have any.
    pub successors: usize,
    /// The symbols the op refers to. Each must name an item of the module.
    pub symbols: Vec<String>,
}

/// What a dialect's op rule may look at: the module's symbol table and the
/// enclosing function (`OpContext` in `lean/Fir/Validation/Scope.lean`).
#[derive(Clone, Copy, Debug)]
pub struct OpContext<'a> {
    /// The symbols of the module.
    pub symbols: &'a SymbolTable<'a>,
    /// The symbol of the enclosing function.
    pub func: &'a str,
    /// The result types of the enclosing function.
    pub results: &'a [Type],
}

/// One op of a dialect. An op family's file implements it once per op.
pub trait OpSpec: Send + Sync {
    /// The op's name, such as `add`. It must be a word.
    fn name(&self) -> &str;

    /// Decodes the op instance used at `op`: its shape, or why no instance
    /// of this op has these attributes, operand types and result types. A
    /// text whose op does not decode is a parse error (ADR-2026-10-30-0815).
    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String>;

    /// The dialect's own rule for a decoded op, beyond its signature, such as
    /// "`ret` returns the function's result types". A broken rule is a
    /// validation error.
    fn check(&self, _cx: &OpContext<'_>, _op: &OpTypes<'_>) -> Result<(), String> {
        Ok(())
    }
}

/// What a dialect says about a type it decodes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeCheck {
    /// The type decodes and is valid.
    Valid,
    /// The type decodes, but validation rejects it, as it rejects `i0`.
    Invalid(String),
    /// The type does not decode, as `i16777216` does not: a parse error.
    Malformed(String),
}

/// The types of a dialect. Two dialects must not claim the same type.
pub trait TypeSpec: Send + Sync {
    /// What the dialect says about `ty`, or `None` if `ty` is not one of its
    /// types.
    fn check(&self, ty: &Type) -> Option<TypeCheck>;
}

/// A dialect: a name, its ops and its types.
pub struct Dialect {
    /// The dialect's name.
    pub name: String,
    /// The dialect's ops.
    pub ops: Vec<Box<dyn OpSpec>>,
    /// The dialect's types.
    pub types: Vec<Box<dyn TypeSpec>>,
}

impl Dialect {
    /// A dialect with no ops and no types yet.
    pub fn new(name: impl Into<String>) -> Dialect {
        Dialect {
            name: name.into(),
            ops: Vec::new(),
            types: Vec::new(),
        }
    }

    /// Adds an op.
    pub fn op(mut self, op: impl OpSpec + 'static) -> Dialect {
        self.ops.push(Box::new(op));
        self
    }

    /// Adds a family of types.
    pub fn types(mut self, types: impl TypeSpec + 'static) -> Dialect {
        self.types.push(Box::new(types));
        self
    }
}

/// Why a dialect could not be registered.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RegistryError {
    /// A dialect of this name is already registered.
    DuplicateDialect(String),
    /// An op of this name is already registered.
    DuplicateOp(String),
    /// The op's name is not a word, so the text cannot write it.
    OpNameNotAWord(String),
}

impl fmt::Display for RegistryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RegistryError::DuplicateDialect(d) => write!(f, "dialect {d} is already registered"),
            RegistryError::DuplicateOp(o) => write!(f, "op {o} is already registered"),
            RegistryError::OpNameNotAWord(o) => write!(f, "op name {o:?} is not a word"),
        }
    }
}

impl std::error::Error for RegistryError {}

/// The registered dialects, their ops by name, and their types.
#[derive(Default)]
pub struct Registry {
    dialects: Vec<String>,
    ops: HashMap<String, (usize, Box<dyn OpSpec>)>,
    types: Vec<Box<dyn TypeSpec>>,
}

impl fmt::Debug for Registry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ops: Vec<_> = self.ops.keys().collect();
        ops.sort();
        f.debug_struct("Registry")
            .field("dialects", &self.dialects)
            .field("ops", &ops)
            .finish()
    }
}

impl Registry {
    /// A registry with no dialects.
    pub fn new() -> Registry {
        Registry::default()
    }

    /// A registry with the core dialect.
    pub fn core() -> Registry {
        let mut r = Registry::new();
        r.register(dialects::core::dialect())
            .expect("the core dialect registers");
        r
    }

    /// Registers a dialect, or fails without changing the registry.
    pub fn register(&mut self, dialect: Dialect) -> Result<(), RegistryError> {
        if self.dialects.contains(&dialect.name) {
            return Err(RegistryError::DuplicateDialect(dialect.name));
        }
        let mut names: Vec<&str> = Vec::new();
        for op in &dialect.ops {
            let name = op.name();
            if !is_word(name) {
                return Err(RegistryError::OpNameNotAWord(name.to_string()));
            }
            if self.ops.contains_key(name) || names.contains(&name) {
                return Err(RegistryError::DuplicateOp(name.to_string()));
            }
            names.push(name);
        }
        let index = self.dialects.len();
        self.dialects.push(dialect.name);
        for op in dialect.ops {
            self.ops.insert(op.name().to_string(), (index, op));
        }
        self.types.extend(dialect.types);
        Ok(())
    }

    /// The registered op named `name`.
    pub fn op(&self, name: &str) -> Option<&dyn OpSpec> {
        self.ops.get(name).map(|(_, op)| op.as_ref())
    }

    /// The dialect that registered the op named `name`.
    pub fn dialect_of(&self, name: &str) -> Option<&str> {
        self.ops.get(name).map(|(d, _)| self.dialects[*d].as_str())
    }

    /// What the registered dialects say about `ty`. A type that no dialect
    /// claims does not decode.
    pub fn check_type(&self, ty: &Type) -> TypeCheck {
        self.types
            .iter()
            .find_map(|t| t.check(ty))
            .unwrap_or_else(|| {
                TypeCheck::Malformed(format!("{} is not a type of any registered dialect", ty))
            })
    }
}
