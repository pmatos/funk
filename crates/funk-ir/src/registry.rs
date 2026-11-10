//! The op registry: how `funk-ir` checks generic ops and types
//! (G0, ADR-2026-10-29-2016; ADR-2026-10-30-1146).
//!
//! An op is data: a name, attributes, operands, successors, regions and a
//! location. Each dialect registers its ops and its types here, and the
//! parser and the verifier ask the registry what each op and type means. The
//! traits mirror the spec's dialect classes: [`OpSpec::decode`] is
//! `decodeOp` with the op's signature (`DialectText`, `DialectSignature`),
//! [`OpSpec::check`] is `validOp`, [`TypeSpec`] is `decodeTy` with `validTy`,
//! and [`FuncSpec::check`] is `validFunc` (`DialectValidation`).
//!
//! A word belongs to the dialect named before its first `.`, and a bare word
//! to the core (ADR-2026-11-09-1543, ADR-2026-11-10-0042). Registration
//! checks that each op of a dialect is written under the dialect's name, so
//! the map of op names routes each op to its dialect. A type goes to the
//! dialect that its head word names, and only that dialect's [`TypeSpec`]s
//! are asked about it, so no dialect can claim another's type.

use std::collections::HashMap;
use std::fmt;

use crate::dialects;
use crate::dialects::core::NAME as CORE;
use crate::ir::names::{is_word, word_dialect};
use crate::ir::{Attr, Func, SymbolTable, Type};

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
    /// The op's name, such as `add` or `toy.br`: a bare word for the core,
    /// and the dialect's name, a `.` and a word for any other dialect.
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

/// The types of a dialect. The registry asks it only about types whose head
/// word names its dialect: `name.word` for a dialect `name`, and a bare word
/// for the core. So a spec of `toy` that claims `f32` is never asked.
pub trait TypeSpec: Send + Sync {
    /// What the dialect says about `ty`, or `None` if `ty` is not one of its
    /// types.
    fn check(&self, ty: &Type) -> Option<TypeCheck>;
}

/// What a dialect's function rule may look at beside the function: the
/// module's symbol table (`FuncContext` in `lean/Fir/Validation/Scope.lean`).
#[derive(Clone, Copy, Debug)]
pub struct FuncContext<'a> {
    /// The symbols of the module.
    pub symbols: &'a SymbolTable<'a>,
}

/// A dialect's own rule over a whole function, for what no op can see
/// alone, such as a value that must be used exactly once. A function holds
/// every dialect's ops as data, so the rule sees the uses by all of them.
pub trait FuncSpec: Send + Sync {
    /// The rule, or why `func` breaks it. The verifier calls it on every
    /// function, also on one that breaks other rules, so it must hold no
    /// assumption about the function.
    fn check(&self, cx: &FuncContext<'_>, func: &Func) -> Result<(), String>;
}

/// A dialect: a name, the dialects it depends on, its ops, its types and its
/// function rules.
pub struct Dialect {
    /// The dialect's name: a word with no `.`. Every dialect but the core
    /// writes its ops and types as this name, a `.` and a word; the core
    /// writes bare words.
    pub name: String,
    /// The names of the dialects it depends on, whose types its ops may
    /// take. Each must be registered before it.
    pub deps: Vec<String>,
    /// The dialect's ops.
    pub ops: Vec<Box<dyn OpSpec>>,
    /// The dialect's types.
    pub types: Vec<Box<dyn TypeSpec>>,
    /// The dialect's rules over whole functions.
    pub func_rules: Vec<Box<dyn FuncSpec>>,
}

impl Dialect {
    /// A dialect with no dependencies, ops, types or function rules yet.
    pub fn new(name: impl Into<String>) -> Dialect {
        Dialect {
            name: name.into(),
            deps: Vec::new(),
            ops: Vec::new(),
            types: Vec::new(),
            func_rules: Vec::new(),
        }
    }

    /// Adds a dialect that this one depends on.
    /// A dependency named twice is kept once.
    pub fn depends_on(mut self, dialect: impl Into<String>) -> Dialect {
        let dialect = dialect.into();
        if !self.deps.contains(&dialect) {
            self.deps.push(dialect);
        }
        self
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

    /// Adds a rule over whole functions.
    pub fn func_rule(mut self, rule: impl FuncSpec + 'static) -> Dialect {
        self.func_rules.push(Box::new(rule));
        self
    }
}

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
        }
    }
}

impl std::error::Error for RegistryError {}

/// Whether `op` is written under `prefix`: a bare word for the core, whose
/// prefix is `None`, and the prefix, a `.` and a word for any other dialect.
fn written_under(op: &str, prefix: Option<&str>) -> bool {
    match prefix {
        None => word_dialect(op).is_none(),
        Some(p) => op
            .strip_prefix(p)
            .and_then(|rest| rest.strip_prefix('.'))
            .is_some_and(is_word),
    }
}

/// A registered dialect: its name, its dependencies and its types.
struct Registered {
    name: String,
    deps: Vec<String>,
    types: Vec<Box<dyn TypeSpec>>,
}

/// The registered dialects, their ops by name, their types and their
/// function rules.
#[derive(Default)]
pub struct Registry {
    dialects: Vec<Registered>,
    ops: HashMap<String, (usize, Box<dyn OpSpec>)>,
    func_rules: Vec<Box<dyn FuncSpec>>,
}

impl fmt::Debug for Registry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let dialects: Vec<_> = self.dialects.iter().map(|d| &d.name).collect();
        let mut ops: Vec<_> = self.ops.keys().collect();
        ops.sort();
        f.debug_struct("Registry")
            .field("dialects", &dialects)
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

    /// The registered dialect named `name`.
    fn dialect(&self, name: &str) -> Option<&Registered> {
        self.dialects.iter().find(|d| d.name == name)
    }

    /// Registers a dialect, or fails without changing the registry. Its name
    /// must be new and a word with no `.`, each dialect it depends on must
    /// be registered, and each op must be a new word that names it.
    pub fn register(&mut self, dialect: Dialect) -> Result<(), RegistryError> {
        let name = dialect.name.as_str();
        if !is_word(name) || name.contains('.') {
            return Err(RegistryError::DialectNameNotAPrefix(dialect.name));
        }
        if self.dialect(name).is_some() {
            return Err(RegistryError::DuplicateDialect(dialect.name));
        }
        if let Some(dep) = dialect.deps.iter().find(|d| self.dialect(d).is_none()) {
            return Err(RegistryError::MissingDependency {
                dialect: dialect.name.clone(),
                dependency: dep.clone(),
            });
        }
        let prefix = (name != CORE).then_some(name);
        let mut names: Vec<&str> = Vec::new();
        for op in &dialect.ops {
            let op_name = op.name();
            if !is_word(op_name) {
                return Err(RegistryError::OpNameNotAWord(op_name.to_string()));
            }
            if !written_under(op_name, prefix) {
                return Err(RegistryError::OpOutsideDialect {
                    dialect: dialect.name.clone(),
                    op: op_name.to_string(),
                });
            }
            if self.ops.contains_key(op_name) || names.contains(&op_name) {
                return Err(RegistryError::DuplicateOp(op_name.to_string()));
            }
            names.push(op_name);
        }
        let index = self.dialects.len();
        for op in dialect.ops {
            self.ops.insert(op.name().to_string(), (index, op));
        }
        self.func_rules.extend(dialect.func_rules);
        self.dialects.push(Registered {
            name: dialect.name,
            deps: dialect.deps,
            types: dialect.types,
        });
        Ok(())
    }

    /// The registered op named `name`.
    pub fn op(&self, name: &str) -> Option<&dyn OpSpec> {
        self.ops.get(name).map(|(_, op)| op.as_ref())
    }

    /// The dialect that registered the op named `name`.
    pub fn dialect_of(&self, name: &str) -> Option<&str> {
        self.ops
            .get(name)
            .map(|(d, _)| self.dialects[*d].name.as_str())
    }

    /// The dialects that the registered dialect `name` depends on.
    pub fn dependencies(&self, name: &str) -> Option<&[String]> {
        self.dialect(name).map(|d| d.deps.as_slice())
    }

    /// The registered dialects' rules over whole functions.
    pub fn func_rules(&self) -> impl Iterator<Item = &dyn FuncSpec> {
        self.func_rules.iter().map(|r| r.as_ref())
    }

    /// What the dialect that `ty`'s head word names says about `ty`. A type
    /// that its dialect does not claim, or whose dialect is not registered,
    /// does not decode.
    pub fn check_type(&self, ty: &Type) -> TypeCheck {
        let name = word_dialect(&ty.name).unwrap_or(CORE);
        let Some(d) = self.dialect(name) else {
            return TypeCheck::Malformed(format!(
                "{ty} is not a type: no dialect named {name} is registered"
            ));
        };
        d.types
            .iter()
            .find_map(|t| t.check(ty))
            .unwrap_or_else(|| TypeCheck::Malformed(format!("{ty} is not a type of {name}")))
    }
}
