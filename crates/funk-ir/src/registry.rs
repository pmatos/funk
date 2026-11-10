//! The op registry: how `funk-ir` checks generic ops and types
//! (G0, ADR-2026-10-29-2016; ADR-2026-10-30-1146).
//!
//! An op is data: a name, attributes, operands, successors, regions and a
//! location. Each dialect registers its ops and its types here, and the
//! parser and the verifier ask the registry what each op and type means. The
//! traits mirror the spec's dialect classes: [`OpSpec::decode`] is
//! `decodeOp` with the op's signature (`DialectText`, `DialectSignature`),
//! [`OpSpec::check`] is `validOp`, [`TypeSpec`] is `decodeTy` with `validTy`,
//! [`FuncSpec::check`] is `validFunc` (`DialectValidation`), and
//! [`OpSpec::effects`] is `effects` (`DialectEffects`).
//!
//! A word belongs to the dialect named before its first `.`, and a bare word
//! to the core (ADR-2026-11-09-1543, ADR-2026-11-10-0042). Registration
//! checks that each op of a dialect is written under the dialect's name, so
//! the map of op names routes each op to its dialect. A type goes to the
//! dialect that its head word names, and only that dialect's [`TypeSpec`]s
//! are asked about it, so no dialect can claim another's type. A region kind
//! is registered under its dialect's name as an op is, and a
//! [`RegionKindSpec`] is the kind's rule, `validRegion`. A kind of item is
//! registered the same way, and an [`ItemKindSpec`] is its rule,
//! `validItem` (ADR-2026-11-10-2224).

mod error;
mod item_kind;
mod region_kind;

use std::collections::HashMap;
use std::fmt;

pub use error::RegistryError;
pub use item_kind::{ItemKindError, ItemKindSpec};
pub use region_kind::RegionKindSpec;

use crate::dialects;
use crate::dialects::core::NAME as CORE;
use crate::effects::Effects;
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
    /// The kind of each region that the op owns, in order: each a region
    /// kind of a dialect, never the core's (`regionKinds`). Empty for an op
    /// that owns no region.
    pub regions: Vec<String>,
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

    /// The effects of the op instance used at `op`, which decodes: those of
    /// its own rule (ADR-2026-11-09-1541). An op with a callee has its
    /// callee's effects too, which this set leaves out. Every op declares
    /// its set, so the method has no default, as `Core.Op.effects` has no
    /// case for the rest. An op without `control` is not a terminator: its
    /// [`OpShape::terminator`] is false, as Lean's `notControl` proves.
    fn effects(&self, op: &OpTypes<'_>) -> Effects;
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

/// A dialect: a name, the dialects it depends on, its ops, its types, its
/// function rules, its region kinds and its kinds of item.
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
    /// The region kinds that the dialect registers, each with its rule.
    pub region_kinds: Vec<Box<dyn RegionKindSpec>>,
    /// The kinds of item that the dialect registers, each with its rule.
    pub item_kinds: Vec<Box<dyn ItemKindSpec>>,
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
            region_kinds: Vec::new(),
            item_kinds: Vec::new(),
        }
    }

    /// Adds a dialect that this one depends on, unless it is already there.
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

    /// Adds a region kind and its rule.
    pub fn region_kind(mut self, kind: impl RegionKindSpec + 'static) -> Dialect {
        self.region_kinds.push(Box::new(kind));
        self
    }

    /// Adds a kind of item and its rule.
    pub fn item_kind(mut self, kind: impl ItemKindSpec + 'static) -> Dialect {
        self.item_kinds.push(Box::new(kind));
        self
    }
}

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

/// The registered dialects, their ops by name, their types, their function
/// rules, their region kinds by name and their kinds of item by name.
#[derive(Default)]
pub struct Registry {
    dialects: Vec<Registered>,
    ops: HashMap<String, (usize, Box<dyn OpSpec>)>,
    func_rules: Vec<Box<dyn FuncSpec>>,
    kinds: HashMap<String, Box<dyn RegionKindSpec>>,
    item_kinds: HashMap<String, Box<dyn ItemKindSpec>>,
}

impl fmt::Debug for Registry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let dialects: Vec<_> = self.dialects.iter().map(|d| &d.name).collect();
        let mut ops: Vec<_> = self.ops.keys().collect();
        ops.sort();
        let mut kinds: Vec<_> = self.kinds.keys().collect();
        kinds.sort();
        let mut item_kinds: Vec<_> = self.item_kinds.keys().collect();
        item_kinds.sort();
        f.debug_struct("Registry")
            .field("dialects", &dialects)
            .field("ops", &ops)
            .field("kinds", &kinds)
            .field("item_kinds", &item_kinds)
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
    /// be registered, each op must be a new word that names it, and each
    /// region kind and each kind of item a new word `name.word` of a dialect
    /// other than the core, which registers neither.
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
        let mut kinds: Vec<&str> = Vec::new();
        for kind in &dialect.region_kinds {
            let kind = kind.name();
            if !is_word(kind) {
                return Err(RegistryError::KindNotAWord(kind.to_string()));
            }
            if prefix.is_none() || !written_under(kind, prefix) {
                return Err(RegistryError::KindOutsideDialect {
                    dialect: dialect.name.clone(),
                    kind: kind.to_string(),
                });
            }
            if self.kinds.contains_key(kind) || kinds.contains(&kind) {
                return Err(RegistryError::DuplicateKind(kind.to_string()));
            }
            kinds.push(kind);
        }
        item_kind::check_kinds(name, prefix, &dialect.item_kinds, |k| {
            self.item_kinds.contains_key(k)
        })
        .map_err(RegistryError::ItemKind)?;
        let index = self.dialects.len();
        for op in dialect.ops {
            self.ops.insert(op.name().to_string(), (index, op));
        }
        self.func_rules.extend(dialect.func_rules);
        for kind in dialect.region_kinds {
            self.kinds.insert(kind.name().to_string(), kind);
        }
        for kind in dialect.item_kinds {
            self.item_kinds.insert(kind.name().to_string(), kind);
        }
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

    /// The effects of the op named `name` at `op`, as the dialect that its
    /// word names declares them, or `None` if no dialect registered it. An
    /// op of a sum has its own side's effects in Lean (the sum's
    /// `DialectEffects`), and the prefix routes it to that side here. Lean
    /// keeps each side's memories apart in the sum; no registered dialect
    /// has a memory yet, so how Rust keeps them apart lands with the first
    /// one.
    pub fn effects(&self, name: &str, op: &OpTypes<'_>) -> Option<Effects> {
        self.op(name).map(|spec| spec.effects(op))
    }

    /// The dialect that registered the op named `name`.
    pub fn dialect_of(&self, name: &str) -> Option<&str> {
        self.ops
            .get(name)
            .map(|(d, _)| self.dialects[*d].name.as_str())
    }

    /// Whether a module's dialect set may name `name`: a registered dialect
    /// other than the core, which every module holds and none names.
    pub fn is_extension(&self, name: &str) -> bool {
        name != CORE && self.dialect(name).is_some()
    }

    /// The dialects that the registered dialect `name` depends on.
    pub fn dependencies(&self, name: &str) -> Option<&[String]> {
        self.dialect(name).map(|d| d.deps.as_slice())
    }

    /// The registered region kind named `name`, with its rule.
    pub fn region_kind(&self, name: &str) -> Option<&dyn RegionKindSpec> {
        self.kinds.get(name).map(|k| k.as_ref())
    }

    /// The registered kind of item named `name`, with its rule.
    pub fn item_kind(&self, name: &str) -> Option<&dyn ItemKindSpec> {
        self.item_kinds.get(name).map(|k| k.as_ref())
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
