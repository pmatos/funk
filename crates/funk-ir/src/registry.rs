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
//! [`OpSpec::effects`] is `effects` (`DialectEffects`) and
//! [`OpSpec::callee`] is `callee?` (`DialectCall`).
//!
//! A word belongs to the dialect named before its first `.`, and a bare word
//! to the core (ADR-2026-11-09-1543, ADR-2026-10-30-1146). Registration
//! checks that each op of a dialect is written under the dialect's name, so
//! the map of op names routes each op to its dialect. A type goes to the
//! dialect that its head word names, and only that dialect's [`TypeSpec`]s
//! are asked about it, so no dialect can claim another's type. A region kind
//! is registered under its dialect's name as an op is, and a
//! [`RegionKindSpec`] is the kind's rule, `validRegion`. A kind of item is
//! registered the same way, and an [`ItemKindSpec`] is its rule,
//! `validItem` (ADR-2026-11-09-1543).

mod error;
mod item_kind;
mod region_kind;
mod spec;

use std::collections::HashMap;
use std::fmt;

pub use error::RegistryError;
pub use item_kind::{ItemKindError, ItemKindSpec};
pub use region_kind::RegionKindSpec;
pub use spec::{FuncContext, FuncSpec, OpContext, OpShape, OpSpec, OpTypes, TypeCheck, TypeSpec};

use crate::dialects;
use crate::dialects::core::NAME as CORE;
use crate::effects::Effects;
use crate::ir::names::{is_word, word_dialect};
use crate::ir::{MemLayout, Type};

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

/// Why a kind's word cannot be registered, for region kinds and kinds of
/// item alike.
enum KindFault<'a> {
    NotAWord(&'a str),
    OutsideDialect(&'a str),
    Duplicate(&'a str),
}

/// Checks the words `kinds` of a dialect whose words are written under
/// `prefix`, `None` for the core: each is a word of the dialect, never the
/// core's, and none repeats one before it or one that `known` says is
/// registered.
fn check_kind_words<'a>(
    kinds: impl Iterator<Item = &'a str>,
    prefix: Option<&str>,
    known: impl Fn(&str) -> bool,
) -> Result<(), KindFault<'a>> {
    let mut seen: Vec<&str> = Vec::new();
    for kind in kinds {
        if !is_word(kind) {
            return Err(KindFault::NotAWord(kind));
        }
        if prefix.is_none() || !written_under(kind, prefix) {
            return Err(KindFault::OutsideDialect(kind));
        }
        if known(kind) || seen.contains(&kind) {
            return Err(KindFault::Duplicate(kind));
        }
        seen.push(kind);
    }
    Ok(())
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
        let region_kinds = dialect.region_kinds.iter().map(|k| k.name());
        check_kind_words(region_kinds, prefix, |k| self.kinds.contains_key(k)).map_err(
            |f| match f {
                KindFault::NotAWord(k) => RegistryError::KindNotAWord(k.to_string()),
                KindFault::OutsideDialect(k) => RegistryError::KindOutsideDialect {
                    dialect: dialect.name.clone(),
                    kind: k.to_string(),
                },
                KindFault::Duplicate(k) => RegistryError::DuplicateKind(k.to_string()),
            },
        )?;
        let item_kinds = dialect.item_kinds.iter().map(|k| k.name());
        check_kind_words(item_kinds, prefix, |k| self.item_kinds.contains_key(k)).map_err(|f| {
            RegistryError::ItemKind(match f {
                KindFault::NotAWord(k) => ItemKindError::NotAWord(k.to_string()),
                KindFault::OutsideDialect(k) => ItemKindError::OutsideDialect {
                    dialect: dialect.name.clone(),
                    kind: k.to_string(),
                },
                KindFault::Duplicate(k) => ItemKindError::Duplicate(k.to_string()),
            })
        })?;
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

    /// The names of the registered ops whose specs ask the width of an
    /// integer that they turn pointers into ([`OpSpec::asks_addr_widths`]).
    pub(crate) fn ops_asking_addr_widths(&self) -> Vec<&str> {
        self.ops
            .iter()
            .filter(|(_, (_, op))| op.asks_addr_widths())
            .map(|(name, _)| name.as_str())
            .collect()
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

    /// The memory that `ty` points into, as the dialect that its head word
    /// names says, if it names one.
    pub fn type_memory(&self, ty: &Type) -> Option<u32> {
        let name = word_dialect(&ty.name).unwrap_or(CORE);
        self.dialect(name)?.types.iter().find_map(|t| t.memory(ty))
    }

    /// The units and the alignment of a field of type `ty` in the memory
    /// `n`, as the dialect that its head word names says, if it may be a
    /// field.
    pub fn field_shape(
        &self,
        ty: &Type,
        entry: &dyn Fn(u64) -> MemLayout,
        n: u64,
    ) -> Option<(u128, u128)> {
        let name = word_dialect(&ty.name).unwrap_or(CORE);
        self.dialect(name)?
            .types
            .iter()
            .find_map(|t| t.field_shape(ty, entry, n))
    }
}
