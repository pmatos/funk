//! What a dialect implements: the rules of its ops, its types and its
//! functions, and what each is asked about (`DialectSignature`,
//! `DialectText`, `DialectValidation`, `DialectEffects` and `DialectCall` in
//! `lean/Fir`). [`super::Registry`] routes each op and type to the dialect
//! that registers it.

use crate::effects::Effects;
use crate::ir::{Attr, Func, MemLayout, SymbolTable, Type};

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
    /// text whose op does not decode is a parse error (ADR-2026-10-29-2014).
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

    /// The types that the op instance carries in its attributes `attrs`,
    /// beyond its operand and result types, such as the type that `alloca`
    /// allocates values of (`DialectValidation.opTypes`). The verifier
    /// checks that the data layout declares each memory they name. An op
    /// that carries no type gives none, the default.
    fn attr_types(&self, _attrs: &[crate::Attr]) -> Vec<Type> {
        Vec::new()
    }

    /// The memories whose units the op instance used at `op`, which decodes,
    /// writes values of, each with the width of those values, such as the
    /// fill `memset` (`DialectValidation.opUnits`). The verifier checks that
    /// the data layout gives each memory units of that width. An op that
    /// writes no values into units gives none, the default.
    fn unit_widths(&self, _op: &OpTypes<'_>) -> Vec<(u32, u32)> {
        Vec::new()
    }

    /// Whether [`OpSpec::unit_widths`] may give a pair for some instance, so
    /// that the verifier types the operands of this op's instances to ask
    /// it. An op that writes no values into units gives `false`, the
    /// default, and the verifier skips it.
    fn asks_unit_widths(&self) -> bool {
        false
    }

    /// The memories whose pointers the op instance used at `op`, which
    /// decodes, turns into integers or back, each with the width of the
    /// integer, such as `ptr_expose` (`DialectValidation.opAddrs`). The
    /// verifier checks that the data layout gives each memory pointers of
    /// that width and does not mark it non-integral. An op that turns no
    /// pointer into an integer gives none, the default.
    fn addr_widths(&self, _op: &OpTypes<'_>) -> Vec<(u32, u32)> {
        Vec::new()
    }

    /// Whether [`OpSpec::addr_widths`] may give a pair for some instance, so
    /// that the verifier types the operands of this op's instances to ask
    /// it. An op that turns no pointer into an integer gives `false`, the
    /// default, and the verifier skips it.
    fn asks_addr_widths(&self) -> bool {
        false
    }

    /// The symbol of the function that the op instance used at `op` calls,
    /// or `None` for an op that calls none (`callee?`, `DialectCall`). The
    /// interpreter runs the callee of an op that is not a terminator, and
    /// the op has its callee's effects too, which [`Summaries`] adds
    /// (ADR-2026-11-09-1541).
    ///
    /// [`Summaries`]: crate::Summaries
    fn callee(&self, _op: &OpTypes<'_>) -> Option<String> {
        None
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

    /// The memory that `ty` points into, by its number in the module's
    /// data layout, if `ty` is a pointer type of the dialect
    /// (`DialectValidation.tyMemory`). A dialect without pointer types
    /// names none.
    fn memory(&self, _ty: &Type) -> Option<u32> {
        None
    }

    /// Whether a parameter or result of type `ty`, one of the dialect's
    /// types, may carry the attributes `attrs` after its type in a
    /// function's signature (`DialectValidation.validSigAttrs`). By default
    /// it carries none.
    fn sig_attrs(&self, _ty: &Type, attrs: &[Attr]) -> bool {
        attrs.is_empty()
    }

    /// The units that a value of `ty` takes as a field of an aggregate's
    /// layout in the memory `n`, and its alignment there, in units, where
    /// `entry` gives each memory's layout entry
    /// (`DialectValidation.fieldShape`, ADR-2026-11-16-1546), if `ty` is a
    /// type of the dialect that may be a field. A dialect whose types may
    /// not be fields gives none.
    fn field_shape(
        &self,
        _ty: &Type,
        _entry: &dyn Fn(u64) -> MemLayout,
        _n: u64,
    ) -> Option<(u128, u128)> {
        None
    }
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
