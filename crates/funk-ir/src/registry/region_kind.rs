//! Region kinds that a dialect registers (ADR-2026-11-10-1941): the
//! `regionKindNames` and `validRegion` of `DialectValidation` in
//! `lean/Fir/Validation/Scope.lean`.
//!
//! A region names its kind by a word of a dialect, such as `toy.graph`, and
//! no kind is the core's control-flow graph, whose rule is the rule of a
//! function's body. An op instance states the kinds of the regions it owns,
//! in its [`OpShape`](super::OpShape), and the verifier checks each region
//! against the rule of its kind. Registration puts each kind under its
//! dialect's prefix, as it does each op, so one map of kind names routes a
//! kind to the dialect that registers it (ADR-2026-10-30-1146).

use super::FuncContext;
use crate::ir::{Func, Region};

/// A region kind of a dialect, and its rule: how values are scoped in a
/// region of the kind, which of its ops end its blocks, and where its
/// successors go. The general rules of an op, its types, symbols, its
/// dialect's own rule and its location, hold for every op inside the
/// region whatever its kind.
pub trait RegionKindSpec: Send + Sync {
    /// The kind's word, such as `toy.graph`: the dialect's name, a `.` and
    /// a word, as an op of the dialect is written.
    fn name(&self) -> &str;

    /// The kind's rule for `region`, a region of this kind owned by an op of
    /// `func`, or why the region breaks it. The verifier calls it on every
    /// region of the kind, also in a function that breaks other rules, so
    /// it must hold no assumption about the region or the function.
    fn check(&self, cx: &FuncContext<'_>, func: &Func, region: &Region) -> Result<(), String>;
}
