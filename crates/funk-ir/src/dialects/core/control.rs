//! Control flow: `ret` (`lean/Fir/Core/Ops.lean`, `Op.Valid` in
//! `lean/Fir/Core/Validation.lean`).
//!
//! `ret` ends a block and returns its operands: any number of values of core
//! types, none included (ADR-2026-10-30-0816). It returns the function's
//! result types, which validation checks.

use super::type_list;
use super::types::core_type;
use crate::registry::{OpContext, OpShape, OpSpec, OpTypes};

/// `ret %a, %b`.
pub(super) struct Ret;

impl OpSpec for Ret {
    fn name(&self) -> &str {
        "ret"
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        if !op.attrs.is_empty() {
            return Err("ret takes no attributes".into());
        }
        if !op.results.is_empty() {
            return Err("ret defines no values".into());
        }
        if let Some(t) = op.operands.iter().find(|t| core_type(t).is_none()) {
            return Err(format!("ret returns values of core types, not {t}"));
        }
        Ok(OpShape {
            terminator: true,
            ..OpShape::default()
        })
    }

    fn check(&self, cx: &OpContext<'_>, op: &OpTypes<'_>) -> Result<(), String> {
        if op.operands == cx.results {
            return Ok(());
        }
        Err(format!(
            "ret returns {} but the function returns {}",
            type_list(op.operands),
            type_list(cx.results)
        ))
    }
}
