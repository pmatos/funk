//! Poison control: `freeze` (`Op.decode` in `lean/Fir/Core/Text.lean`).
//!
//! `freeze` takes one `iN` and defines one `iN` of the same width, with no
//! attributes. It gives its operand unchanged when that is not poison, and
//! otherwise an arbitrary value chosen once, so every use of its result
//! sees the same bits (ADR-2026-10-29-2006, ADR-2026-10-29-2017).

use super::type_list;
use super::types::int_width;
use crate::registry::{OpShape, OpSpec, OpTypes};

/// `%f: iN = freeze %x`.
pub(super) struct Freeze;

impl OpSpec for Freeze {
    fn name(&self) -> &str {
        "freeze"
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        if !op.attrs.is_empty() {
            return Err("freeze takes no attributes".into());
        }
        let same_width = match (op.operands, op.results) {
            ([x], [r]) => int_width(x).is_some_and(|w| int_width(r) == Some(w)),
            _ => false,
        };
        if same_width {
            return Ok(OpShape::default());
        }
        Err(format!(
            "freeze takes one operand of an integer type and defines one value of that \
             type, not {} -> {}",
            type_list(op.operands),
            type_list(op.results)
        ))
    }
}
