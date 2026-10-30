//! Integer arithmetic: `add` (`Op.decode` in `lean/Fir/Core/Text.lean`).
//!
//! `add` takes two `iN` and defines one `iN`. The tracer registers it without
//! flags; the arithmetic family adds `nuw` and `nsw`, with `sub` and `mul`.

use super::type_list;
use super::types::int_width;
use crate::Type;
use crate::registry::{OpShape, OpSpec, OpTypes};

/// The width `N` of an op that takes two `iN` and defines one `iN`
/// (`binWidth`).
fn bin_width(operands: &[Type], results: &[Type]) -> Option<u32> {
    let [a, b] = operands else { return None };
    let [r] = results else { return None };
    let w = int_width(a)?;
    (int_width(b)? == w && int_width(r)? == w).then_some(w)
}

/// `%s: iN = add %a, %b`.
pub(super) struct Add;

impl OpSpec for Add {
    fn name(&self) -> &str {
        "add"
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        if !op.attrs.is_empty() {
            return Err("add takes no attributes: its flags are not registered yet".into());
        }
        match bin_width(op.operands, op.results) {
            Some(_) => Ok(OpShape::default()),
            None => Err(format!(
                "add takes two operands of one integer type and defines one value of that \
                 type, not {} -> {}",
                type_list(op.operands),
                type_list(op.results)
            )),
        }
    }
}
