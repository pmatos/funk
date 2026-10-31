//! Bitwise ops and shifts: `and`, `or`, `xor`, `shl`, `lshr` and `ashr`
//! (`plainBinOps` and `Op.decode` in `lean/Fir/Core/Text.lean`).
//!
//! Each op takes two `iN` and defines one `iN`, and has no attributes: the
//! shifts have no flags, so `shl nuw` does not decode, and neither does
//! `and nsw` or `xor exact`. The second operand of a shift is its amount,
//! read as unsigned; an amount of `N` or more gives poison, not an error,
//! so validation has no rule for these ops beyond their signature
//! (`Op.Valid` in `lean/Fir/Core/Validation.lean`).

use super::arith::bin_width;
use super::type_list;
use crate::registry::{OpShape, OpSpec, OpTypes};

/// The bitwise ops, in the spec's order.
pub const BITWISE_OPS: [&str; 3] = ["and", "or", "xor"];

/// The shifts, in the spec's order.
pub const SHIFT_OPS: [&str; 3] = ["shl", "lshr", "ashr"];

/// `%r: iN = and %a, %b`, and `or`, `xor`, `shl`, `lshr` and `ashr`
/// likewise.
pub(super) struct Bitwise(pub &'static str);

impl OpSpec for Bitwise {
    fn name(&self) -> &str {
        self.0
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        if !op.attrs.is_empty() {
            return Err(format!("{} takes no attributes", self.0));
        }
        match bin_width(op.operands, op.results) {
            Some(_) => Ok(OpShape::default()),
            None => Err(format!(
                "{} takes two operands of one integer type and defines one value of that \
                 type, not {} -> {}",
                self.0,
                type_list(op.operands),
                type_list(op.results)
            )),
        }
    }
}
