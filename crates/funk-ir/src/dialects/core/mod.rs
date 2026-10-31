//! The core dialect: the small, CPU-shaped dialect of M0
//! (`lean/Fir/Core/`).
//!
//! Its types are the integers `iN` and the reserved `ptr`. Each op family
//! lives in a file of its own and registers its ops in [`dialect`]: the
//! tracer registers `const`, `add` and `ret`, the arithmetic family (#14)
//! `sub`, `mul`, the flags of all three and `freeze`, the bitwise family
//! (#15) `and`, `or`, `xor`, `shl`, `lshr` and `ashr`, and each later family
//! adds a file and a line here.

mod arith;
mod bitwise;
mod constant;
mod control;
mod freeze;
mod types;

pub use arith::WRAP_FLAG_SETS;
pub use bitwise::{BITWISE_OPS, SHIFT_OPS};
pub use types::{CoreType, MAX_WIDTH, core_type, int_type, int_width};

use crate::registry::Dialect;

/// The core dialect's name.
pub const NAME: &str = "core";

/// The core dialect, ready to register.
pub fn dialect() -> Dialect {
    Dialect::new(NAME)
        .types(types::CoreTypes)
        .op(constant::Const)
        .op(arith::Wrap("add"))
        .op(arith::Wrap("sub"))
        .op(arith::Wrap("mul"))
        .op(freeze::Freeze)
        .op(bitwise::Bitwise("and"))
        .op(bitwise::Bitwise("or"))
        .op(bitwise::Bitwise("xor"))
        .op(bitwise::Bitwise("shl"))
        .op(bitwise::Bitwise("lshr"))
        .op(bitwise::Bitwise("ashr"))
        .op(control::Ret)
}

/// Writes a list of types as `(t1, t2)`, for messages.
fn type_list(tys: &[crate::Type]) -> String {
    format!("({})", crate::text::Commas(tys))
}
