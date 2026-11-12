//! The core dialect: the small, CPU-shaped dialect of M0
//! (`lean/Fir/Core/`).
//!
//! Its types are the integers `iN`, the floats `float<e,m>` and the pointers
//! `ptr<N>`. Each op family lives in a file of its own and registers its ops in
//! [`dialect`]: the tracer registers `const`, `add` and `ret`, the arithmetic
//! family (#14) `sub`, `mul`, the flags of all three and `freeze`, the
//! bitwise family (#15) `and`, `or`, `xor`, `shl`, `lshr` and `ashr`, the
//! width changes (#17) `zext`, `sext` and `trunc`, the division family (#18)
//! `sdiv`, `udiv`, `srem`, `urem` and the flag `exact`, the comparison
//! family (#16) `icmp` with its predicates and `select`, the branches (#19)
//! `br` and `cond_br`, and the calls (#20) `call`. #122 adds the constant
//! `poison` beside `const`, and #228 the terminator `unreachable` beside
//! `ret`. #229 adds float constants to `const`, the float comparison
//! `fcmp`, and the float arithmetic `fadd`, `fsub`, `fmul`, `fdiv`, `fneg`,
//! `fabs`, `sqrt` and `fma`. #241 adds the bit cast `bitcast` between a
//! float and an integer of its width. A later family adds a file and a
//! line here.

mod arith;
mod bitcast;
mod bitwise;
mod call;
mod compare;
mod constant;
mod control;
mod div;
mod float_arith;
mod float_text;
mod freeze;
mod types;
mod width;

pub use arith::WRAP_FLAG_SETS;
pub use bitwise::{BITWISE_OPS, SHIFT_OPS};
pub use compare::{FLOAT_PREDICATES, PREDICATES};
pub use div::DIVISION_OPS;
pub use float_arith::FLOAT_ARITH_OPS;
pub use float_text::{float_constant, has_decimals, read_float, spell_float};
pub use types::{
    CoreType, FLOAT_ALIASES, MAX_MEMORY, MAX_WIDTH, core_type, float_format, float_type, int_type,
    int_width, ptr_type,
};
pub use width::WIDTH_CHANGES;

use crate::registry::Dialect;

/// The core dialect's name.
pub const NAME: &str = "core";

/// The core dialect, ready to register.
pub fn dialect() -> Dialect {
    let core = Dialect::new(NAME)
        .types(types::CoreTypes)
        .op(constant::Const)
        .op(arith::Wrap("add"))
        .op(arith::Wrap("sub"))
        .op(arith::Wrap("mul"))
        .op(freeze::Freeze)
        .op(constant::Poison)
        .op(bitwise::Bitwise("and"))
        .op(bitwise::Bitwise("or"))
        .op(bitwise::Bitwise("xor"))
        .op(bitwise::Bitwise("shl"))
        .op(bitwise::Bitwise("lshr"))
        .op(bitwise::Bitwise("ashr"))
        .op(width::Cast("zext"))
        .op(width::Cast("sext"))
        .op(width::Cast("trunc"))
        .op(div::Division("sdiv", true))
        .op(div::Division("udiv", true))
        .op(div::Division("srem", false))
        .op(div::Division("urem", false))
        .op(compare::Icmp)
        .op(compare::Fcmp)
        .op(compare::Select)
        .op(control::Br)
        .op(control::CondBr)
        .op(control::Ret)
        .op(control::Unreachable)
        .op(call::Call)
        .op(bitcast::Bitcast);
    float_arith::FloatArith::all().fold(core, Dialect::op)
}

/// Writes a list of types as `(t1, t2)`, for messages.
fn type_list(tys: &[crate::Type]) -> String {
    format!("({})", crate::text::Commas(tys))
}
