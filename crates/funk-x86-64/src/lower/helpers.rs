//! The runtime helpers that ops call
//! (`docs/decisions/x86-64-backend-lowering.md#division-at-i128`).
//!
//! A helper is assembly that the module's own object file carries: each of
//! its routines is a local `__funk_rt_` symbol, which no fir function's
//! symbol is, so it clashes with nothing, the host's C library included.
//! The module's text ends with each helper that one of its ops calls, once.

use funk_ir::Op;

use super::{div, farith, frem, memops};
use crate::asm::Asm;

/// A runtime helper: the routine of it that an op calls, if any, its code,
/// and the bytes of stack that a call of one of its routines uses below
/// the caller's `%rsp`.
type Helper = (fn(&Op) -> Option<&'static str>, &'static str, u64);

/// Every runtime helper: the one that divides at `i128`, the one that
/// does `fma` at `f32` and `f64`, the one that does `frem` and `fmod`
/// there, and funk's own `memcpy`, `memmove` and `memset`.
const HELPERS: [Helper; 4] = [
    (div::helper, div::HELPER, div::HELPER_STACK),
    (farith::helper, farith::HELPER, farith::HELPER_STACK),
    (frem::helper, frem::HELPER, frem::HELPER_STACK),
    (memops::helper, memops::HELPER, memops::HELPER_STACK),
];

/// Which helpers a function or module calls, in `HELPERS` order.
pub type Used = [bool; HELPERS.len()];

/// The most stack that a call of a routine of any runtime helper uses
/// below the caller's `%rsp`.
pub const STACK: u64 = {
    let (mut i, mut most) = (0, 0);
    while i < HELPERS.len() {
        if HELPERS[i].2 > most {
            most = HELPERS[i].2;
        }
        i += 1;
    }
    most
};

/// Marks in `used` each helper whose routine `op` calls, and says whether
/// there is one.
pub fn mark(op: &Op, used: &mut Used) -> bool {
    let mut any = false;
    for ((routine, _, _), used) in HELPERS.iter().zip(used.iter_mut()) {
        if routine(op).is_some() {
            *used = true;
            any = true;
        }
    }
    any
}

/// Appends to `asm` the code of each helper in `used`.
pub fn append(asm: &mut Asm, used: &Used) {
    for ((_, code, _), used) in HELPERS.iter().zip(used) {
        if *used {
            asm.raw(code);
        }
    }
}
