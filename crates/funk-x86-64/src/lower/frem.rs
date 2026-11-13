//! The remainders `frem` and `fmod` (`dialects/core/float_arith.rs` in
//! `funk-ir`), at `f32` and `f64`
//! (`docs/decisions/x86-64-backend-lowering-floats.md#the-remainders`).
//!
//! SSE has no remainder, so each op loads its operands into `%xmm0` and
//! `%xmm1` and calls a routine of the runtime helper `frem.s`, which the
//! module's own object file carries, as `fma`'s does (`farith.rs`). The
//! routines run the x87 unit's `fprem1`, IEEE 754's remainder, for `frem`,
//! and `fprem`, C's `fmod`, for `fmod`; both are exact. A routine clobbers
//! only registers that System V lets a callee clobber, none of which holds
//! a value from one op to the next, and leaves the x87 stack empty.

use funk_ir::Op;
use funk_ir::dialects::core::float_format;

use super::farith::call_routine;
use super::{Cx, Lower, Unlowered};

/// The runtime helper: the routines that do `frem` and `fmod` at `f32` and
/// `f64`, as assembly, which [`super::module`] appends once to a module
/// that calls one.
pub const HELPER: &str = include_str!("frem.s");

/// The bytes of stack that a call of a routine of [`HELPER`] uses below
/// the caller's `%rsp`: its return address and the word it pushes.
pub const HELPER_STACK: u64 = 16;

/// The routine of [`HELPER`] that `op` calls, if it is `frem` or `fmod` at
/// `f32` or `f64`.
pub fn helper(op: &Op) -> Option<&'static str> {
    let [r] = op.results.as_slice() else {
        return None;
    };
    match (op.name.as_str(), float_format(&r.ty)?) {
        ("frem", (8, 23)) => Some("__funk_rt_fremf"),
        ("frem", (11, 52)) => Some("__funk_rt_frem"),
        ("fmod", (8, 23)) => Some("__funk_rt_fmodf"),
        ("fmod", (11, 52)) => Some("__funk_rt_fmod"),
        _ => None,
    }
}

pub(super) fn lowering(name: &str) -> Option<Lower> {
    match name {
        "frem" | "fmod" => Some(remainder),
        _ => None,
    }
}

/// `%r: f64 = frem %a, %b`, and `fmod` likewise: a call of the helper's
/// routine with `%a` in `%xmm0` and `%b` in `%xmm1`.
fn remainder(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    let ([a, b], [r]) = (op.operands.as_slice(), op.results.as_slice()) else {
        return Err(format!("{} takes two operands and defines one value", op.name).into());
    };
    let routine = helper(op).ok_or("frem and fmod at f32 or f64 call the runtime helper")?;
    call_routine(cx, op, routine, &[a.as_str(), b], &r.name)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The helper's code: each line without its comment, trimmed.
    fn code() -> Vec<&'static str> {
        HELPER
            .lines()
            .map(|l| l.split('#').next().unwrap_or_default().trim())
            .collect()
    }

    /// The routines touch no general register but `%rax`, no SSE register
    /// but `%xmm0` and `%xmm1`, push as much as they pop, call nothing, and
    /// leave the x87 stack as they found it: each loads two values and
    /// pops two.
    #[test]
    fn the_helper_touches_only_rax_xmm0_xmm1_and_the_x87_stack() {
        for line in code() {
            for reg in line.split('%').skip(1) {
                let reg: String = reg
                    .chars()
                    .take_while(char::is_ascii_alphanumeric)
                    .collect();
                assert!(
                    ["rax", "ax", "ah", "rsp", "xmm0", "xmm1", "st"].contains(&reg.as_str()),
                    "{line}"
                );
            }
            assert!(!line.starts_with("call"), "{line}");
        }
        let count = |m: &str| code().iter().filter(|l| l.starts_with(m)).count();
        assert_eq!((count("pushq"), count("popq")), (4, 4));
        assert_eq!(count("fld"), 8);
        assert_eq!(count("fstp"), 8);
        assert_eq!(HELPER_STACK, 8 + 8);
    }

    /// Every label is a local `__funk_rt_` symbol, or starts with
    /// `.Lrt_f`, which no block's or function's local label does, and each
    /// routine runs the x87 instruction of its op.
    #[test]
    fn each_routine_is_its_op_s_and_its_labels_stay_apart() {
        let lines = code();
        let labels: Vec<&str> = lines.iter().filter_map(|l| l.strip_suffix(':')).collect();
        for label in &labels {
            assert!(
                label.starts_with("__funk_rt_") || label.starts_with(".Lrt_f"),
                "{label}"
            );
            assert_ne!(crate::abi::symbol(label), *label);
        }
        assert!(!lines.iter().any(|l| l.contains(".globl")));
        for (routine, ins) in [
            ("__funk_rt_fremf", "fprem1"),
            ("__funk_rt_frem", "fprem1"),
            ("__funk_rt_fmodf", "fprem"),
            ("__funk_rt_fmod", "fprem"),
        ] {
            let start = lines
                .iter()
                .position(|l| *l == format!("{routine}:"))
                .unwrap();
            let end = start + lines[start..].iter().position(|l| *l == "ret").unwrap();
            let body = &lines[start..end];
            assert_eq!(body.iter().filter(|l| l.starts_with("fprem")).count(), 1);
            assert!(body.contains(&ins), "{routine}");
        }
    }
}
