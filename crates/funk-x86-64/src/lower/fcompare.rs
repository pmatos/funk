//! Float comparison: `fcmp` (`dialects/core/compare.rs` in `funk-ir`), at
//! `f32` and `f64`
//! (`docs/decisions/x86-64-backend-abi.md#floats-in-sse-registers`).
//!
//! `movss` or `movsd` loads each operand from its slot into `%xmm0` and
//! `%xmm1`, and one `ucomiss` or `ucomisd` compares them. It sets the flags
//! as an unsigned integer comparison would, `ZF` for equal and `CF` for
//! below, and sets all three of `ZF`, `PF` and `CF` when the pair is
//! unordered, so when either operand is a NaN, whatever its payload or
//! sign. `-0` and `+0` compare equal. Each predicate then reads the flags
//! with one `setCC` into `%al`, or two joined with `andb` or `orb`:
//!
//! * `ogt` and `oge` are `seta` and `setae` of `%a` against `%b`, false on
//!   an unordered pair; `olt` and `ole` are the same with the operands
//!   swapped.
//! * `ult` and `ule` are `setb` and `setbe`, true on an unordered pair;
//!   `ugt` and `uge` are the same with the operands swapped.
//! * `ueq` is `sete` and `one` is `setne`, since an unordered pair sets
//!   `ZF`. `oeq` needs `ZF` set and `PF` clear, so it is `sete` and
//!   `setnp`; `une` is `setne` or `setpe`.
//! * `ord` is `setnp`, and `uno` is `setpe`.
//!
//! `%rax` is stored. Bit 0 of the slot is the `i1`, and the bits above it
//! are unspecified, as for `icmp`. `fcmp` is never UB, and native code holds
//! no poison (ADR-2026-10-30-2248). The comparison raises no exception that
//! a program sees: M1 has no floating-point exceptions.

use funk_ir::{Attr, Op};

use super::{Cx, Lower, Unlowered};
use crate::asm::Reg;
use crate::width::Class;

pub(super) fn lowering(name: &str) -> Option<Lower> {
    match name {
        "fcmp" => Some(fcmp),
        _ => None,
    }
}

/// How `fcmp` tests a predicate: whether it swaps its operands, and the
/// `setCC`s whose results it joins, with the join, after `ucomis %b, %a`.
fn predicate(p: &str) -> Option<(bool, &'static [&'static str], &'static str)> {
    Some(match p {
        "oeq" => (false, &["sete", "setnp"], "andb"),
        "one" => (false, &["setne"], ""),
        "olt" => (true, &["seta"], ""),
        "ole" => (true, &["setae"], ""),
        "ogt" => (false, &["seta"], ""),
        "oge" => (false, &["setae"], ""),
        "ord" => (false, &["setnp"], ""),
        "ueq" => (false, &["sete"], ""),
        "une" => (false, &["setne", "setpe"], "orb"),
        "ult" => (false, &["setb"], ""),
        "ule" => (false, &["setbe"], ""),
        "ugt" => (true, &["setb"], ""),
        "uge" => (true, &["setbe"], ""),
        "uno" => (false, &["setpe"], ""),
        _ => return None,
    })
}

/// `%r: i1 = fcmp p %a, %b`: whether `p` holds of `%a` and `%b`.
fn fcmp(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    let ([a, b], [r]) = (op.operands.as_slice(), op.results.as_slice()) else {
        return Err("fcmp takes two operands and defines one value".into());
    };
    let p = match op.attrs.as_slice() {
        [Attr::Word(p)] => p.as_str(),
        _ => return Err("fcmp has one attribute, its predicate".into()),
    };
    let Some((swap, sets, join)) = predicate(p) else {
        return Err(format!("fcmp has no predicate {p}").into());
    };
    cx.width(&r.name)?;
    if cx.class(a)? != Class::Sse {
        return Err("fcmp compares floats".into());
    }
    let (mov, ucomis) = match cx.width(a)? {
        32 => ("movss", "ucomiss"),
        64 => ("movsd", "ucomisd"),
        w => return Err(format!("fcmp compares f32 or f64, not a value of {w} bits").into()),
    };
    let (sa, sb) = (cx.slot(a)?, cx.slot(b)?);
    cx.asm.ins(mov, format_args!("{sa}, %xmm0"));
    cx.asm.ins(mov, format_args!("{sb}, %xmm1"));
    if swap {
        cx.asm.ins(ucomis, format_args!("%xmm0, %xmm1"));
    } else {
        cx.asm.ins(ucomis, format_args!("%xmm1, %xmm0"));
    }
    let regs = [Reg::Rax, Reg::Rcx];
    for (set, reg) in sets.iter().zip(regs) {
        cx.asm.ins(set, format_args!("{}", reg.at(8)));
    }
    if sets.len() == 2 {
        cx.asm
            .ins(join, format_args!("{}, {}", Reg::Rcx.at(8), Reg::Rax.at(8)));
    }
    cx.store(&r.name, Reg::Rax)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Each predicate, read off the flags of `ucomis` on how `%a` and `%b`
    /// compare, holds exactly as its name says. `ZF`, `PF` and `CF` are set
    /// as the instruction sets them for the operands in the order compared.
    #[test]
    fn each_predicate_reads_the_flags_it_needs() {
        use std::cmp::Ordering::{self, *};
        let flags = |c: Option<Ordering>| match c {
            None => (true, true, true),
            Some(Less) => (false, false, true),
            Some(Equal) => (true, false, false),
            Some(Greater) => (false, false, false),
        };
        let set = |cc: &str, (zf, pf, cf): (bool, bool, bool)| match cc {
            "sete" => zf,
            "setne" => !zf,
            "setpe" => pf,
            "setnp" => !pf,
            "setb" => cf,
            "setbe" => cf || zf,
            "seta" => !cf && !zf,
            "setae" => !cf,
            _ => panic!("{cc}"),
        };
        let want = |p: &str, c: Option<Ordering>| match (p, c) {
            ("ord", c) => c.is_some(),
            ("uno", c) => c.is_none(),
            (p, None) => p.starts_with('u'),
            (p, Some(o)) => match &p[1..] {
                "eq" => o == Equal,
                "ne" => o != Equal,
                "lt" => o == Less,
                "le" => o != Greater,
                "gt" => o == Greater,
                "ge" => o != Less,
                _ => panic!("{p}"),
            },
        };
        for p in funk_ir::dialects::core::FLOAT_PREDICATES {
            let (swap, sets, join) = predicate(p).unwrap();
            for c in [None, Some(Less), Some(Equal), Some(Greater)] {
                let seen = if swap { c.map(Ordering::reverse) } else { c };
                let bits: Vec<bool> = sets.iter().map(|cc| set(cc, flags(seen))).collect();
                let got = match join {
                    "andb" => bits.iter().all(|&b| b),
                    "orb" => bits.iter().any(|&b| b),
                    _ => bits[0],
                };
                assert_eq!(got, want(p, c), "{p} on {c:?}");
            }
        }
    }
}
