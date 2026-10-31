//! Control flow: `br`, `cond_br` and `ret` (`dialects/core/control.rs` in
//! `funk-ir`).
//!
//! A branch copies the values its successor passes into the slots of that
//! block's arguments, as one parallel move (ADR-2026-10-31-0335), then
//! jumps to the block's label, unless the block comes next
//! (ADR-2026-10-31-0334). `cond_br` tests bit 0 of its condition, and
//! nothing above it (ADR-2026-10-30-1231), before either successor's moves.
//! Native code holds no poison (ADR-2026-10-30-2248): a branch on poison is
//! UB in the source, and here it goes one way or the other.
//!
//! `ret` puts its value, if it has one, in the result register, then
//! returns (ADR-2026-10-30-1232). An `i1` result is returned as 0 or 1 in
//! all of `%rax`. That is more than C gives for a `_Bool` result, which
//! defines only bits 0 to 7, so code that calls C may rely only on `%al`.
//! A function with more than one result needs a convention for the others,
//! which #31 decides; until then the backend reports it at the `ret`.

use funk_ir::{Op, Succ};

use super::moves::{Src, Step, sequence};
use super::{Cx, Lower, Unlowered};
use crate::abi::RESULT_REG;
use crate::asm::{Mem, Reg};
use crate::frame;
use crate::width::{self, Ext};

pub(super) fn lowering(name: &str) -> Option<Lower> {
    match name {
        "br" => Some(br),
        "cond_br" => Some(cond_br),
        "ret" => Some(ret),
        _ => None,
    }
}

/// `br ^b(%x, %y)`.
fn br(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    let [s] = op.succs.as_slice() else {
        return Err("br has one successor".into());
    };
    let steps = moves(cx, s)?;
    edge(cx, s, &steps, true);
    Ok(())
}

/// `cond_br %c, ^t(%x), ^e(%y)`. After the test, a conditional jump goes
/// to one edge, the first, and the other edge's code follows it. An edge
/// with nothing to move needs no code of its own, so the jump goes straight
/// to its block. Otherwise the first edge's code goes after the other's, at
/// a local label. Only the code that ends the branch may fall through into
/// the next block, so the edges are ordered to let the one whose block
/// comes next end it.
fn cond_br(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    let ([c], [t, e]) = (op.operands.as_slice(), op.succs.as_slice()) else {
        return Err("cond_br has one condition and two successors".into());
    };
    cx.width(c)?;
    let (t_steps, e_steps) = (moves(cx, t)?, moves(cx, e)?);
    let then_first = match (t_steps.is_empty(), e_steps.is_empty()) {
        (true, false) => true,
        (false, true) => false,
        (true, true) => !cx.falls_through(&t.label),
        (false, false) => cx.falls_through(&t.label),
    };
    let ((first, first_steps, jump), (last, last_steps)) = if then_first {
        ((t, t_steps, "jnz"), (e, e_steps))
    } else {
        ((e, e_steps, "jz"), (t, t_steps))
    };
    cx.load(Reg::Rax, c)?;
    cx.asm.ins("testb", format_args!("$1, {}", Reg::Rax.at(8)));
    if first_steps.is_empty() {
        let label = cx.block_label(&first.label);
        cx.asm.ins(jump, format_args!("{label}"));
        edge(cx, last, &last_steps, true);
    } else {
        let local = cx.local_label();
        cx.asm.ins(jump, format_args!("{local}"));
        edge(cx, last, &last_steps, false);
        cx.asm.label(&local);
        edge(cx, first, &first_steps, true);
    }
    Ok(())
}

/// The steps that copy what `s` passes into the slots of its block's
/// arguments.
fn moves(cx: &Cx<'_>, s: &Succ) -> Result<Vec<Step<Mem>>, Unlowered> {
    let params = cx.block_params(&s.label)?;
    if params.len() != s.args.len() {
        return Err(format!(
            "^{} takes {} arguments, and the branch passes {}",
            s.label,
            params.len(),
            s.args.len()
        )
        .into());
    }
    let mut pairs = Vec::with_capacity(params.len());
    for (p, a) in params.iter().zip(&s.args) {
        cx.width(&p.name)?;
        cx.width(a)?;
        pairs.push((cx.slot(&p.name)?, cx.slot(a)?));
    }
    Ok(sequence(&pairs))
}

/// The steps of the edge to `s`, then the jump to its block, unless the
/// edge ends the branch (`ends`) and that block comes next. The moves go
/// through `%rax`, and a cycle of them through `%rcx`.
fn edge(cx: &mut Cx<'_>, s: &Succ, steps: &[Step<Mem>], ends: bool) {
    let (rax, rcx) = (Reg::Rax.q(), Reg::Rcx.q());
    for step in steps {
        match *step {
            Step::Save(d) => cx.asm.ins("movq", format_args!("{d}, {rcx}")),
            Step::Copy(Src::Temp, d) => cx.asm.ins("movq", format_args!("{rcx}, {d}")),
            Step::Copy(Src::At(from), d) => {
                cx.asm.ins("movq", format_args!("{from}, {rax}"));
                cx.asm.ins("movq", format_args!("{rax}, {d}"));
            }
        }
    }
    if !(ends && cx.falls_through(&s.label)) {
        let label = cx.block_label(&s.label);
        cx.asm.ins("jmp", format_args!("{label}"));
    }
}

/// `ret %a`, or `ret` with no value.
fn ret(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    match op.operands.as_slice() {
        [] => {}
        [v] => {
            let w = cx.width(v)?;
            cx.load(RESULT_REG, v)?;
            if w == 1 {
                width::extend(&mut cx.asm, Ext::Zero, 1, RESULT_REG);
            }
        }
        vs => {
            return Err(format!(
                "ret returns {} values: the x86-64 backend returns at most one value \
                 so far",
                vs.len()
            )
            .into());
        }
    }
    frame::epilogue(&mut cx.asm);
    Ok(())
}
