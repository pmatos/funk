//! Lowering a module's functions to assembly (ADR-2026-10-30-1230).
//!
//! Each op family of the core dialect has a file of its own here, as in
//! `funk-ir`'s `dialects/core/`, and lowers its ops by name. A later family
//! adds a file and one line to [`lowering`]. The driver below checks the
//! width of every value where it is defined, and reports, as a
//! [`Diagnostic`] at the op or block, each width and each op that the
//! backend cannot lower: all of them, in one pass.
//!
//! Blocks are laid out in the order of the function's body, each at its
//! own label, and a branch jumps to its successor's label unless that
//! block comes next (ADR-2026-10-31-0334). A branch copies the values it
//! passes into its successor's arguments as one parallel move (`moves.rs`,
//! ADR-2026-10-31-0335).

mod arith;
mod bitwise;
mod cast;
mod compare;
mod constant;
mod control;
mod div;
mod freeze;
mod moves;

use std::collections::HashMap;

use funk_ir::text::{print_op, print_symbol};
use funk_ir::{Block, Def, Diagnostic, Func, Module, Op};

use crate::abi::{ARG_REGS, stack_arg_offset, symbol};
use crate::asm::{Asm, Mem, NO_EXEC_STACK, Reg};
use crate::frame::{self, Frame};
use crate::width;

/// Why an op was not lowered.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Unlowered {
    /// A value it uses or defines has a width that the backend does not
    /// lower, which is already reported where the value is defined.
    Reported,
    /// Why, for a diagnostic at the op.
    Why(String),
}

impl From<String> for Unlowered {
    fn from(why: String) -> Unlowered {
        Unlowered::Why(why)
    }
}

impl From<&str> for Unlowered {
    fn from(why: &str) -> Unlowered {
        Unlowered::Why(why.to_string())
    }
}

/// What an op's lowering sees of its function, and where it writes.
pub struct Cx<'f> {
    /// The function's code so far.
    pub asm: Asm,
    frame: Frame<'f>,
    /// The width of each value defined so far; `None` when the backend does
    /// not lower it.
    widths: HashMap<&'f str, Option<u32>>,
    /// The index of the function in its module, which its labels hold.
    func: usize,
    /// The arguments of each block, by label.
    params: HashMap<&'f str, &'f [Def]>,
    /// The label of the block after the one being lowered, if any.
    next: Option<&'f str>,
    /// How many local labels the function has made so far.
    locals: usize,
}

impl<'f> Cx<'f> {
    /// The width of the value `name`, one of the supported widths. A
    /// lowering looks a value's width up before it relies on it.
    pub fn width(&self, name: &str) -> Result<u32, Unlowered> {
        match self.widths.get(name) {
            Some(Some(w)) => Ok(*w),
            Some(None) => Err(Unlowered::Reported),
            None => Err(format!("%{name} is not defined").into()),
        }
    }

    /// The slot of the value `name`.
    pub fn slot(&self, name: &str) -> Result<Mem, Unlowered> {
        self.frame
            .slot(name)
            .ok_or_else(|| format!("%{name} is not defined").into())
    }

    /// Loads the value `name` from its slot into `reg`.
    pub fn load(&mut self, reg: Reg, name: &str) -> Result<(), Unlowered> {
        let slot = self.slot(name)?;
        self.asm.ins("movq", format_args!("{slot}, {}", reg.q()));
        Ok(())
    }

    /// Stores `reg` into the slot of the value `name`.
    pub fn store(&mut self, name: &str, reg: Reg) -> Result<(), Unlowered> {
        let slot = self.slot(name)?;
        self.asm.ins("movq", format_args!("{}, {slot}", reg.q()));
        Ok(())
    }

    /// The arguments of the block labelled `label`.
    pub fn block_params(&self, label: &str) -> Result<&'f [Def], Unlowered> {
        self.params
            .get(label)
            .copied()
            .ok_or_else(|| format!("^{label} is not a block of the function").into())
    }

    /// The assembly label of the block labelled `label`.
    pub fn block_label(&self, label: &str) -> String {
        block_label(self.func, label)
    }

    /// Whether the block labelled `label` comes right after the one being
    /// lowered, so that its code follows with no jump.
    pub fn falls_through(&self, label: &str) -> bool {
        self.next == Some(label)
    }

    /// A new local label of the function, `.Lc` with the function's index
    /// and a count, which no block label can be.
    pub fn local_label(&mut self) -> String {
        self.locals += 1;
        format!(".Lc{}_{}", self.func, self.locals)
    }

    /// Records the width of each of `defs`, and returns why the backend does
    /// not lower each one it does not.
    fn define(&mut self, defs: &'f [Def]) -> Vec<String> {
        let mut out = Vec::new();
        for d in defs {
            let w = width::check(&d.ty);
            if let Err(why) = &w {
                out.push(format!("%{}: {why}", d.name));
            }
            self.widths.insert(d.name.as_str(), w.ok());
        }
        out
    }
}

/// How one op is lowered: its code goes to `cx.asm`, or why not.
pub type Lower = fn(&mut Cx<'_>, &Op) -> Result<(), Unlowered>;

/// The lowering of the op named `name`, if the backend has one.
fn lowering(name: &str) -> Option<Lower> {
    constant::lowering(name)
        .or_else(|| arith::lowering(name))
        .or_else(|| freeze::lowering(name))
        .or_else(|| bitwise::lowering(name))
        .or_else(|| cast::lowering(name))
        .or_else(|| div::lowering(name))
        .or_else(|| compare::lowering(name))
        .or_else(|| control::lowering(name))
}

/// A module's functions, lowered.
pub struct Lowered {
    /// The assembly of every function.
    pub text: String,
    /// The size of each function's frame below `%rbp`, in order.
    pub frames: Vec<i32>,
}

/// The assembly of every function of `m`, or a diagnostic for each part
/// that the backend cannot lower. `m` must be valid.
pub fn module(m: &Module) -> Result<Lowered, Vec<Diagnostic>> {
    let mut asm = Asm::new();
    let mut out = Vec::new();
    let mut frames = Vec::new();
    asm.directive(format_args!(".text"));
    for (i, f) in m.funcs().enumerate() {
        if let Some((code, size)) = func(i, f, &mut out) {
            asm.raw(&code);
            frames.push(size);
        }
    }
    asm.raw(NO_EXEC_STACK);
    if out.is_empty() {
        Ok(Lowered {
            text: asm.finish(),
            frames,
        })
    } else {
        Err(out)
    }
}

/// A diagnostic about `f`: at its block `block`, or at the op `op` of it,
/// located as the verifier locates its own.
pub fn at(f: &Func, block: Option<&Block>, op: Option<usize>, message: String) -> Diagnostic {
    match (block, op) {
        (Some(b), Some(i)) => Diagnostic::at_op(&f.name, b, i, message),
        _ => Diagnostic::at_block(&f.name, block, message),
    }
}

/// The local label of block `label` of the `i`-th function.
pub fn block_label(i: usize, label: &str) -> String {
    format!(".Lb{i}_{label}")
}

/// The code of the `i`-th function, `f`, and the size of its frame, or
/// `None` when it has a part that the backend cannot lower, which goes to
/// `out`.
fn func(i: usize, f: &Func, out: &mut Vec<Diagnostic>) -> Option<(String, i32)> {
    let entry = f.body.blocks.first();
    let before = out.len();
    let frame = Frame::new(f)
        .map_err(|why| out.push(at(f, entry, None, why)))
        .ok()?;
    let mut cx = Cx {
        asm: Asm::new(),
        frame,
        widths: HashMap::new(),
        func: i,
        params: HashMap::new(),
        next: None,
        locals: 0,
    };
    for b in &f.body.blocks {
        cx.params.entry(b.label.as_str()).or_insert(&b.params);
    }
    // Every width is known before any op is lowered, since a block may use a
    // value that a block after it in the list defines.
    for why in cx.define(&f.params) {
        out.push(at(f, entry, None, format!("parameter {why}")));
    }
    for b in &f.body.blocks {
        for why in cx.define(&b.params) {
            out.push(at(f, Some(b), None, format!("block argument {why}")));
        }
        for (n, op) in b.ops.iter().enumerate() {
            for why in cx.define(&op.results) {
                out.push(at(f, Some(b), Some(n), why));
            }
        }
    }
    let sym = symbol(&f.name);
    cx.asm.comment(format_args!("{}", print_symbol(&f.name)));
    cx.asm.directive(format_args!(".globl\t{sym}"));
    cx.asm.directive(format_args!(".type\t{sym}, @function"));
    cx.asm.directive(format_args!(".p2align\t4"));
    cx.asm.label(&sym);
    frame::prologue(&mut cx.asm, cx.frame.size());
    for (n, d) in f.params.iter().enumerate() {
        let Some(slot) = cx.frame.slot(&d.name) else {
            out.push(at(
                f,
                entry,
                None,
                format!("parameter %{} has no slot", d.name),
            ));
            return None;
        };
        if let Some(reg) = ARG_REGS.get(n) {
            cx.asm.ins("movq", format_args!("{}, {slot}", reg.q()));
        } else {
            let Some(disp) = stack_arg_offset(n) else {
                let why = format!("parameter %{} is out of the reach of %rbp", d.name);
                out.push(at(f, entry, None, why));
                return None;
            };
            let from = Mem { disp };
            cx.asm.ins("movq", format_args!("{from}, %rax"));
            cx.asm.ins("movq", format_args!("%rax, {slot}"));
        }
    }
    for (k, b) in f.body.blocks.iter().enumerate() {
        cx.next = f.body.blocks.get(k + 1).map(|n| n.label.as_str());
        block(i, f, &mut cx, b, out);
    }
    cx.asm.directive(format_args!(".size\t{sym}, .-{sym}"));
    let size = cx.frame.size();
    (out.len() == before).then(|| (cx.asm.finish(), size))
}

fn block(i: usize, f: &Func, cx: &mut Cx<'_>, b: &Block, out: &mut Vec<Diagnostic>) {
    cx.asm.label(&block_label(i, &b.label));
    for (n, op) in b.ops.iter().enumerate() {
        let Some(lower) = lowering(&op.name) else {
            let why = format!("the x86-64 backend cannot lower the op {} yet", op.name);
            out.push(at(f, Some(b), Some(n), why));
            continue;
        };
        let text = print_op(op, 0);
        let line = text.lines().next().unwrap_or_default().trim();
        cx.asm.comment(format_args!("{line}"));
        if let Err(Unlowered::Why(why)) = lower(cx, op) {
            out.push(at(f, Some(b), Some(n), why));
        }
    }
}
