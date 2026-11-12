//! Lowering a module's functions to assembly
//! (`docs/decisions/x86-64-backend.md#frames-and-slots`).
//!
//! Each op family of the core dialect has a file of its own here, as in
//! `funk-ir`'s `dialects/core/`, and lowers its ops by name. A later family
//! adds a file and one line to [`lowering`]. The driver below checks the
//! width of every value where it is defined, and reports, as a
//! [`Diagnostic`] at the op or block, each width and each op that the
//! backend cannot lower: all of them, in one pass.
//!
//! Blocks are laid out in the order of the function's body, each at its own
//! label, and a branch jumps to its successor's label unless that block
//! comes next (`docs/decisions/x86-64-backend-lowering.md#branches`). A
//! branch copies the values it passes into its successor's arguments as one
//! parallel move (`moves.rs`,
//! `docs/decisions/x86-64-backend-lowering.md#block-arguments`). A call
//! follows System V, with no extension of its arguments (`call.rs`,
//! `docs/decisions/x86-64-backend-abi.md#calls-between-funk-functions`).
//! `ret` and `call` place and read any number of results as `abi::results`
//! lays them out (ADR-2026-10-30-1232).
//!
//! An `i128` is a pair of eightbytes in two slots, and each op lowers it
//! through a pair of registers, `%rax` for its low half and `%rdx` for its
//! high one unless the op says otherwise
//! (`docs/decisions/x86-64-backend-lowering.md#lowering-i128`). Division at
//! `i128` calls a routine of a runtime helper, as `fma` at `f32` and `f64`
//! does, and the module's text then ends with each helper that it calls,
//! once (`div.rs`, `farith.rs`,
//! `docs/decisions/x86-64-backend-lowering.md#division-at-i128`).
//!
//! An `f32` or `f64` is its bits in one slot. A float constant writes them
//! as an integer immediate, as any constant does, and `fcmp` loads its
//! operands into SSE registers (`fcompare.rs`), as the float arithmetic
//! does, but for `fneg` and `fabs`, which change the sign bit in `%rax`,
//! and `fma`, `frem` and `fmod`, which call routines of runtime helpers of
//! their own (`farith.rs`, `frem.rs`,
//! `docs/decisions/x86-64-backend-lowering.md#float-arithmetic`). Floats
//! pass and return in SSE registers
//! (`docs/decisions/x86-64-backend-abi.md#floats-in-sse-registers`). A
//! bit cast copies a slot (`bitcast.rs`).

mod arith;
mod bitcast;
mod bitwise;
mod call;
mod cast;
mod compare;
mod constant;
mod control;
mod div;
mod farith;
mod fcompare;
mod freeze;
mod frem;
mod moves;

use std::collections::HashMap;

use funk_ir::text::{print_op, print_symbol};
use funk_ir::{Block, Def, Diagnostic, Func, Module, Op};

pub use call::callee;

use crate::abi::{self, Arg, symbol};
use crate::asm::{Asm, Mem, NO_EXEC_STACK, Reg};
use crate::frame::{self, Frame};
use crate::width;

/// A runtime helper: the routine of it that an op calls, if any, its code,
/// and the bytes of stack that a call of one of its routines uses below
/// the caller's `%rsp`.
type Helper = (fn(&Op) -> Option<&'static str>, &'static str, u64);

/// Every runtime helper: the one that divides at `i128`, the one that
/// does `fma` at `f32` and `f64`, and the one that does `frem` and `fmod`
/// there.
const HELPERS: [Helper; 3] = [
    (div::helper, div::HELPER, div::HELPER_STACK),
    (farith::helper, farith::HELPER, farith::HELPER_STACK),
    (frem::helper, frem::HELPER, frem::HELPER_STACK),
];

/// The most stack that a call of a routine of any runtime helper uses
/// below the caller's `%rsp`.
pub const HELPER_STACK: u64 = {
    let (mut i, mut most) = (0, 0);
    while i < HELPERS.len() {
        if HELPERS[i].2 > most {
            most = HELPERS[i].2;
        }
        i += 1;
    }
    most
};

/// The routine of a runtime helper that `op` calls, if any: a division at
/// `i128`, or `fma`, `frem` or `fmod` at `f32` or `f64`. Each routine needs at most
/// [`HELPER_STACK`] bytes of stack below its caller's `%rsp`.
pub fn helper(op: &Op) -> Option<&'static str> {
    HELPERS.iter().find_map(|(routine, _, _)| routine(op))
}

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
    /// The class of each value defined so far: how it passes to and from a
    /// function.
    classes: HashMap<&'f str, width::Class>,
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

    /// The class of the value `name`, one that the backend lowers: SSE for
    /// a float, a pair for an `i128`, and one INTEGER eightbyte otherwise.
    pub fn class(&self, name: &str) -> Result<width::Class, Unlowered> {
        self.width(name)?;
        Ok(self.classes.get(name).copied().unwrap_or(width::Class::Int))
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

    /// Loads the `i128` value `name` from its two slots: its low half into
    /// `lo` and its high half into `hi`.
    pub fn load_pair(&mut self, lo: Reg, hi: Reg, name: &str) -> Result<(), Unlowered> {
        let slot = self.slot(name)?;
        self.asm.ins("movq", format_args!("{slot}, {}", lo.q()));
        self.asm
            .ins("movq", format_args!("{}, {}", slot.high(), hi.q()));
        Ok(())
    }

    /// The slots of each eightbyte of the value `name`, its low half first:
    /// one, or two for an `i128`.
    pub fn eightbytes(&self, name: &str) -> Result<Vec<Mem>, Unlowered> {
        let slot = self.slot(name)?;
        if self.width(name)? == width::PAIR {
            Ok(vec![slot, slot.high()])
        } else {
            Ok(vec![slot])
        }
    }

    /// Stores `lo` and `hi` into the two slots of the `i128` value `name`,
    /// as its low half and its high half.
    pub fn store_pair(&mut self, name: &str, lo: Reg, hi: Reg) -> Result<(), Unlowered> {
        let slot = self.slot(name)?;
        self.asm.ins("movq", format_args!("{}, {slot}", lo.q()));
        self.asm
            .ins("movq", format_args!("{}, {}", hi.q(), slot.high()));
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
            let (w, class) = width::lowered(&d.ty);
            if let Err(why) = &w {
                out.push(format!("%{}: {why}", d.name));
            }
            self.widths.insert(d.name.as_str(), w.ok());
            self.classes.insert(d.name.as_str(), class);
        }
        out
    }
}

/// Whether the first result of `op` is an `i128`, so that the op lowers
/// through register pairs. An op with no result is lowered by its own
/// rule, which reports its shape.
pub fn is_pair(cx: &Cx<'_>, op: &Op) -> Result<bool, Unlowered> {
    match op.results.first() {
        Some(r) => Ok(cx.width(&r.name)? == width::PAIR),
        None => Ok(false),
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
        .or_else(|| fcompare::lowering(name))
        .or_else(|| farith::lowering(name))
        .or_else(|| frem::lowering(name))
        .or_else(|| control::lowering(name))
        .or_else(|| call::lowering(name))
        .or_else(|| bitcast::lowering(name))
}

/// A module's functions, lowered.
pub struct Lowered {
    /// The assembly of every function.
    pub text: String,
    /// The size of each function's frame below `%rbp`, in order.
    pub frames: Vec<i32>,
}

/// The assembly of every function of `m`, followed by each runtime helper
/// whose routine a function calls, or a diagnostic for each part that the
/// backend cannot lower. `m` must be valid.
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
    let ops = || m.funcs().flat_map(|f| &f.body.blocks).flat_map(|b| &b.ops);
    for (routine, code, _) in HELPERS {
        if ops().any(|op| routine(op).is_some()) {
            asm.raw(code);
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
        classes: HashMap::new(),
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
    // The address of the function's result area, when its results go in
    // memory, arrives first, as an argument of one eightbyte, and its
    // parameters after it (ADR-2026-10-30-1232).
    let mut incoming = Vec::with_capacity(f.params.len());
    for d in &f.params {
        let Some(slot) = cx.frame.slot(&d.name) else {
            out.push(at(
                f,
                entry,
                None,
                format!("parameter %{} has no slot", d.name),
            ));
            return None;
        };
        incoming.push(Arg {
            slot,
            class: width::class(&d.ty),
        });
    }
    if let Err(i) = abi::receive(&mut cx.asm, &incoming, cx.frame.results_address()) {
        let why = format!(
            "parameter %{} is out of the reach of %rbp",
            f.params[i].name
        );
        out.push(at(f, entry, None, why));
        return None;
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
