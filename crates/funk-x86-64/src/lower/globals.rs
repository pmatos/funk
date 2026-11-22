//! Globals and their addresses: the data of a module's globals and
//! `globaladdr` (`dialects/core/global_addr.rs` in `funk-ir`;
//! `docs/decisions/x86-64-backend-lowering-memory.md#globals`).
//!
//! Each global of the module's own table is a symbol of the object file,
//! as a function is, with `abi::symbol`'s spelling: global when the global
//! is `export`, local otherwise. A constant global goes to `.rodata`, so a
//! store to it faults, a global whose initializer gives only zeros to
//! `.bss`, and any other to `.data`, aligned to its alignment. Its
//! initializer's units are bytes, an `addr(@g, K)` piece is the relocation
//! `.quad g+K`, whose addend wraps at 64 bits as `ptradd` does, and the
//! units past the initializer are zeros (#237 Q1). A nested module's
//! globals are left out with its functions.
//!
//! `globaladdr @g` is `leaq g(%rip)`. Validation makes `@g` a global of the
//! op's own table, of the result's memory, and the driver reports the
//! result where it is defined unless the backend realises that memory, so
//! every global that an op names is placed here.
//!
//! A global of a memory that the backend does not realise is reported at
//! the global, as is one that holds a pointer of such a memory. The small
//! code model that `leaq` and calls relative to `%rip` assume keeps code
//! and data within 2 GiB, so the globals, each with its alignment's
//! padding, take at most 2^30 bytes, and the global past that is reported.
//!
//! A module with globals also gets the table `__funk_globals`, from which
//! the runtime reports each global's address and units when the
//! executable runs with `--memory`
//! (`docs/decisions/x86-64-backend-executable.md#reporting-memory`). It
//! is in the module's file because a global that is not `export` is a
//! local symbol there. It is a hidden global symbol, and the entry file
//! refers to it weakly, so a module without globals defines no data and
//! reports an empty list.

use std::fmt::Write as _;

use funk_ir::text::print_symbol;
use funk_ir::{Attr, Diagnostic, Global, InitPiece, Linkage, Module, Op};

use super::{Cx, Lower, Unlowered, memory};
use crate::abi::symbol;
use crate::asm::{Asm, Reg};

/// The most bytes that a module's globals take, their padding included.
const LIMIT: u64 = 1 << 30;

/// How many units go on one `.byte` line.
const PER_LINE: usize = 16;

pub(super) fn lowering(name: &str) -> Option<Lower> {
    match name {
        "globaladdr" => Some(global_addr),
        _ => None,
    }
}

/// `%p: ptr<N> = globaladdr @g`.
fn global_addr(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    let ([Attr::Sym(g)], [], [p]) = (
        op.attrs.as_slice(),
        op.operands.as_slice(),
        op.results.as_slice(),
    ) else {
        return Err("globaladdr takes a global's symbol and defines a pointer".into());
    };
    cx.width(&p.name)?;
    cx.asm
        .ins("leaq", format_args!("{}(%rip), %rax", symbol(g)));
    cx.store(&p.name, Reg::Rax)
}

/// Appends the data of each global of `m`'s own table to `asm`, in the
/// table's order, or reports at the global each one that the backend
/// cannot place.
pub fn data(m: &Module, asm: &mut Asm, out: &mut Vec<Diagnostic>) {
    let table = m.symbols();
    let mut total: u64 = 0;
    let mut placed = Vec::new();
    for g in m.items.iter().filter_map(|i| i.as_global()) {
        let mut why = realised(m, g.memory).err();
        for piece in &g.init {
            if let InitPiece::Addr(t, _) = piece
                && let Some(target) = table.global(t)
                && let Err(e) = realised(m, target.memory)
            {
                why.get_or_insert(format!(
                    "addr({}) holds a pointer of memory {}: {e}",
                    print_symbol(t),
                    target.memory
                ));
            }
        }
        let padding = g.align.saturating_sub(1);
        let taken = g
            .size
            .checked_add(padding)
            .and_then(|b| total.checked_add(b))
            .filter(|&t| t <= LIMIT);
        match (taken, why) {
            (_, Some(why)) => out.push(at(g, why)),
            (None, None) => out.push(at(
                g,
                format!(
                    "the x86-64 backend places at most 2^30 bytes of globals, their \
                     alignment's padding included, and {} takes {} more and up to {} of \
                     padding, past the {total} already placed",
                    print_symbol(&g.name),
                    g.size,
                    padding
                ),
            )),
            (Some(t), None) => {
                total = t;
                global(asm, g);
                placed.push(g);
            }
        }
    }
    if !placed.is_empty() {
        report_table(asm, &placed);
    }
}

/// The table `__funk_globals`: the number of globals, then for each its
/// report's text up to its address, that text's length, its address and
/// its size, then the texts.
fn report_table(asm: &mut Asm, globals: &[&Global]) {
    asm.directive(format_args!(".section\t.rodata"));
    asm.directive(format_args!(".p2align\t3"));
    asm.directive(format_args!(".globl\t__funk_globals"));
    asm.directive(format_args!(".hidden\t__funk_globals"));
    asm.directive(format_args!(".type\t__funk_globals, @object"));
    asm.label("__funk_globals");
    asm.directive(format_args!(".quad\t{}", globals.len()));
    let texts: Vec<String> = globals
        .iter()
        .enumerate()
        .map(|(i, g)| report_text(i, g))
        .collect();
    for (i, (g, text)) in globals.iter().zip(&texts).enumerate() {
        asm.directive(format_args!(
            ".quad\t.Lfunk_global_text{i}, {}, {}, {}",
            text.len(),
            symbol(&g.name),
            g.size
        ));
    }
    for (i, text) in texts.iter().enumerate() {
        asm.label(&format!(".Lfunk_global_text{i}"));
        for line in text.as_bytes().chunks(PER_LINE) {
            let bytes: Vec<String> = line.iter().map(u8::to_string).collect();
            asm.directive(format_args!(".byte\t{}", bytes.join(", ")));
        }
    }
}

/// The JSON text that goes before the address of the `i`-th global `g` in
/// the memory report: a comma after the first, then
/// `{"global":"NAME","memory":N,"address":"`.
fn report_text(i: usize, g: &Global) -> String {
    let comma = if i == 0 { "" } else { "," };
    let name = json_escape(&print_symbol(&g.name));
    format!(
        "{comma}{{\"global\":\"{name}\",\"memory\":{},\"address\":\"",
        g.memory
    )
}

/// `text` as the inside of a JSON string.
fn json_escape(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for c in text.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            c if u32::from(c) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", u32::from(c));
            }
            c => out.push(c),
        }
    }
    out
}

fn at(g: &Global, why: String) -> Diagnostic {
    Diagnostic::at_block(&g.name, None, why)
}

/// Whether the backend realises memory `n`, or why not.
fn realised(m: &Module, n: u64) -> Result<(), String> {
    let n = u32::try_from(n).map_err(|_| format!("memory {n}, which the layout cannot declare"))?;
    memory::realised(&m.layout, n).map(|_| ())
}

/// Whether every unit of `g`'s initializer is 0.
fn all_zero(g: &Global) -> bool {
    g.init.iter().all(|p| match p {
        InitPiece::Units(us) => us.iter().all(|u| u.as_str() == "0"),
        InitPiece::Zeros(_) => true,
        InitPiece::Addr(..) => false,
    })
}

/// The data of `g`, which the backend can place.
fn global(asm: &mut Asm, g: &Global) {
    let sym = symbol(&g.name);
    asm.comment(format_args!("global {}", print_symbol(&g.name)));
    let zero = all_zero(g);
    let section = match (g.constant, zero) {
        (true, _) => ".section\t.rodata",
        (false, true) => ".bss",
        (false, false) => ".data",
    };
    asm.directive(format_args!("{section}"));
    if g.linkage == Linkage::Exported {
        asm.directive(format_args!(".globl\t{sym}"));
    }
    asm.directive(format_args!(".type\t{sym}, @object"));
    asm.directive(format_args!(".balign\t{}", g.align));
    asm.label(&sym);
    let mut placed: u64 = 0;
    if !zero || g.constant {
        for piece in &g.init {
            placed += emit(asm, piece);
        }
    }
    // `as` warns on a count of 0, and a build fails on any warning.
    if g.size > placed {
        asm.directive(format_args!(".zero\t{}", g.size - placed));
    }
    asm.directive(format_args!(".size\t{sym}, {}", g.size));
}

/// Writes `piece` and returns how many bytes it takes.
fn emit(asm: &mut Asm, piece: &InitPiece) -> u64 {
    match piece {
        InitPiece::Units(us) => {
            for line in us.chunks(PER_LINE) {
                let units: Vec<&str> = line.iter().map(|u| u.as_str()).collect();
                asm.directive(format_args!(".byte\t{}", units.join(", ")));
            }
            us.len() as u64
        }
        InitPiece::Zeros(0) => 0,
        InitPiece::Zeros(n) => {
            asm.directive(format_args!(".zero\t{n}"));
            *n
        }
        InitPiece::Addr(t, k) => {
            asm.directive(format_args!(".quad\t{}+{k}", symbol(t)));
            8
        }
    }
}
