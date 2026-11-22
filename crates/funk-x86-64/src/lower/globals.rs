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

use funk_ir::{Attr, Diagnostic, Global, InitPiece, Linkage, Module, Op};

use super::{Cx, Lower, Unlowered, memory};
use crate::abi::symbol;
use crate::asm::{Asm, Reg};

/// The most bytes that a module's globals take, their padding included.
pub const LIMIT: u64 = 1 << 30;

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
    for g in m.items.iter().filter_map(|i| i.as_global()) {
        let mut why = realised(m, g.memory).err();
        for piece in &g.init {
            if let InitPiece::Addr(t, _) = piece
                && let Some(target) = table.global(t)
                && let Err(e) = realised(m, target.memory)
            {
                why.get_or_insert(format!(
                    "addr({}) holds a pointer of memory {}: {e}",
                    print(t),
                    target.memory
                ));
            }
        }
        let taken = g
            .size
            .checked_add(g.align.saturating_sub(1))
            .and_then(|b| total.checked_add(b))
            .filter(|&t| t <= LIMIT);
        match (taken, why) {
            (_, Some(why)) => out.push(at(g, why)),
            (None, None) => out.push(at(
                g,
                format!(
                    "the x86-64 backend places at most 2^30 bytes of globals, their \
                     alignment's padding included, and {} takes {} more",
                    print(&g.name),
                    g.size
                ),
            )),
            (Some(t), None) => {
                total = t;
                global(asm, g);
            }
        }
    }
}

/// The text of the symbol `name`.
fn print(name: &str) -> String {
    funk_ir::text::print_symbol(name)
}

fn at(g: &Global, why: String) -> Diagnostic {
    Diagnostic::at_block(&g.name, None, why)
}

/// Memory `n`'s entry when the backend realises it, or why not.
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
    asm.comment(format_args!("global {}", print(&g.name)));
    let zero = all_zero(g);
    if g.constant {
        asm.directive(format_args!(".section\t.rodata"));
    } else if zero {
        asm.directive(format_args!(".bss"));
    } else {
        asm.directive(format_args!(".data"));
    }
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
