//! The entry point of an executable that `funk build` links
//! (`docs/decisions/x86-64-backend-executable.md#running-one-function`).
//!
//! It is one assembly file: the fixed runtime in `runtime.s` and `values.s`, which
//! parses arguments and prints results at every width
//! (`docs/decisions/x86-64-backend-executable.md#the-entry-file-and-its-runtime`),
//! then what this module
//! writes for the module being built. That is a wrapper for each function, which
//! parses the function's arguments, calls it by the System V convention and prints
//! each of its results, in order (ADR-2026-10-30-1232), and the table
//! `__funk_functions`, which gives each function's name as fir writes it (`@f`,
//! `@"a b"`), its number of parameters, its wrapper, the bytes of stack that a run
//! of it needs with every call it makes (`stack.rs`), and whether it is recursive.
//! The runtime finds a function in the table by the name on the command line,
//! reserves that stack, or for a recursive function up to the process's stack
//! limit (`ulimit -s`), and calls the wrapper on it
//! (`docs/decisions/x86-64-backend-executable.md#the-runs-stack`).

use funk_ir::text::print_symbol;
use funk_ir::{Diagnostic, Func, Module, Type};

use crate::abi::{
    self, Arg,
    results::{Area, Layout},
};
use crate::asm::{Asm, Mem, NO_EXEC_STACK, Reg};
use crate::frame::{self, PAGE, displacement, size_for};
use crate::lower::{Need, at};
use crate::width::{self, Class, Ext, PAIR};

/// The runtime: the entry point `__funk_start` and the routines that the
/// wrappers call, among them those that read arguments and print results
/// at every width, `i128` included, in `values.s`.
const RUNTIME: &str = concat!(include_str!("runtime.s"), include_str!("values.s"));

/// The line that goes before the entry's assembly when the program links
/// with the C library: it turns on the runtime's `.ifdef .Lfunk_libc`
/// parts, which flush the C library's streams and leave through its `exit`
/// (`docs/decisions/x86-64-backend.md#linking-with-the-host-c-library`).
/// Without it the runtime assembles as it always has.
pub const LIBC: &str = "\t.set\t.Lfunk_libc, 1\n";

/// The stack that the runtime's routines need below a wrapper, with room to
/// spare: the deepest of them uses less than 256 bytes, or, with the C
/// library, what its `fflush(NULL)` needs when a long values line flushes
/// the runtime's buffer.
const RUNTIME_STACK: u64 = 16 * 1024;

/// The largest figure in the table: no machine can map more, and the
/// runtime adds a guard page to it without overflow.
const MOST_STACK: u64 = 1 << 62;

/// The entry point's assembly for `m`, with the complete stack needs that
/// lowering computed for its functions, in the same order. A function whose
/// results the wrappers cannot print is reported.
pub fn generate(m: &Module, needs: &[Need]) -> Result<String, Vec<Diagnostic>> {
    let mut asm = Asm::new();
    asm.raw(RUNTIME);
    asm.directive(format_args!(".text"));
    let mut out = Vec::new();
    let mut stacks = Vec::new();
    let funcs: Vec<&Func> = m.funcs().collect();
    for (i, (f, need)) in funcs.iter().zip(needs).enumerate() {
        match wrapper(&mut asm, i, f, need.bytes) {
            Ok(stack) => stacks.push((stack, u8::from(need.recursive))),
            Err(d) => out.push(d),
        }
    }
    if !out.is_empty() {
        return Err(out);
    }
    asm.directive(format_args!(".section\t.rodata"));
    asm.directive(format_args!(".p2align\t3"));
    asm.label("__funk_functions");
    asm.directive(format_args!(".quad\t{}", funcs.len()));
    let names: Vec<String> = funcs.iter().map(|f| print_symbol(&f.name)).collect();
    for (i, ((f, name), (stack, recursive))) in funcs.iter().zip(&names).zip(&stacks).enumerate() {
        asm.directive(format_args!(
            ".quad\t.Lname{i}, {}, {}, __funk_entry_{i}, {stack}, {recursive}",
            name.len(),
            f.params.len()
        ));
    }
    for (i, name) in names.iter().enumerate() {
        asm.label(&format!(".Lname{i}"));
        for chunk in name.as_bytes().chunks(16) {
            let bytes: Vec<String> = chunk.iter().map(u8::to_string).collect();
            asm.directive(format_args!(".byte\t{}", bytes.join(", ")));
        }
    }
    asm.raw(NO_EXEC_STACK);
    Ok(asm.finish())
}

/// The wrapper `__funk_entry_I` of the `i`-th function `f`, a run of which
/// needs `need` bytes below its return address, and the bytes of stack that
/// the wrapper needs to run it.
///
/// Lowering has already reported each parameter and each value whose width
/// the backend does not lower. The wrapper checks the signature again
/// because a function that never reaches a `ret`, which branches allow,
/// must still have results it can print.
///
/// Its frame holds a slot per eightbyte of an argument, two for an `i128`,
/// which after the call holds an eightbyte of a result instead, and more
/// slots when the results take more eightbytes than the arguments. When
/// the results go in memory it also holds the slot for the result area's
/// address and, at its bottom, the area (ADR-2026-10-30-1232).
fn wrapper(asm: &mut Asm, i: usize, f: &Func, need: u64) -> Result<u64, Diagnostic> {
    let report = |why: String| at(f, f.body.blocks.first(), None, why);
    let params = widths(f.params.iter().map(|d| &d.ty)).map_err(report)?;
    let results = widths(&f.results).map_err(report)?;
    let layout = Layout::of_types(&f.results).map_err(report)?;
    let too_many = || report("the function has more values than a wrapper's frame holds".into());
    let param_types = f.params.iter().map(|d| &d.ty);
    let (args, arg_words) = slots(param_types).ok_or_else(too_many)?;
    let (outs, out_words) = slots(&f.results).ok_or_else(too_many)?;
    let values = arg_words.max(out_words);
    let address = values + 1;
    let size = size_for(values + layout.hidden_arguments())
        .and_then(|s| s.checked_add(layout.area()))
        .ok_or_else(too_many)?;
    let area = if layout.in_memory() {
        Some(Area {
            address: Mem {
                disp: displacement(address).ok_or_else(too_many)?,
            },
            base: Mem { disp: -size },
        })
    } else {
        None
    };
    asm.directive(format_args!(".p2align\t4"));
    asm.label(&format!("__funk_entry_{i}"));
    asm.comment(format_args!("{}", print_symbol(&f.name)));
    frame::prologue(asm, size);
    for (j, (w, a)) in params.iter().zip(&args).enumerate() {
        asm.ins("movl", format_args!("${j}, %edi"));
        asm.ins("movl", format_args!("${w}, %esi"));
        asm.ins("call", format_args!("__funk_rt_arg"));
        asm.ins("movq", format_args!("%rax, {}", a.slot));
        if a.class == Class::Pair {
            asm.ins("movq", format_args!("%rdx, {}", a.slot.high()));
        }
    }
    let mut passed = Vec::with_capacity(args.len() + 1);
    passed.extend(area.map(|a| Arg {
        slot: a.address,
        class: Class::Int,
    }));
    passed.extend(&args);
    if let Some(area) = area {
        layout.pass(asm, area);
    }
    let outgoing = abi::call(asm, &f.name, &passed).map_err(report)?;
    let into: Vec<Mem> = outs.iter().flat_map(eightbytes).collect();
    layout.receive(asm, area, &into).map_err(report)?;
    // `__funk_rt_value` reads the high half of an `i128` from `%rdx`.
    let (rdi, rdx) = (Reg::Rdi, Reg::Rdx);
    for (&w, out) in results.iter().zip(&outs) {
        asm.ins("movq", format_args!("{}, {}", out.slot, rdi.q()));
        if w == PAIR {
            asm.ins("movq", format_args!("{}, {}", out.slot.high(), rdx.q()));
        } else {
            width::extend(asm, Ext::Sign, w, rdi);
        }
        asm.ins("movl", format_args!("${w}, %esi"));
        asm.ins("call", format_args!("__funk_rt_value"));
    }
    frame::epilogue(asm);
    Ok(stack_need(need, size, outgoing))
}

/// The slots in a wrapper's frame of values of `types`, from `-8(%rbp)`
/// down, and how many slots they take: two for an `i128`, its low half
/// below, as in a function's frame
/// (`docs/decisions/x86-64-backend-lowering.md#lowering-i128`). The
/// arguments take these slots, and after the call the results take them
/// again.
fn slots<'t>(types: impl IntoIterator<Item = &'t Type>) -> Option<(Vec<Arg>, usize)> {
    let mut used = 0usize;
    let mut out = Vec::new();
    for t in types {
        let class = width::class(t);
        used = used.checked_add(class.words())?;
        let disp = displacement(used)?;
        out.push(Arg {
            slot: Mem { disp },
            class,
        });
    }
    Some((out, used))
}

/// The slot of each eightbyte of `value`, its low half first.
fn eightbytes(value: &Arg) -> impl Iterator<Item = Mem> {
    [value.slot, value.slot.high()]
        .into_iter()
        .take(value.class.words())
}

/// The width of each of `types`, or why the backend does not lower one.
fn widths<'t>(types: impl IntoIterator<Item = &'t Type>) -> Result<Vec<u32>, String> {
    types.into_iter().map(width::check).collect()
}

/// The bytes of stack that a wrapper with a frame of `wrapper` bytes and
/// `outgoing` bytes of argument space needs to call a function, a run of
/// which needs `need` bytes below its return address, rounded up to a page
/// and at most [`MOST_STACK`]. The call emitter supplies the outgoing
/// space, padding included. The wrapper's frame also holds a return address
/// and a saved `%rbp`.
fn stack_need(need: u64, wrapper: i32, outgoing: u64) -> u64 {
    let bytes = need
        .saturating_add(16)
        .saturating_add(u64::from(wrapper.unsigned_abs()))
        .saturating_add(outgoing)
        .saturating_add(RUNTIME_STACK)
        .min(MOST_STACK);
    let page = u64::from(PAGE.unsigned_abs());
    bytes.div_ceil(page) * page
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A function's need already holds its return address and saved
    /// `%rbp`: 16 bytes and its frame, and what its calls need.
    #[test]
    fn the_stack_holds_the_need_the_wrapper_and_the_runtime() {
        assert_eq!(stack_need(16, 0, 0), 5 * 4096);
        assert_eq!(stack_need(32, 0, 0), 5 * 4096);
        assert_eq!(stack_need(16, 0, 16), 5 * 4096);
        let big = 1 << 24;
        assert_eq!(stack_need(big + 16, 16, 0), big + 5 * 4096);
        let most = u64::from((i32::MAX & !15).unsigned_abs());
        assert_eq!(
            stack_need(most + 16, i32::MAX & !15, 8 << 20),
            (1 << 32) + (8 << 20) + 4 * 4096
        );
    }

    #[test]
    fn a_stack_beyond_any_machine_is_capped() {
        assert_eq!(stack_need(u64::MAX, 16, 0), MOST_STACK);
        assert_eq!(stack_need(MOST_STACK, 0, 0), MOST_STACK);
        assert_eq!(stack_need(MOST_STACK - 4096, 0, u64::MAX), MOST_STACK);
    }
}
