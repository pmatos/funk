//! The entry point of an executable that `funk build` links (ADR-2026-10-30-1233).
//!
//! It is one assembly file: the fixed runtime in `runtime.s`, then what this
//! module writes for the module being built. That is a wrapper for each
//! function, which parses the function's arguments, calls it by the System V
//! convention and prints its result, and the table `__funk_functions`, which
//! gives each function's name as fir writes it (`@f`, `@"a b"`), its number
//! of parameters, its wrapper and the bytes of stack that the wrapper needs.
//! The runtime finds a function in the table by the name on the command
//! line, reserves that stack, and calls the wrapper on it.

use funk_ir::text::print_symbol;
use funk_ir::{Diagnostic, Func, Module};

use crate::abi::{ARG_REGS, RESULT_REG, symbol};
use crate::asm::{Asm, Mem, NO_EXEC_STACK, Reg};
use crate::frame::{self, PAGE, displacement, size_for};
use crate::lower::at;
use crate::width::{self, Ext};

/// The runtime: the entry point `__funk_start` and the routines that the
/// wrappers call.
const RUNTIME: &str = include_str!("runtime.s");

/// The stack that the runtime's routines need below a wrapper, with room to
/// spare: the deepest of them uses less than 256 bytes.
const RUNTIME_STACK: u64 = 16 * 1024;

/// The entry point's assembly for `m`, which the backend has lowered into
/// functions with frames of `frames` bytes. A function whose results the
/// wrappers cannot print is reported.
pub fn generate(m: &Module, frames: &[i32]) -> Result<String, Vec<Diagnostic>> {
    let mut asm = Asm::new();
    asm.raw(RUNTIME);
    asm.directive(format_args!(".text"));
    let mut out = Vec::new();
    let mut stacks = Vec::new();
    let funcs: Vec<&Func> = m.funcs().collect();
    for (i, (f, &frame)) in funcs.iter().zip(frames).enumerate() {
        match wrapper(&mut asm, i, f, frame) {
            Ok(stack) => stacks.push(stack),
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
    for (i, ((f, name), stack)) in funcs.iter().zip(&names).zip(&stacks).enumerate() {
        asm.directive(format_args!(
            ".quad\t.Lname{i}, {}, {}, __funk_entry_{i}, {stack}",
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

/// The wrapper `__funk_entry_I` of the `i`-th function `f`, whose frame is
/// `frame` bytes, and the bytes of stack that the wrapper needs to run.
///
/// Lowering has already reported each parameter whose width the backend
/// does not lower, and each `ret` with more than one value. The wrapper
/// checks the signature again because a function that never reaches a
/// `ret`, which branches allow, must still have results it can print.
fn wrapper(asm: &mut Asm, i: usize, f: &Func, frame: i32) -> Result<u64, Diagnostic> {
    let report = |why: String| at(f, f.body.blocks.first(), None, why);
    let params = f
        .params
        .iter()
        .map(|d| width::check(&d.ty))
        .collect::<Result<Vec<u32>, String>>()
        .map_err(report)?;
    let result = match f.results.as_slice() {
        [] => None,
        [t] => Some(width::check(t).map_err(report)?),
        ts => {
            return Err(report(format!(
                "the function returns {} values: the x86-64 backend returns at most one \
                 value so far",
                ts.len()
            )));
        }
    };
    let too_many = || report("the function has more parameters than a frame holds".into());
    let size = size_for(params.len()).ok_or_else(too_many)?;
    let slots = (1..=params.len())
        .map(|k| displacement(k).map(|disp| Mem { disp }))
        .collect::<Option<Vec<Mem>>>()
        .ok_or_else(too_many)?;
    asm.directive(format_args!(".p2align\t4"));
    asm.label(&format!("__funk_entry_{i}"));
    asm.comment(format_args!("{}", print_symbol(&f.name)));
    frame::prologue(asm, size);
    for (j, (w, at)) in params.iter().zip(&slots).enumerate() {
        asm.ins("movl", format_args!("${j}, %edi"));
        asm.ins("movl", format_args!("${w}, %esi"));
        asm.ins("call", format_args!("__funk_rt_arg"));
        asm.ins("movq", format_args!("%rax, {at}"));
    }
    let on_stack = slots.get(ARG_REGS.len()..).unwrap_or_default();
    if on_stack.len() % 2 == 1 {
        asm.ins("subq", format_args!("$8, %rsp"));
    }
    for at in on_stack.iter().rev() {
        asm.ins("pushq", format_args!("{at}"));
    }
    for (reg, at) in ARG_REGS.iter().zip(&slots) {
        asm.ins("movq", format_args!("{at}, {}", reg.q()));
    }
    asm.ins("call", format_args!("{}", symbol(&f.name)));
    if let Some(w) = result {
        width::extend(asm, Ext::Sign, w, RESULT_REG);
        asm.ins("movq", format_args!("{}, {}", RESULT_REG.q(), Reg::Rdi.q()));
        asm.ins("movl", format_args!("${w}, %esi"));
        asm.ins("call", format_args!("__funk_rt_value"));
    }
    frame::epilogue(asm);
    Ok(stack_need(frame, size, on_stack.len()))
}

/// The bytes of stack that a wrapper with a frame of `wrapper` bytes and
/// `on_stack` arguments on the stack needs to call a function with a frame
/// of `frame` bytes, rounded up to a page. Each frame also holds a return
/// address and a saved `%rbp`, and the arguments on the stack are padded to
/// an even number.
fn stack_need(frame: i32, wrapper: i32, on_stack: usize) -> u64 {
    let on_stack = on_stack as u64;
    let args = 8 * (on_stack + on_stack % 2);
    let bytes = u64::from(frame.unsigned_abs())
        + 16
        + u64::from(wrapper.unsigned_abs())
        + 16
        + args
        + RUNTIME_STACK;
    let page = u64::from(PAGE.unsigned_abs());
    bytes.div_ceil(page) * page
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_stack_holds_both_frames_and_the_runtime() {
        assert_eq!(stack_need(0, 0, 0), 5 * 4096);
        assert_eq!(stack_need(16, 0, 0), 5 * 4096);
        let big = 1 << 24;
        assert_eq!(
            stack_need(big, 16, 0),
            u64::from(big.unsigned_abs()) + 5 * 4096
        );
        let most = i32::MAX & !15;
        assert_eq!(
            stack_need(most, most, (1 << 20) - 1),
            (1 << 32) + (8 << 20) + 4 * 4096
        );
    }
}
