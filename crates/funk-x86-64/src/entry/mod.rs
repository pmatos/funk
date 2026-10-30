//! The entry point of an executable that `funk build` links (ADR-2026-10-30-1233).
//!
//! It is one assembly file: the fixed runtime in `runtime.s`, then what this
//! module writes for the module being built. That is a wrapper for each
//! function, which parses the function's arguments, calls it by the System V
//! convention and prints its result, and the table `__funk_functions`, which
//! gives each function's name as fir writes it (`@f`, `@"a b"`), its number
//! of parameters and its wrapper. The runtime finds a function in the table
//! by the name on the command line.

use funk_ir::text::print_symbol;
use funk_ir::{Diagnostic, Func, Module};

use crate::abi::{ARG_REGS, RESULT_REG, symbol};
use crate::asm::{Asm, Mem, NO_EXEC_STACK, Reg};
use crate::frame::{self, displacement, size_for};
use crate::lower::at;
use crate::width::{self, Ext};

/// The runtime: the entry point `__funk_start` and the routines that the
/// wrappers call.
const RUNTIME: &str = include_str!("runtime.s");

/// The entry point's assembly for `m`, which the backend has lowered. A
/// function whose results the wrappers cannot print is reported.
pub fn generate(m: &Module) -> Result<String, Vec<Diagnostic>> {
    let mut asm = Asm::new();
    asm.raw(RUNTIME);
    asm.directive(format_args!(".text"));
    let mut out = Vec::new();
    let funcs: Vec<&Func> = m.funcs().collect();
    for (i, f) in funcs.iter().enumerate() {
        if let Err(d) = wrapper(&mut asm, i, f) {
            out.push(d);
        }
    }
    if !out.is_empty() {
        return Err(out);
    }
    asm.directive(format_args!(".section\t.rodata"));
    asm.directive(format_args!(".p2align\t3"));
    asm.label("__funk_functions");
    asm.directive(format_args!(".quad\t{}", funcs.len()));
    for (i, f) in funcs.iter().enumerate() {
        let name = print_symbol(&f.name);
        asm.directive(format_args!(
            ".quad\t.Lname{i}, {}, {}, __funk_entry_{i}",
            name.len(),
            f.params.len()
        ));
    }
    for (i, f) in funcs.iter().enumerate() {
        asm.label(&format!(".Lname{i}"));
        for chunk in print_symbol(&f.name).as_bytes().chunks(16) {
            let bytes: Vec<String> = chunk.iter().map(u8::to_string).collect();
            asm.directive(format_args!(".byte\t{}", bytes.join(", ")));
        }
    }
    asm.raw(NO_EXEC_STACK);
    Ok(asm.finish())
}

/// The wrapper `__funk_entry_I` of the `i`-th function `f`.
///
/// Lowering has already reported each parameter whose width the backend
/// does not lower, and each `ret` with more than one value. The wrapper
/// checks the signature again because a function that never reaches a
/// `ret`, which branches allow, must still have results it can print.
fn wrapper(asm: &mut Asm, i: usize, f: &Func) -> Result<(), Diagnostic> {
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
    Ok(())
}
