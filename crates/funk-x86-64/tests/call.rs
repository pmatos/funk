//! How `call` is lowered (#20): System V between funk functions
//! (ADR-2026-10-30-1232), the arguments past the sixth pushed with padding
//! to keep `%rsp` 16-byte aligned, no extension of any argument or result
//! (ADR-2026-11-02-1021), the callee's symbol as ADR-2026-10-30-1232 spells
//! it, and no callee-saved register but `%rbp` ever written.

use funk_ir::{LocRef, Module, Registry, parse};
use funk_x86_64::compile;

/// The module of the functions `funcs`, each with its ops at `@0`.
fn module(funcs: &str) -> Module {
    let text = format!("{funcs}\nlocs {{\n  @0 = unknown\n  @1 = \"c.c\":1:1 to 1:2\n}}\n");
    parse(&text, &Registry::core()).unwrap_or_else(|e| panic!("{e}\n{text}"))
}

/// The assembly of the functions `funcs`.
fn lowered(funcs: &str) -> String {
    compile(&module(funcs))
        .unwrap_or_else(|ds| panic!("{ds:#?}"))
        .module
}

fn assert_has(asm: &str, lines: &[&str]) {
    let want: String = lines.iter().map(|l| format!("\t{l}\n")).collect();
    assert!(asm.contains(&want), "{want}\nnot in\n{asm}");
}

/// `@callee` with `n` parameters of the types `types` in turn, which
/// returns its first, and `@caller`, which passes its own parameters in
/// reverse order to it.
fn chain(n: usize, types: &[&str]) -> String {
    let ty = |k: usize| types[k % types.len()];
    let params = |rev: bool| -> String {
        (0..n)
            .map(|k| {
                let t = if rev { ty(n - 1 - k) } else { ty(k) };
                format!("%p{k}: {t}")
            })
            .collect::<Vec<_>>()
            .join(", ")
    };
    let args: Vec<String> = (0..n).rev().map(|k| format!("%p{k}")).collect();
    format!(
        "func @callee({}) -> {} {{\n^entry:\n  ret %p0 @0\n}}\n\n\
         func @caller({}) -> {} {{\n^entry:\n  %r: {} = call @callee {} @0\n  ret %r @0\n}}\n",
        params(false),
        ty(0),
        params(true),
        ty(0),
        ty(0),
        args.join(", ")
    )
}

#[test]
fn six_arguments_go_in_registers_as_their_slots_hold_them() {
    let asm = lowered(&chain(6, &["i8", "i1", "i16"]));
    assert_has(
        &asm,
        &[
            "# %r: i8 = call @callee %p5, %p4, %p3, %p2, %p1, %p0 @0",
            "movq\t-48(%rbp), %rdi",
            "movq\t-40(%rbp), %rsi",
            "movq\t-32(%rbp), %rdx",
            "movq\t-24(%rbp), %rcx",
            "movq\t-16(%rbp), %r8",
            "movq\t-8(%rbp), %r9",
            "call\tcallee",
            "movq\t%rax, -56(%rbp)",
            "# ret %r @0",
        ],
    );
}

#[test]
fn an_odd_number_of_stack_arguments_is_padded_to_keep_the_stack_aligned() {
    // `%p0` is the seventh argument: at `(%rsp)` at the call.
    let asm = lowered(&chain(7, &["i32", "i64"]));
    assert_has(
        &asm,
        &[
            "subq\t$8, %rsp",
            "pushq\t-8(%rbp)",
            "movq\t-56(%rbp), %rdi",
            "movq\t-48(%rbp), %rsi",
            "movq\t-40(%rbp), %rdx",
            "movq\t-32(%rbp), %rcx",
            "movq\t-24(%rbp), %r8",
            "movq\t-16(%rbp), %r9",
            "call\tcallee",
            "addq\t$16, %rsp",
            "movq\t%rax, -64(%rbp)",
        ],
    );
}

#[test]
fn an_even_number_of_stack_arguments_needs_no_padding() {
    let asm = lowered(&chain(8, &["i1", "i8", "i16", "i32", "i64"]));
    assert_has(
        &asm,
        &[
            "# %r: i1 = call @callee %p7, %p6, %p5, %p4, %p3, %p2, %p1, %p0 @0",
            "pushq\t-8(%rbp)",
            "pushq\t-16(%rbp)",
            "movq\t-64(%rbp), %rdi",
        ],
    );
    assert_has(&asm, &["call\tcallee", "addq\t$16, %rsp"]);
    assert!(!asm.contains("subq\t$8, %rsp"), "{asm}");
}

#[test]
fn no_argument_and_no_result_is_extended() {
    // A narrow argument and result are moved whole: the only extension in
    // the callee is the `i1` result's (ADR-2026-10-30-1232).
    let asm = lowered(&chain(9, &["i1", "i8", "i16"]));
    for ext in ["movs", "movz", "andl", "shlq", "sarq", "cbtw", "cltq"] {
        assert!(
            asm.lines()
                .filter(|l| l.contains(ext))
                .all(|l| l == "\tandl\t$1, %eax"),
            "{ext} in\n{asm}"
        );
    }
}

#[test]
fn a_call_with_no_result_stores_nothing() {
    let asm = lowered(
        "func @sink(%x: i64) {\n^entry:\n  ret @0\n}\n\n\
         func @f(%x: i64) -> i64 {\n^entry:\n  call @sink %x @0\n  call @f %x @1\n  ret %x @0\n}\n",
    );
    assert_has(
        &asm,
        &[
            "# call @sink %x @0",
            "movq\t-8(%rbp), %rdi",
            "call\tsink",
            "# call @f %x @1",
            "movq\t-8(%rbp), %rdi",
            "call\tf",
            "# ret %x @0",
        ],
    );
}

#[test]
fn a_callee_is_named_by_its_symbol_in_the_object_file() {
    let asm = lowered(
        "func @\"1\"() {\n^entry:\n  ret @0\n}\n\n\
         func @_end() {\n^entry:\n  call @\"1\" @0\n  call @_end @0\n  call @x @0\n  ret @0\n}\n\n\
         func @x() {\n^entry:\n  ret @0\n}\n",
    );
    assert_has(&asm, &["call\t__funk_sym_31"]);
    assert_has(&asm, &["call\t__funk_sym_5f656e64"]);
    assert_has(&asm, &["call\tx"]);
}

/// Checks the assembly of every function: no callee-saved register but
/// `%rbp` is named, `%rbp` is only saved, set, restored and used as the
/// frame's base, and `%rsp` is 16-byte aligned at each `call`, counting
/// from the alignment of a function's entry, 8 bytes past a multiple of 16.
fn check_registers_and_alignment(asm: &str) {
    let mut below = 0i64;
    for line in asm.lines() {
        for reg in ["%rbx", "%ebx", "%bl", "%r12", "%r13", "%r14", "%r15"] {
            assert!(!line.contains(reg), "{line}\n{asm}");
        }
        let rbp_ok = ["\tpushq\t%rbp", "\tmovq\t%rsp, %rbp"].contains(&line)
            || line.starts_with("\t#")
            || line.replace("(%rbp)", "").find("%rbp").is_none();
        assert!(rbp_ok, "{line}");
        let parts: Vec<&str> = line.trim().split('\t').collect();
        match parts.as_slice() {
            [label] if label.ends_with(':') && !label.starts_with('.') && label != &"1:" => {
                below = 8;
            }
            ["pushq", _] => below += 8,
            ["subq", ops] if ops.ends_with(", %rsp") => {
                below += ops[1..ops.len() - 6].parse::<i64>().unwrap();
            }
            ["addq", ops] if ops.ends_with(", %rsp") => {
                below -= ops[1..ops.len() - 6].parse::<i64>().unwrap();
            }
            ["call", _] => assert_eq!(below % 16, 0, "{line}\n{asm}"),
            _ => {}
        }
    }
}

#[test]
fn a_call_keeps_the_stack_aligned_and_saves_no_register() {
    for n in 0..=13 {
        check_registers_and_alignment(&lowered(&chain(n.max(1), &["i8", "i64", "i1"])));
        let mut text = String::from("func @f() {\n^entry:\n");
        for k in 0..n {
            text += &format!("  %v{k}: i32 = const {k} @0\n");
        }
        text += "  call @f @0\n  ret @0\n}\n";
        check_registers_and_alignment(&lowered(&text));
    }
}

#[test]
fn a_call_with_more_than_one_result_is_reported_at_the_call() {
    let m = module(
        "func @two() -> i8, i8 {\n^entry:\n  %c: i8 = const 1 @0\n  ret %c, %c @0\n}\n\n\
         func @f() -> i8 {\n^entry:\n  %a: i8, %b: i8 = call @two @1\n  ret %a @0\n}\n",
    );
    let ds = compile(&m).unwrap_err();
    let at: Vec<_> = ds
        .iter()
        .map(|d| (d.func.as_deref(), d.block.as_deref(), d.op, d.loc))
        .collect();
    assert_eq!(
        at,
        [
            (Some("two"), Some("entry"), Some(1), Some(LocRef(0))),
            (Some("f"), Some("entry"), Some(0), Some(LocRef(1))),
        ],
        "{ds:#?}"
    );
    assert_eq!(
        ds[1].message,
        "call returns 2 values: the x86-64 backend returns at most one value so far"
    );
}

#[test]
fn a_call_at_a_width_the_backend_does_not_lower_is_reported_once() {
    let m = module(
        "func @g(%x: i7) -> i7 {\n^entry:\n  ret %x @0\n}\n\n\
         func @f(%x: i7) -> i7 {\n^entry:\n  %y: i7 = call @g %x @1\n  ret %y @0\n}\n",
    );
    let ds = compile(&m).unwrap_err();
    let msgs: Vec<String> = ds.iter().map(|d| d.to_string()).collect();
    assert_eq!(ds.len(), 3, "{msgs:#?}");
    assert!(msgs.iter().all(|d| !d.contains("call")), "{msgs:#?}");
}
