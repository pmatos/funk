//! How `call` is lowered (#20): System V between funk functions
//! (ADR-2026-10-30-1232), the arguments past the sixth pushed with padding
//! to keep `%rsp` 16-byte aligned, no extension of any argument or result
//! (`docs/decisions/x86-64-backend-abi.md#calls-between-funk-functions`),
//! the callee's symbol as ADR-2026-10-30-1232 spells it, no callee-saved
//! register but `%rbp` ever written, and no call that lands more than a
//! page below the stack's last access.

use funk_ir::{Module, Registry, parse};
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
    returning(n, 1, types)
}

/// [`chain`], where `@callee` returns its first parameter `r` times and
/// `@caller` returns all `r` results of its call: in memory when `r` is
/// more than two (ADR-2026-10-30-1232).
fn returning(n: usize, r: usize, types: &[&str]) -> String {
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
    let names: Vec<String> = (0..r)
        .map(|k| {
            if k == 0 {
                "%r".into()
            } else {
                format!("%r{k}")
            }
        })
        .collect();
    let defs: Vec<String> = names.iter().map(|v| format!("{v}: {}", ty(0))).collect();
    let types = vec![ty(0); r].join(", ");
    format!(
        "func @callee({}) -> {types} {{\n^entry:\n  ret {} @0\n}}\n\n\
         func @caller({}) -> {types} {{\n^entry:\n  {} = call @callee {} @0\n  ret {} @0\n}}\n",
        params(false),
        vec!["%p0"; r].join(", "),
        params(true),
        defs.join(", "),
        args.join(", "),
        names.join(", ")
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
        for r in [2, 3, 9] {
            let text = returning(n.max(1), r, &["i16", "i1", "i32"]);
            check_registers_and_alignment(&lowered(&text));
        }
        let mut text = String::from("func @f() {\n^entry:\n");
        for k in 0..n {
            text += &format!("  %v{k}: i32 = const {k} @0\n");
        }
        text += "  call @f @0\n  ret @0\n}\n";
        check_registers_and_alignment(&lowered(&text));
    }
}

/// Checks that every access to the stack in every function is at most a
/// page below the deepest one already made, counting in bytes below the
/// function's entry, where the caller wrote the return address: the slots
/// at `-N(%rbp)`, each push, the probe loop's pages and each call's return
/// address (`docs/decisions/x86-64-backend.md#frames-and-slots`,
/// `docs/decisions/x86-64-backend.md#stack-probes`).
fn check_no_access_skips_a_page(asm: &str) {
    let (mut below, mut deepest, mut pages) = (0i64, 0i64, 1i64);
    let touch = |at: i64, deepest: &mut i64, line: &str| {
        assert!(at - *deepest <= 4096, "{at} below {deepest}: {line}\n{asm}");
        *deepest = (*deepest).max(at);
    };
    for line in asm.lines() {
        // `leaq` of a slot, the address of a result area, touches nothing.
        if let Some(i) = line.find("(%rbp)").filter(|_| !line.contains("leaq")) {
            let start = line[..i].rfind(['\t', ' ']).map_or(0, |j| j + 1);
            if let Ok(disp) = line[start..i].parse::<i64>() {
                touch(8 - disp, &mut deepest, line);
            }
        }
        let parts: Vec<&str> = line.trim().split('\t').collect();
        match parts.as_slice() {
            [label] if label.ends_with(':') && !label.starts_with('.') && label != &"1:" => {
                (below, deepest) = (0, 0);
            }
            ["movl", ops] if ops.ends_with(", %r11d") => {
                pages = ops[1..ops.len() - 7].parse().unwrap();
            }
            ["orq", "$0, (%rsp)"] => {
                touch(below, &mut deepest, line);
                for _ in 1..pages {
                    below += 4096;
                    touch(below, &mut deepest, line);
                }
            }
            ["pushq", _] => {
                below += 8;
                touch(below, &mut deepest, line);
            }
            ["subq", ops] if ops.ends_with(", %rsp") => {
                below += ops[1..ops.len() - 6].parse::<i64>().unwrap();
            }
            ["addq", ops] if ops.ends_with(", %rsp") => {
                below -= ops[1..ops.len() - 6].parse::<i64>().unwrap();
            }
            ["call", _] => touch(below + 8, &mut deepest, line),
            _ => {}
        }
    }
}

/// A call lands at most a page below the last access, from frames of 0 to
/// 13 values and of about one and two pages, with no argument and with
/// stack arguments, and with results in a result area at the frame's
/// bottom: a frame of exactly a page is probed
/// (`docs/decisions/x86-64-backend.md#stack-probes`).
#[test]
fn a_call_lands_at_most_a_page_below_the_last_access() {
    let consts = |n: usize| -> String {
        (0..n)
            .map(|k| format!("  %v{k}: i64 = const {k} @0\n"))
            .collect()
    };
    let seven = ["%x"; 7].join(", ");
    let callee = "func @g() {\n^entry:\n  ret @0\n}\n\n\
                  func @h(%a: i64, %b: i64, %c: i64, %d: i64, %e: i64, %f: i64, %g: i64) {\n\
                  ^entry:\n  ret @0\n}\n\n\
                  func @h3(%a: i64, %b: i64, %c: i64, %d: i64, %e: i64, %f: i64, %g: i64) \
                  -> i64, i64, i64 {\n^entry:\n  ret %a, %b, %c @0\n}\n\n";
    for n in (0..=13).chain(500..=530).chain(1015..=1030) {
        let text = format!(
            "{callee}func @f() {{\n^entry:\n  call @g @0\n{}  ret @0\n}}\n\n\
             func @f2(%x: i64) {{\n^entry:\n  call @h {seven} @0\n{}  ret @0\n}}\n\n\
             func @f3(%x: i64) {{\n^entry:\n  \
             %a: i64, %b: i64, %c: i64 = call @h3 {seven} @0\n{}  ret @0\n}}\n",
            consts(n),
            consts(n),
            consts(n)
        );
        let asm = lowered(&text);
        check_no_access_skips_a_page(&asm);
        if n == 512 {
            assert_has(&asm, &["movl\t$1, %r11d"]);
        }
    }
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

/// Entry generation uses the same outgoing convention as a fir call and
/// restores its space before the runtime prints the result. Counts around
/// a page make a missing or double-counted outgoing area visible in the
/// reservation table, as well as exercising the register/stack transition.
#[test]
fn entry_restores_outgoing_space_and_reserves_its_peak() {
    for (n, outgoing, reservation) in [
        (0, 0, 20480),
        (6, 0, 20480),
        (7, 16, 20480),
        (8, 16, 20480),
        (509, 4032, 28672),
        (510, 4032, 28672),
        (511, 4048, 28672),
        (512, 4048, 28672),
        (513, 4064, 32768),
        (600, 4752, 32768),
    ] {
        let params = (0..n)
            .map(|k| format!("%p{k}: i64"))
            .collect::<Vec<_>>()
            .join(", ");
        let text = format!(
            "func @f({params}) -> i64 {{\n^entry:\n  %r: i64 = const 7 @0\n  ret %r @0\n}}\n"
        );
        let entry = compile(&module(&text)).unwrap().entry;
        let after_call = entry.split_once("\tcall\tf\n").unwrap().1;
        let cleanup = if outgoing == 0 {
            String::new()
        } else {
            format!("\taddq\t${outgoing}, %rsp\n")
        };
        // The result goes in the first slot, whose argument the call no
        // longer needs, and is printed from there (ADR-2026-10-30-1232).
        assert!(
            after_call.starts_with(&format!(
                "{cleanup}\tmovq\t%rax, -8(%rbp)\n\tmovq\t-8(%rbp), %rdi\n"
            )),
            "{n} arguments: {after_call}"
        );
        assert!(
            entry.contains(&format!(
                "\t.quad\t.Lname0, 2, {n}, __funk_entry_0, {reservation}, 0\n"
            )),
            "{n} arguments: {entry}"
        );
    }
}
