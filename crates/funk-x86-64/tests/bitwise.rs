//! How the bitwise ops and shifts are lowered (#15): `and`, `or` and `xor`
//! are one 64-bit instruction at every width; a shift zero-extends its
//! amount, extends the value of a right shift as the shift reads it, and is
//! one 64-bit shift by `%cl` (ADR-2026-10-30-1231, ADR-2026-10-30-2248).

use funk_ir::{Registry, parse};
use funk_x86_64::compile;
use funk_x86_64::width::SUPPORTED as WIDTHS;

/// The assembly of `@f(%a: iW, %b: iW) -> iW` with the one op `line`,
/// whose result is `%r`.
fn lowered(w: u32, line: &str) -> String {
    let text = format!(
        "func @f(%a: i{w}, %b: i{w}) -> i{w} {{\n^entry:\n  {line} @0\n  ret %r @0\n}}\n\nlocs {{\n  @0 = unknown\n}}\n"
    );
    compile(&parse(&text, &Registry::core()).unwrap())
        .unwrap()
        .module
}

#[test]
fn each_bitwise_op_is_one_instruction_at_every_width() {
    for w in WIDTHS {
        for (op, mnemonic) in [("and", "andq"), ("or", "orq"), ("xor", "xorq")] {
            let line = format!("%r: i{w} = {op} %a, %b");
            let code = format!(
                "\t# {line} @0\n\tmovq\t-8(%rbp), %rax\n\t{mnemonic}\t-16(%rbp), %rax\n\
                 \tmovq\t%rax, -24(%rbp)\n\t# ret %r @0\n"
            );
            let asm = lowered(w, &line);
            assert!(asm.contains(&code), "{code}\nnot in\n{asm}");
        }
    }
}

/// The instructions that zero-extend (`zero`) or sign-extend `%rax` or
/// `%rcx` from `w` bits, as `width::extend` writes them.
fn extend(zero: bool, w: u32, rcx: bool) -> String {
    let (q, l, b, h) = if rcx {
        ("%rcx", "%ecx", "%cl", "%cx")
    } else {
        ("%rax", "%eax", "%al", "%ax")
    };
    match (zero, w) {
        (_, 64) => String::new(),
        (true, 1) => format!("\tandl\t$1, {l}\n"),
        (true, 8) => format!("\tmovzbl\t{b}, {l}\n"),
        (true, 16) => format!("\tmovzwl\t{h}, {l}\n"),
        (true, _) => format!("\tmovl\t{l}, {l}\n"),
        (false, 1) => format!("\tshlq\t$63, {q}\n\tsarq\t$63, {q}\n"),
        (false, 8) => format!("\tmovsbq\t{b}, {q}\n"),
        (false, 16) => format!("\tmovswq\t{h}, {q}\n"),
        (false, _) => format!("\tmovslq\t{l}, {q}\n"),
    }
}

#[test]
fn each_shift_extends_what_it_reads_and_shifts_by_cl() {
    for w in WIDTHS {
        // The op, the extension of its value (zero or sign), if any, and
        // its instruction.
        for (op, value, mnemonic) in [
            ("shl", None, "shlq"),
            ("lshr", Some(true), "shrq"),
            ("ashr", Some(false), "sarq"),
        ] {
            let line = format!("%r: i{w} = {op} %a, %b");
            let value = value.map_or(String::new(), |zero| extend(zero, w, false));
            let amount = extend(true, w, true);
            let code = format!(
                "\t# {line} @0\n\tmovq\t-8(%rbp), %rax\n{value}\tmovq\t-16(%rbp), %rcx\n\
                 {amount}\t{mnemonic}\t%cl, %rax\n\tmovq\t%rax, -24(%rbp)\n\t# ret %r @0\n"
            );
            let asm = lowered(w, &line);
            assert!(asm.contains(&code), "{code}\nnot in\n{asm}");
        }
    }
}

#[test]
fn a_shift_by_a_constant_n_or_more_is_lowered_as_any_other() {
    // It gives poison, which any value refines: no code tests the amount.
    for w in WIDTHS {
        let n = if w == 1 { "true".into() } else { w.to_string() };
        for op in ["shl", "lshr", "ashr"] {
            let text = format!(
                "func @f(%a: i{w}) -> i{w} {{\n^entry:\n  %n: i{w} = const {n} @0\n  \
                 %r: i{w} = {op} %a, %n @0\n  ret %r @0\n}}\n\nlocs {{\n  @0 = unknown\n}}\n"
            );
            let asm = compile(&parse(&text, &Registry::core()).unwrap())
                .unwrap()
                .module;
            assert!(asm.contains("%cl, %rax"), "{op} at i{w}:\n{asm}");
            assert!(!asm.contains("cmp"), "{op} at i{w}:\n{asm}");
        }
    }
}
