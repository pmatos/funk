//! How `icmp` and `select` are lowered (#16): `icmp` extends both operands
//! from `N` bits as its predicate reads them, then is one `cmpq` and one
//! `setCC` (ADR-2026-10-30-1231); `select` tests bit 0 of its condition and
//! is one `cmovzq`, with no branch (ADR-2026-10-31-0215).

use funk_ir::{Registry, parse};
use funk_x86_64::compile;
use funk_x86_64::width::SUPPORTED as WIDTHS;

/// The assembly of `@f(params) -> result` with the one op `line`, whose
/// result is `%r`.
fn lowered(params: &str, result: &str, line: &str) -> String {
    let text = format!(
        "func @f({params}) -> {result} {{\n^entry:\n  {line} @0\n  ret %r @0\n}}\n\nlocs {{\n  @0 = unknown\n}}\n"
    );
    compile(&parse(&text, &Registry::core()).unwrap())
        .unwrap()
        .module
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

/// Each predicate, whether it reads its operands as unsigned (or as bits),
/// and its `setCC`.
const PREDICATES: [(&str, bool, &str); 10] = [
    ("eq", true, "sete"),
    ("ne", true, "setne"),
    ("slt", false, "setl"),
    ("sle", false, "setle"),
    ("sgt", false, "setg"),
    ("sge", false, "setge"),
    ("ult", true, "setb"),
    ("ule", true, "setbe"),
    ("ugt", true, "seta"),
    ("uge", true, "setae"),
];

#[test]
fn icmp_extends_both_operands_then_compares_and_sets_al() {
    assert_eq!(
        PREDICATES.map(|(p, ..)| p),
        funk_ir::dialects::core::PREDICATES
    );
    for w in WIDTHS {
        for (p, zero, set) in PREDICATES {
            let line = format!("%r: i1 = icmp {p} %a, %b");
            let code = format!(
                "\t# {line} @0\n\tmovq\t-8(%rbp), %rax\n{}\tmovq\t-16(%rbp), %rcx\n{}\
                 \tcmpq\t%rcx, %rax\n\t{set}\t%al\n\tmovq\t%rax, -24(%rbp)\n\t# ret %r @0\n",
                extend(zero, w, false),
                extend(zero, w, true),
            );
            let asm = lowered(&format!("%a: i{w}, %b: i{w}"), "i1", &line);
            assert!(asm.contains(&code), "{code}\nnot in\n{asm}");
        }
    }
}

#[test]
fn select_tests_bit_0_of_its_condition_and_moves_with_no_branch() {
    for w in WIDTHS {
        let line = format!("%r: i{w} = select %c, %a, %b");
        let code = format!(
            "\t# {line} @0\n\tmovq\t-8(%rbp), %rcx\n\tmovq\t-16(%rbp), %rax\n\
             \ttestb\t$1, %cl\n\tcmovzq\t-24(%rbp), %rax\n\tmovq\t%rax, -32(%rbp)\n\
             \t# ret %r @0\n"
        );
        let params = format!("%c: i1, %a: i{w}, %b: i{w}");
        let asm = lowered(&params, &format!("i{w}"), &line);
        assert!(asm.contains(&code), "{code}\nnot in\n{asm}");
        let body = asm.split("\t# ret").next().unwrap_or_default();
        assert!(!body.contains("\tj"), "a branch in\n{asm}");
    }
}
