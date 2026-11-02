//! How `sdiv`, `udiv`, `srem` and `urem` are lowered (#18): one bare
//! `idiv` or `div` of the op's own size, with no guard against a zero
//! divisor or the signed minimum divided by `-1`, the same with `exact` as
//! without (ADR-2026-10-31-0050).

use funk_ir::{Registry, parse};
use funk_x86_64::compile;

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

/// Asserts that `line` at `iW` lowers to `body` and nothing more: `%a` is
/// in `-8(%rbp)`, `%b` in `-16(%rbp)`, and the result goes to `-24(%rbp)`.
fn lowers_to(w: u32, line: &str, body: &[&str]) {
    let mut code = format!("\t# {line} @0\n\tmovq\t-8(%rbp), %rax\n\tmovq\t-16(%rbp), %rcx\n");
    for ins in body {
        code += &format!("\t{ins}\n");
    }
    code += "\t# ret %r @0\n";
    let asm = lowered(w, line);
    assert!(asm.contains(&code), "{code}\nnot in\n{asm}");
}

#[test]
fn i16_i32_and_i64_divide_rdx_rax_by_rcx_at_their_size() {
    for (w, sign, size, cx, ax, dx) in [
        (16, "cwtd", "w", "%cx", "%rax", "%rdx"),
        (32, "cltd", "l", "%ecx", "%rax", "%rdx"),
        (64, "cqto", "q", "%rcx", "%rax", "%rdx"),
    ] {
        let zero = "xorl\t%edx, %edx";
        let store = |r: &str| format!("movq\t{r}, -24(%rbp)");
        for (op, widen, ins, out) in [
            ("sdiv", sign, "idiv", ax),
            ("sdiv exact", sign, "idiv", ax),
            ("srem", sign, "idiv", dx),
            ("udiv", zero, "div", ax),
            ("udiv exact", zero, "div", ax),
            ("urem", zero, "div", dx),
        ] {
            let line = format!("%r: i{w} = {op} %a, %b");
            let div = format!("{ins}{size}\t{cx}");
            lowers_to(w, &line, &[widen, &div, &store(out)]);
        }
    }
}

#[test]
fn i8_divides_ax_by_cl_with_the_remainder_in_ah() {
    let (store, ah) = ("movq\t%rax, -24(%rbp)", "movb\t%ah, %al");
    let zero = "movzbl\t%al, %eax";
    for (op, body) in [
        ("sdiv", &["cbtw", "idivb\t%cl", store][..]),
        ("sdiv exact", &["cbtw", "idivb\t%cl", store]),
        ("srem", &["cbtw", "idivb\t%cl", ah, store]),
        ("udiv", &[zero, "divb\t%cl", store]),
        ("udiv exact", &[zero, "divb\t%cl", store]),
        ("urem", &[zero, "divb\t%cl", ah, store]),
    ] {
        lowers_to(8, &format!("%r: i8 = {op} %a, %b"), body);
    }
}

#[test]
fn i1_extends_both_operands_and_divides_as_i8() {
    let (store, ah) = ("movq\t%rax, -24(%rbp)", "movb\t%ah, %al");
    let sign = [
        "shlq\t$63, %rax",
        "sarq\t$63, %rax",
        "shlq\t$63, %rcx",
        "sarq\t$63, %rcx",
        "cbtw",
        "idivb\t%cl",
    ];
    let zero = [
        "andl\t$1, %eax",
        "andl\t$1, %ecx",
        "movzbl\t%al, %eax",
        "divb\t%cl",
    ];
    for (op, ext, rem) in [
        ("sdiv", &sign[..], false),
        ("sdiv exact", &sign, false),
        ("srem", &sign, true),
        ("udiv", &zero, false),
        ("udiv exact", &zero, false),
        ("urem", &zero, true),
    ] {
        let mut body = ext.to_vec();
        if rem {
            body.push(ah);
        }
        body.push(store);
        lowers_to(1, &format!("%r: i1 = {op} %a, %b"), &body);
    }
}
