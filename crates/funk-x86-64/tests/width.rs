//! How `zext`, `sext` and `trunc` are lowered (#17): `zext` and `sext`
//! extend their operand from its width to 64 bits, by zero or by sign, and
//! `trunc` is a copy (ADR-2026-10-30-1231).

use funk_ir::{Registry, parse};
use funk_x86_64::compile;
use funk_x86_64::width::SUPPORTED as WIDTHS;

/// The assembly of `@f(%a: iM) -> iN` with the one op `line`, whose result
/// is `%r`.
fn lowered(m: u32, n: u32, line: &str) -> String {
    let text = format!(
        "func @f(%a: i{m}) -> i{n} {{\n^entry:\n  {line} @0\n  ret %r @0\n}}\n\nlocs {{\n  @0 = unknown\n}}\n"
    );
    compile(&parse(&text, &Registry::core()).unwrap())
        .unwrap()
        .module
}

/// The instructions that extend `%rax` from `M` bits to 64, by zero or by
/// sign.
fn extension(sign: bool, m: u32) -> &'static str {
    match (sign, m) {
        (false, 1) => "\tandl\t$1, %eax\n",
        (false, 8) => "\tmovzbl\t%al, %eax\n",
        (false, 16) => "\tmovzwl\t%ax, %eax\n",
        (false, 32) => "\tmovl\t%eax, %eax\n",
        (true, 1) => "\tshlq\t$63, %rax\n\tsarq\t$63, %rax\n",
        (true, 8) => "\tmovsbq\t%al, %rax\n",
        (true, 16) => "\tmovswq\t%ax, %rax\n",
        (true, 32) => "\tmovslq\t%eax, %rax\n",
        _ => panic!("no extension from i{m}"),
    }
}

#[test]
fn zext_and_sext_extend_their_operand_from_its_width() {
    for m in WIDTHS {
        for n in WIDTHS.into_iter().filter(|&n| m < n) {
            for (op, sign) in [("zext", false), ("sext", true)] {
                let line = format!("%r: i{n} = {op} %a");
                let code = format!(
                    "\t# {line} @0\n\tmovq\t-8(%rbp), %rax\n{}\tmovq\t%rax, -16(%rbp)\n\
                     \t# ret %r @0\n",
                    extension(sign, m)
                );
                let asm = lowered(m, n, &line);
                assert!(asm.contains(&code), "{code}\nnot in\n{asm}");
            }
        }
    }
}

#[test]
fn trunc_copies_its_operand_into_its_own_slot() {
    for m in WIDTHS {
        for n in WIDTHS.into_iter().filter(|&n| n < m) {
            let line = format!("%r: i{n} = trunc %a");
            let code = format!(
                "\t# {line} @0\n\tmovq\t-8(%rbp), %rax\n\tmovq\t%rax, -16(%rbp)\n\
                 \t# ret %r @0\n"
            );
            let asm = lowered(m, n, &line);
            assert!(asm.contains(&code), "{code}\nnot in\n{asm}");
        }
    }
}
