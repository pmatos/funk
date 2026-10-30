//! How `add`, `sub`, `mul` and `freeze` are lowered (#14): one 64-bit
//! instruction at every width, the same with any flags, and `freeze` as a
//! copy into its own slot (ADR-2026-10-30-1231, ADR-2026-10-30-2248).

use funk_ir::dialects::core::WRAP_FLAG_SETS;
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
fn each_op_is_one_instruction_whatever_its_flags_and_width() {
    for w in WIDTHS {
        for (op, mnemonic) in [("add", "addq"), ("sub", "subq"), ("mul", "imulq")] {
            for flags in WRAP_FLAG_SETS {
                let words: Vec<&str> = std::iter::once(op).chain(flags.iter().copied()).collect();
                let line = format!("%r: i{w} = {} %a, %b", words.join(" "));
                let code = format!(
                    "\t# {line} @0\n\tmovq\t-8(%rbp), %rax\n\t{mnemonic}\t-16(%rbp), %rax\n\
                     \tmovq\t%rax, -24(%rbp)\n\t# ret %r @0\n"
                );
                let asm = lowered(w, &line);
                assert!(asm.contains(&code), "{code}\nnot in\n{asm}");
            }
        }
    }
}

#[test]
fn freeze_copies_its_operand_into_its_own_slot() {
    for w in WIDTHS {
        let line = format!("%r: i{w} = freeze %b");
        let code = format!(
            "\t# {line} @0\n\tmovq\t-16(%rbp), %rax\n\tmovq\t%rax, -24(%rbp)\n\
             \t# ret %r @0\n"
        );
        let asm = lowered(w, &line);
        assert!(asm.contains(&code), "{code}\nnot in\n{asm}");
    }
}
