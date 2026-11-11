//! Incoming arguments through the ABI interface and function lowering.

use funk_ir::{Registry, parse};

use super::Arg;
use crate::asm::Mem;
use crate::width::Class;

fn arguments(words: &[usize]) -> Vec<Arg> {
    let mut used = 0;
    words
        .iter()
        .map(|&words| {
            used += words;
            Arg {
                slot: Mem {
                    disp: -8 * used as i32,
                },
                class: if words == 2 { Class::Pair } else { Class::Int },
            }
        })
        .collect()
}

/// Characterize lowering before moving receipt behind its own interface.
/// The optional result-area address follows the parameters and one constant.
fn lowered_receipt(words: &[usize], hidden: bool) -> String {
    let params: Vec<String> = words
        .iter()
        .enumerate()
        .map(|(i, w)| format!("%p{i}: i{}", if *w == 2 { 128 } else { 64 }))
        .collect();
    let (results, ret) = if hidden {
        ("-> i64, i64, i64", "%v, %v, %v")
    } else {
        ("", "")
    };
    let text = format!(
        "func @f({}) {results} {{\n^entry:\n  %v: i64 = const 0 @0\n  ret {ret} @0\n}}\n\nlocs {{\n  @0 = unknown\n}}\n",
        params.join(", ")
    );
    let m = parse(&text, &Registry::core()).unwrap();
    let asm = crate::compile(&m).unwrap().module;
    let prologue = asm.split_once("\tmovq\t%rsp, %rbp\n").unwrap().1;
    let receipt = prologue.split_once(".Lb0_entry:\n").unwrap().0;
    receipt.split_once('\n').unwrap().1.to_string() // The frame's subq.
}

#[test]
fn lowering_preserves_register_reuse_after_a_stack_pair() {
    let expected = concat!(
        "\tmovq\t%rdi, -8(%rbp)\n",
        "\tmovq\t%rsi, -16(%rbp)\n",
        "\tmovq\t%rdx, -24(%rbp)\n",
        "\tmovq\t%rcx, -32(%rbp)\n",
        "\tmovq\t%r8, -40(%rbp)\n",
        "\tmovq\t16(%rbp), %rax\n\tmovq\t%rax, -56(%rbp)\n",
        "\tmovq\t24(%rbp), %rax\n\tmovq\t%rax, -48(%rbp)\n",
        "\tmovq\t%r9, -64(%rbp)\n",
    );
    assert_eq!(lowered_receipt(&[1, 1, 1, 1, 1, 2, 1], false), expected);
}

#[test]
fn lowering_receives_the_result_area_before_shifted_parameters() {
    let expected = concat!(
        "\tmovq\t%rdi, -64(%rbp)\n",
        "\tmovq\t%rsi, -8(%rbp)\n",
        "\tmovq\t%rdx, -16(%rbp)\n",
        "\tmovq\t%rcx, -24(%rbp)\n",
        "\tmovq\t%r8, -32(%rbp)\n",
        "\tmovq\t16(%rbp), %rax\n\tmovq\t%rax, -48(%rbp)\n",
        "\tmovq\t24(%rbp), %rax\n\tmovq\t%rax, -40(%rbp)\n",
    );
    // Six parameter eightbytes, the constant, then the result-area address.
    assert_eq!(lowered_receipt(&[1, 1, 1, 1, 2], true), expected);
}

fn received(words: &[usize], hidden: Option<i32>) -> String {
    let mut asm = crate::asm::Asm::new();
    super::receive(&mut asm, &arguments(words), hidden.map(|disp| Mem { disp })).unwrap();
    asm.finish()
}

#[test]
fn receipt_without_parameters_only_stores_a_hidden_address_when_present() {
    assert_eq!(received(&[], None), "");
    assert_eq!(received(&[], Some(-8)), "\tmovq\t%rdi, -8(%rbp)\n");
}

#[test]
fn receipt_uses_six_registers_then_the_stack_above_the_saved_frame() {
    assert_eq!(
        received(&[1; 8], None),
        concat!(
            "\tmovq\t%rdi, -8(%rbp)\n",
            "\tmovq\t%rsi, -16(%rbp)\n",
            "\tmovq\t%rdx, -24(%rbp)\n",
            "\tmovq\t%rcx, -32(%rbp)\n",
            "\tmovq\t%r8, -40(%rbp)\n",
            "\tmovq\t%r9, -48(%rbp)\n",
            "\tmovq\t16(%rbp), %rax\n\tmovq\t%rax, -56(%rbp)\n",
            "\tmovq\t24(%rbp), %rax\n\tmovq\t%rax, -64(%rbp)\n",
        )
    );
}

#[test]
fn receipt_stores_three_register_pairs_low_half_first() {
    assert_eq!(
        received(&[2; 3], None),
        concat!(
            "\tmovq\t%rdi, -16(%rbp)\n",
            "\tmovq\t%rsi, -8(%rbp)\n",
            "\tmovq\t%rdx, -32(%rbp)\n",
            "\tmovq\t%rcx, -24(%rbp)\n",
            "\tmovq\t%r8, -48(%rbp)\n",
            "\tmovq\t%r9, -40(%rbp)\n",
        )
    );
}

#[test]
fn receipt_leaves_the_last_register_for_a_scalar_after_a_spilled_pair() {
    assert_eq!(
        received(&[1, 1, 1, 1, 1, 2, 1], None),
        lowered_receipt(&[1, 1, 1, 1, 1, 2, 1], false)
    );
}

#[test]
fn receipt_skips_the_stack_alignment_hole_before_a_pair() {
    assert_eq!(
        received(&[2, 2, 2, 1, 2], None),
        concat!(
            "\tmovq\t%rdi, -16(%rbp)\n",
            "\tmovq\t%rsi, -8(%rbp)\n",
            "\tmovq\t%rdx, -32(%rbp)\n",
            "\tmovq\t%rcx, -24(%rbp)\n",
            "\tmovq\t%r8, -48(%rbp)\n",
            "\tmovq\t%r9, -40(%rbp)\n",
            "\tmovq\t16(%rbp), %rax\n\tmovq\t%rax, -56(%rbp)\n",
            "\tmovq\t32(%rbp), %rax\n\tmovq\t%rax, -72(%rbp)\n",
            "\tmovq\t40(%rbp), %rax\n\tmovq\t%rax, -64(%rbp)\n",
        )
    );
}

#[test]
fn receipt_shifts_parameters_for_the_hidden_result_area_address() {
    assert_eq!(
        received(&[1, 1, 1, 1, 2], Some(-64)),
        lowered_receipt(&[1, 1, 1, 1, 2], true)
    );
    assert_eq!(
        received(&[2, 2, 1, 2], Some(-64)),
        concat!(
            "\tmovq\t%rdi, -64(%rbp)\n",
            "\tmovq\t%rsi, -16(%rbp)\n",
            "\tmovq\t%rdx, -8(%rbp)\n",
            "\tmovq\t%rcx, -32(%rbp)\n",
            "\tmovq\t%r8, -24(%rbp)\n",
            "\tmovq\t%r9, -40(%rbp)\n",
            "\tmovq\t16(%rbp), %rax\n\tmovq\t%rax, -56(%rbp)\n",
            "\tmovq\t24(%rbp), %rax\n\tmovq\t%rax, -48(%rbp)\n",
        )
    );
}
