//! How `ret`, `call` and the entry wrapper move an `i128` among several
//! results (#21, #31). One `i128` alone comes back in `%rdx:%rax`; next to
//! any other result it goes in the result area, at an offset that is a
//! multiple of 16, its low half first (ADR-2026-11-03-0109). The area's
//! address is the call's first argument, so an `i128` argument that would
//! have had `%r8:%r9` finds one register left and goes on the stack
//! (ADR-2026-11-03-0108).

use funk_ir::{Module, Registry, parse};
use funk_x86_64::compile;

fn module(funcs: &str) -> Module {
    let text = format!("{funcs}\nlocs {{\n  @0 = unknown\n}}\n");
    parse(&text, &Registry::core()).unwrap_or_else(|e| panic!("{e}\n{text}"))
}

fn assert_has(asm: &str, lines: &[&str]) {
    let want: String = lines.iter().map(|l| format!("\t{l}\n")).collect();
    assert!(asm.contains(&want), "{want}\nnot in\n{asm}");
}

/// `@g` returns an `i64` and an `i128`, so its results go in memory, and
/// takes four `i64`s and an `i128`, which the area's address pushes to the
/// stack. `@f` calls it and returns an `i1`, an `i128` and an `i8`.
const MIXED: &str = "func @g(%a: i64, %b: i64, %c: i64, %d: i64, %x: i128) -> i64, i128 {\n\
                     ^entry:\n  ret %d, %x @0\n}\n\n\
                     func @f(%a: i64, %b: i64, %c: i64, %d: i64, %x: i128) -> i1, i128, i8 {\n\
                     ^entry:\n  %r: i64, %s: i128 = call @g %a, %b, %c, %d, %x @0\n  \
                     %t: i1 = trunc %r @0\n  %u: i8 = trunc %s @0\n  ret %t, %s, %u @0\n}\n";

/// The address arrives in `%rdi`, the four `i64`s in `%rsi` to `%r8`, and
/// the `i128` at `16(%rbp)` and `24(%rbp)`, with `%r9` unused.
#[test]
fn the_area_s_address_moves_an_i128_parameter_to_the_stack() {
    let asm = compile(&module(MIXED)).unwrap().module;
    assert_has(
        &asm,
        &[
            "subq\t$64, %rsp",
            "movq\t%rdi, -56(%rbp)",
            "movq\t%rsi, -8(%rbp)",
            "movq\t%rdx, -16(%rbp)",
            "movq\t%rcx, -24(%rbp)",
            "movq\t%r8, -32(%rbp)",
            "movq\t16(%rbp), %rax",
            "movq\t%rax, -48(%rbp)",
            "movq\t24(%rbp), %rax",
            "movq\t%rax, -40(%rbp)",
        ],
    );
}

/// The `i64` at 0, and the `i128` at 16 and 24, past 8 bytes of padding.
#[test]
fn an_i128_next_to_an_i64_goes_in_the_area_at_16() {
    let asm = compile(&module(MIXED)).unwrap().module;
    assert_has(
        &asm,
        &[
            "# ret %d, %x @0",
            "movq\t-56(%rbp), %rax",
            "movq\t-32(%rbp), %rcx",
            "movq\t%rcx, 0(%rax)",
            "movq\t-48(%rbp), %rcx",
            "movq\t%rcx, 16(%rax)",
            "movq\t-40(%rbp), %rcx",
            "movq\t%rcx, 24(%rax)",
            "leave",
        ],
    );
}

/// The caller pushes the `i128` high half first, passes the area's
/// address in `%rdi`, and copies both halves of the `i128` result out of
/// the area into its two slots. Its frame: 13 slots, then 32 bytes of area.
#[test]
fn a_caller_passes_an_i128_on_the_stack_and_copies_both_halves_out() {
    let asm = compile(&module(MIXED)).unwrap().module;
    let caller = asm.split_once("f:\n").unwrap().1;
    assert_has(caller, &["subq\t$144, %rsp", "movq\t%rdi, -96(%rbp)"]);
    assert_has(
        caller,
        &[
            "leaq\t-144(%rbp), %rax",
            "movq\t%rax, -104(%rbp)",
            "pushq\t-40(%rbp)",
            "pushq\t-48(%rbp)",
            "movq\t-104(%rbp), %rdi",
            "movq\t-8(%rbp), %rsi",
            "movq\t-16(%rbp), %rdx",
            "movq\t-24(%rbp), %rcx",
            "movq\t-32(%rbp), %r8",
            "call\tg",
            "addq\t$16, %rsp",
            "movq\t-144(%rbp), %rax",
            "movq\t%rax, -56(%rbp)",
            "movq\t-128(%rbp), %rax",
            "movq\t%rax, -72(%rbp)",
            "movq\t-120(%rbp), %rax",
            "movq\t%rax, -64(%rbp)",
        ],
    );
}

/// `i1, i128, i8`: offsets 0, 16 and 32, the `i1` as 0 or 1.
#[test]
fn narrow_results_on_both_sides_of_an_i128_take_0_16_and_32() {
    let asm = compile(&module(MIXED)).unwrap().module;
    assert_has(
        &asm,
        &[
            "# ret %t, %s, %u @0",
            "movq\t-96(%rbp), %rax",
            "movq\t-80(%rbp), %rcx",
            "andl\t$1, %ecx",
            "movq\t%rcx, 0(%rax)",
            "movq\t-72(%rbp), %rcx",
            "movq\t%rcx, 16(%rax)",
            "movq\t-64(%rbp), %rcx",
            "movq\t%rcx, 24(%rax)",
            "movq\t-88(%rbp), %rcx",
            "movq\t%rcx, 32(%rax)",
            "leave",
        ],
    );
}

const TWO: &str = "func @two(%x: i128, %y: i128) -> i128, i128 {\n^entry:\n  ret %y, %x @0\n}\n\n\
                   func @one(%x: i128, %y: i128) -> i128 {\n^entry:\n  \
                   %p: i128, %q: i128 = call @two %x, %y @0\n  \
                   %r: i128 = call @one %q, %p @0\n  ret %r @0\n}\n";

/// Two `i128`s take four eightbytes, more than `%rax` and `%rdx` hold: they
/// go in the area at 0 and 16, and the arguments move along to `%rsi`.
#[test]
fn two_i128_results_go_in_the_area_at_0_and_16() {
    let asm = compile(&module(TWO)).unwrap().module;
    assert_has(
        &asm,
        &[
            "movq\t%rdi, -40(%rbp)",
            "movq\t%rsi, -16(%rbp)",
            "movq\t%rdx, -8(%rbp)",
            "movq\t%rcx, -32(%rbp)",
            "movq\t%r8, -24(%rbp)",
        ],
    );
    assert_has(
        &asm,
        &[
            "# ret %y, %x @0",
            "movq\t-40(%rbp), %rax",
            "movq\t-32(%rbp), %rcx",
            "movq\t%rcx, 0(%rax)",
            "movq\t-24(%rbp), %rcx",
            "movq\t%rcx, 8(%rax)",
            "movq\t-16(%rbp), %rcx",
            "movq\t%rcx, 16(%rax)",
            "movq\t-8(%rbp), %rcx",
            "movq\t%rcx, 24(%rax)",
        ],
    );
    assert_has(
        &asm,
        &[
            "call\ttwo",
            "movq\t-128(%rbp), %rax",
            "movq\t%rax, -48(%rbp)",
            "movq\t-120(%rbp), %rax",
            "movq\t%rax, -40(%rbp)",
            "movq\t-112(%rbp), %rax",
            "movq\t%rax, -64(%rbp)",
            "movq\t-104(%rbp), %rax",
            "movq\t%rax, -56(%rbp)",
        ],
    );
}

/// One `i128` alone needs no area: it comes back in `%rdx:%rax`, and the
/// arguments start at `%rdi`.
#[test]
fn an_i128_alone_comes_back_in_rdx_and_rax() {
    let asm = compile(&module(TWO)).unwrap().module;
    assert_has(
        &asm,
        &[
            "movq\t-64(%rbp), %rdi",
            "movq\t-56(%rbp), %rsi",
            "movq\t-48(%rbp), %rdx",
            "movq\t-40(%rbp), %rcx",
            "call\tone",
            "movq\t%rax, -80(%rbp)",
            "movq\t%rdx, -72(%rbp)",
            "# ret %r @0",
            "movq\t-80(%rbp), %rax",
            "movq\t-72(%rbp), %rdx",
            "leave",
        ],
    );
}

/// The wrapper gives each `i128` argument and result two slots, and prints
/// an `i128` result from both: its low half in `%rdi`, its high one in
/// `%rdx`.
#[test]
fn the_wrapper_prints_an_i128_among_results_from_both_halves() {
    let entry = compile(&module(MIXED)).unwrap().entry;
    let wrapper = entry.split_once("__funk_entry_0:\n").unwrap().1;
    let wrapper = wrapper.split_once("\tret\n").unwrap().0;
    // Six slots for the arguments, which then hold the three of the
    // results, the slot for the area's address, and the area.
    assert_has(wrapper, &["subq\t$96, %rsp"]);
    assert_has(
        wrapper,
        &[
            "movl\t$4, %edi",
            "movl\t$128, %esi",
            "call\t__funk_rt_arg",
            "movq\t%rax, -48(%rbp)",
            "movq\t%rdx, -40(%rbp)",
            "leaq\t-96(%rbp), %rax",
            "movq\t%rax, -56(%rbp)",
            "pushq\t-40(%rbp)",
            "pushq\t-48(%rbp)",
            "movq\t-56(%rbp), %rdi",
        ],
    );
    assert_has(
        wrapper,
        &[
            "call\tg",
            "addq\t$16, %rsp",
            "movq\t-96(%rbp), %rax",
            "movq\t%rax, -8(%rbp)",
            "movq\t-80(%rbp), %rax",
            "movq\t%rax, -24(%rbp)",
            "movq\t-72(%rbp), %rax",
            "movq\t%rax, -16(%rbp)",
            "movq\t-8(%rbp), %rdi",
            "movl\t$64, %esi",
            "call\t__funk_rt_value",
            "movq\t-24(%rbp), %rdi",
            "movq\t-16(%rbp), %rdx",
            "movl\t$128, %esi",
            "call\t__funk_rt_value",
        ],
    );
}
