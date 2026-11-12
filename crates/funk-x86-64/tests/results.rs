//! How `ret` and `call` move any number of results (#31,
//! ADR-2026-10-30-1232): one or two eightbytes in `%rax` and `%rdx`, more
//! in a result area at the bottom of the caller's frame, whose address the
//! call passes first, so that the callee's parameters move along by one. A
//! result of a width that the backend does not lower is reported where it
//! is defined.

use funk_ir::{LocRef, Module, Registry, parse};
use funk_x86_64::compile;

fn module(funcs: &str) -> Module {
    let text = format!("{funcs}\nlocs {{\n  @0 = unknown\n  @1 = \"r.c\":2:3 to 2:9\n}}\n");
    parse(&text, &Registry::core()).unwrap_or_else(|e| panic!("{e}\n{text}"))
}

fn lowered(funcs: &str) -> String {
    compile(&module(funcs))
        .unwrap_or_else(|ds| panic!("{ds:#?}"))
        .module
}

fn assert_has(asm: &str, lines: &[&str]) {
    let want: String = lines.iter().map(|l| format!("\t{l}\n")).collect();
    assert!(asm.contains(&want), "{want}\nnot in\n{asm}");
}

const PAIR: &str = "func @pair(%a: i64, %b: i1) -> i64, i1 {\n^entry:\n  ret %a, %b @0\n}\n\n\
                    func @use(%a: i64, %b: i1) -> i1 {\n^entry:\n  \
                    %x: i64, %y: i1 = call @pair %a, %b @0\n  ret %y @0\n}\n";

#[test]
fn two_results_come_back_in_rax_and_rdx() {
    let asm = lowered(PAIR);
    assert_has(
        &asm,
        &[
            "# ret %a, %b @0",
            "movq\t-8(%rbp), %rax",
            "movq\t-16(%rbp), %rdx",
            "andl\t$1, %edx",
            "leave",
        ],
    );
    assert_has(
        &asm,
        &[
            "call\tpair",
            "movq\t%rax, -24(%rbp)",
            "movq\t%rdx, -32(%rbp)",
            "# ret %y @0",
        ],
    );
}

const TRIPLE: &str = "func @triple(%a: i8, %b: i16) -> i16, i8, i1 {\n^entry:\n  \
                      %t: i1 = const true @0\n  ret %b, %a, %t @0\n}\n\n\
                      func @use(%a: i8, %b: i16) -> i8 {\n^entry:\n  \
                      %x: i16, %y: i8, %z: i1 = call @triple %a, %b @0\n  ret %y @0\n}\n";

/// The address of the area arrives in `%rdi` and is kept in the slot after
/// the values; `ret` writes each result there and returns the address.
#[test]
fn more_results_go_in_the_area_whose_address_arrives_first() {
    let asm = lowered(TRIPLE);
    assert_has(
        &asm,
        &[
            "subq\t$32, %rsp",
            "movq\t%rdi, -32(%rbp)",
            "movq\t%rsi, -8(%rbp)",
            "movq\t%rdx, -16(%rbp)",
        ],
    );
    assert_has(
        &asm,
        &[
            "# ret %b, %a, %t @0",
            "movq\t-32(%rbp), %rax",
            "movq\t-16(%rbp), %rcx",
            "movq\t%rcx, 0(%rax)",
            "movq\t-8(%rbp), %rcx",
            "movq\t%rcx, 8(%rax)",
            "movq\t-24(%rbp), %rcx",
            "andl\t$1, %ecx",
            "movq\t%rcx, 16(%rax)",
            "leave",
        ],
    );
}

/// The caller's frame holds its five values, the slot for the area's
/// address and, at its bottom, the area of 32 bytes: 48 + 32 bytes.
#[test]
fn a_caller_passes_the_area_in_its_frame_and_copies_each_result_out() {
    let asm = lowered(TRIPLE);
    let caller = asm.split_once("use:\n").unwrap().1;
    assert_has(
        caller,
        &[
            "subq\t$80, %rsp",
            "movq\t%rdi, -8(%rbp)",
            "movq\t%rsi, -16(%rbp)",
        ],
    );
    assert_has(
        caller,
        &[
            "leaq\t-80(%rbp), %rax",
            "movq\t%rax, -48(%rbp)",
            "movq\t-48(%rbp), %rdi",
            "movq\t-8(%rbp), %rsi",
            "movq\t-16(%rbp), %rdx",
            "call\ttriple",
            "movq\t-80(%rbp), %rax",
            "movq\t%rax, -24(%rbp)",
            "movq\t-72(%rbp), %rax",
            "movq\t%rax, -32(%rbp)",
            "movq\t-64(%rbp), %rax",
            "movq\t%rax, -40(%rbp)",
            "# ret %y @0",
        ],
    );
}

/// With the area's address first, a sixth argument goes on the stack, and
/// the callee reads it there.
#[test]
fn the_area_s_address_moves_the_sixth_argument_to_the_stack() {
    let params = (0..6)
        .map(|k| format!("%p{k}: i32"))
        .collect::<Vec<_>>()
        .join(", ");
    let args = (0..6)
        .map(|k| format!("%p{k}"))
        .collect::<Vec<_>>()
        .join(", ");
    let asm = lowered(&format!(
        "func @g({params}) -> i32, i32, i32 {{\n^entry:\n  ret %p5, %p4, %p0 @0\n}}\n\n\
         func @f({params}) -> i32 {{\n^entry:\n  \
         %x: i32, %y: i32, %z: i32 = call @g {args} @0\n  ret %x @0\n}}\n"
    ));
    assert_has(
        &asm,
        &[
            "movq\t%rdi, -56(%rbp)",
            "movq\t%rsi, -8(%rbp)",
            "movq\t%rdx, -16(%rbp)",
            "movq\t%rcx, -24(%rbp)",
            "movq\t%r8, -32(%rbp)",
            "movq\t%r9, -40(%rbp)",
            "movq\t16(%rbp), %rax",
            "movq\t%rax, -48(%rbp)",
        ],
    );
    assert_has(
        &asm,
        &[
            "subq\t$8, %rsp",
            "pushq\t-48(%rbp)",
            "movq\t-80(%rbp), %rdi",
            "movq\t-8(%rbp), %rsi",
            "movq\t-16(%rbp), %rdx",
            "movq\t-24(%rbp), %rcx",
            "movq\t-32(%rbp), %r8",
            "movq\t-40(%rbp), %r9",
            "call\tg",
            "addq\t$16, %rsp",
        ],
    );
}

/// A function with no result or one result, and a call of one, compile as
/// before the convention for more.
#[test]
fn no_result_and_one_result_need_no_area() {
    let asm = lowered(
        "func @one(%a: i1) -> i1 {\n^entry:\n  ret %a @0\n}\n\n\
         func @none(%a: i1) {\n^entry:\n  %b: i1 = call @one %a @0\n  call @none %b @0\n  ret @0\n}\n",
    );
    assert_has(&asm, &["subq\t$16, %rsp", "movq\t%rdi, -8(%rbp)"]);
    assert_has(
        &asm,
        &[
            "# ret %a @0",
            "movq\t-8(%rbp), %rax",
            "andl\t$1, %eax",
            "leave",
        ],
    );
    assert_has(
        &asm,
        &[
            "call\tone",
            "movq\t%rax, -16(%rbp)",
            "# call @none %b @0",
            "movq\t-16(%rbp), %rdi",
            "call\tnone",
            "# ret @0",
            "leave",
        ],
    );
    assert!(!asm.contains("leaq"), "{asm}");
}

/// Each type the backend does not lower, an integer width or a float format,
/// is reported once, where its value is defined: a call's result at the
/// call, with its location.
#[test]
fn a_result_of_a_width_the_backend_does_not_lower_is_reported_at_its_op() {
    for t in ["i7", "i256", "f16", "bf16", "f128", "float(5, 2)"] {
        let why =
            format!("the x86-64 backend lowers i1, i8, i16, i32, i64, i128, f32 and f64, not {t}");
        let m = module(&format!(
            "func @g(%a: i64, %b: {t}) -> i64, {t}, i64 {{\n^entry:\n  ret %a, %b, %a @0\n}}\n\n\
             func @f(%a: i64, %b: {t}) -> i64 {{\n^entry:\n  \
             %x: i64, %y: {t}, %z: i64 = call @g %a, %b @1\n  ret %z @0\n}}\n"
        ));
        let ds = compile(&m).unwrap_err();
        let at: Vec<_> = ds
            .iter()
            .map(|d| (d.func.as_deref(), d.op, d.loc, d.message.as_str()))
            .collect();
        let param = format!("parameter %b: {why}");
        let result = format!("%y: {why}");
        assert_eq!(
            at,
            [
                (Some("g"), None, Some(LocRef(0)), param.as_str()),
                (Some("f"), None, Some(LocRef(1)), param.as_str()),
                (Some("f"), Some(0), Some(LocRef(1)), result.as_str()),
            ],
            "{t}: {ds:#?}"
        );
    }
}

/// The entry wrapper provides an area too, and prints every result.
#[test]
fn the_wrapper_passes_an_area_and_prints_every_result_in_order() {
    let entry = compile(&module(TRIPLE)).unwrap().entry;
    let wrapper = entry.split_once("__funk_entry_0:\n").unwrap().1;
    let wrapper = wrapper.split_once("\tret\n").unwrap().0;
    // Two argument slots, which then hold results, a third result slot,
    // the slot for the area's address, and the area.
    assert_has(wrapper, &["subq\t$64, %rsp"]);
    assert_has(
        wrapper,
        &[
            "leaq\t-64(%rbp), %rax",
            "movq\t%rax, -32(%rbp)",
            "movq\t-32(%rbp), %rdi",
            "movq\t-8(%rbp), %rsi",
            "movq\t-16(%rbp), %rdx",
            "call\ttriple",
            "movq\t-64(%rbp), %rax",
            "movq\t%rax, -8(%rbp)",
        ],
    );
    let printed: Vec<&str> = wrapper
        .lines()
        .filter(|l| l.starts_with("\tmovl\t$") && l.ends_with(", %esi"))
        .collect();
    assert_eq!(
        printed,
        [
            "\tmovl\t$8, %esi",
            "\tmovl\t$16, %esi",
            "\tmovl\t$16, %esi",
            "\tmovl\t$8, %esi",
            "\tmovl\t$1, %esi",
        ]
    );
    assert_eq!(wrapper.matches("call\t__funk_rt_value").count(), 3);
}
