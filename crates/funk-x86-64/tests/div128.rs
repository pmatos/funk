//! How `sdiv`, `udiv`, `srem` and `urem` are lowered at `i128` (#22): a
//! call of a System V routine of the runtime helper, with the operands in
//! `%rsi:%rdi` and `%rcx:%rdx` and the result in `%rdx:%rax`
//! (ADR-2026-11-03-0415), and the helper once at the end of the module's
//! assembly, under local symbols, when a function calls it
//! (ADR-2026-11-03-0414).

use funk_ir::{Registry, parse};
use funk_x86_64::compile;

/// The assembly of the module of the functions `funcs`.
fn lowered(funcs: &str) -> String {
    let text = format!("{funcs}\nlocs {{\n  @0 = unknown\n}}\n");
    compile(&parse(&text, &Registry::core()).unwrap_or_else(|e| panic!("{e}\n{text}")))
        .unwrap_or_else(|ds| panic!("{ds:#?}"))
        .module
}

/// `@NAME(%a: TY, %b: TY) -> TY` with the one op `OP %a, %b`, whose result
/// is `%r`.
fn divides(name: &str, ty: &str, op: &str) -> String {
    format!(
        "func @{name}(%a: {ty}, %b: {ty}) -> {ty} {{\n^entry:\n  %r: {ty} = {op} %a, %b @0\n  \
         ret %r @0\n}}\n"
    )
}

/// The labels that the helper defines, in order.
const ROUTINES: [&str; 6] = [
    "__funk_rt_udivmod128:",
    "__funk_rt_udiv128:",
    "__funk_rt_urem128:",
    "__funk_rt_sdiv128:",
    "__funk_rt_srem128:",
    "__funk_rt_magnitudes:",
];

/// Each op loads `%a` (at `-16(%rbp)` and `-8(%rbp)`) into `%rdi` and
/// `%rsi`, `%b` (at `-32(%rbp)` and `-24(%rbp)`) into `%rdx` and `%rcx`,
/// calls its routine, and stores `%rax` and `%rdx` into `%r`, the same
/// with `exact` as without.
#[test]
fn each_op_calls_its_routine_with_the_operands_in_system_v_registers() {
    for (op, routine) in [
        ("sdiv", "__funk_rt_sdiv128"),
        ("sdiv exact", "__funk_rt_sdiv128"),
        ("udiv", "__funk_rt_udiv128"),
        ("udiv exact", "__funk_rt_udiv128"),
        ("srem", "__funk_rt_srem128"),
        ("urem", "__funk_rt_urem128"),
    ] {
        let asm = lowered(&divides("f", "i128", op));
        let want = format!(
            "\t# %r: i128 = {op} %a, %b @0\n\
             \tmovq\t-16(%rbp), %rdi\n\
             \tmovq\t-8(%rbp), %rsi\n\
             \tmovq\t-32(%rbp), %rdx\n\
             \tmovq\t-24(%rbp), %rcx\n\
             \tcall\t{routine}\n\
             \tmovq\t%rax, -48(%rbp)\n\
             \tmovq\t%rdx, -40(%rbp)\n\
             \t# ret %r @0\n"
        );
        assert!(asm.contains(&want), "{want}\nnot in\n{asm}");
    }
}

/// The helper comes once, after every function and before the note on
/// the stack, however many functions divide at `i128`; none of its
/// symbols is global.
#[test]
fn the_helper_follows_the_functions_once() {
    let funcs = [
        divides("q", "i128", "sdiv"),
        divides("m", "i64", "urem"),
        divides("r", "i128", "urem"),
        divides("e", "i128", "udiv exact"),
    ]
    .concat();
    let asm = lowered(&funcs);
    for label in ROUTINES {
        assert_eq!(asm.matches(&format!("\n{label}\n")).count(), 1, "{label}");
    }
    let helper = asm.find("\n__funk_rt_udivmod128:\n").unwrap();
    let last = asm.find("\ne:\n").unwrap();
    let note = asm.find(".note.GNU-stack").unwrap();
    assert!(last < helper && helper < note, "{asm}");
    assert!(!asm.contains(".globl\t__funk_rt"), "{asm}");
    assert_eq!(asm.matches("\t.globl\t").count(), 4, "{asm}");
}

/// A module with no division at `i128` gets no helper, whatever else it
/// divides.
#[test]
fn a_module_that_does_not_divide_at_i128_has_no_helper() {
    let mut funcs = String::new();
    for (k, ty) in ["i1", "i8", "i16", "i32", "i64"].iter().enumerate() {
        for (j, op) in ["sdiv", "udiv", "srem", "urem"].iter().enumerate() {
            funcs += &divides(&format!("f{k}_{j}"), ty, op);
        }
    }
    funcs += "func @wide(%a: i128, %b: i128) -> i128 {\n^entry:\n  %r: i128 = mul %a, %b @0\n  \
              ret %r @0\n}\n";
    let asm = lowered(&funcs);
    assert!(!asm.contains("__funk_rt"), "{asm}");
}

/// A function named as a routine of the helper has the symbol that
/// `abi::symbol` gives a name that starts with `_`, so the call of the
/// routine and the helper's own label stay the helper's.
#[test]
fn a_function_named_as_a_routine_keeps_a_symbol_of_its_own() {
    let funcs = [
        divides("__funk_rt_sdiv128", "i128", "sdiv"),
        "func @call(%a: i128, %b: i128) -> i128 {\n^entry:\n  \
         %r: i128 = call @__funk_rt_sdiv128 %a, %b @0\n  ret %r @0\n}\n"
            .to_string(),
    ]
    .concat();
    let asm = lowered(&funcs);
    let sym = "__funk_sym_5f5f66756e6b5f72745f73646976313238";
    assert!(asm.contains(&format!("\t.globl\t{sym}\n")), "{asm}");
    assert_eq!(asm.matches(&format!("\n{sym}:\n")).count(), 1, "{asm}");
    assert_eq!(asm.matches("\n__funk_rt_sdiv128:\n").count(), 1, "{asm}");
    assert_eq!(asm.matches("\tcall\t__funk_rt_sdiv128\n").count(), 1);
    assert_eq!(asm.matches(&format!("\tcall\t{sym}\n")).count(), 1);
}
