//! The rules of `call` (#20) and how its text fails to decode.
//!
//! `call @f` decodes at any types, so a call that does not match its callee
//! is a validation error: `call f ts rs` is valid when the module's symbol
//! table gives `@f` the type `⟨ts, rs⟩` (`Op.Valid` in
//! `lean/Fir/Core/Validation.lean`), and each symbol an op refers to must
//! name a function (`Func.OpValid` in `lean/Fir/Validation/Rules.lean`). A
//! callee that names no function breaks both, as in the spec. Each
//! diagnostic names the function, the block, the op's index and its
//! location reference.
//!
//! A call without one symbol attribute does not decode, and a use of a
//! value that another function defines is undefined in the caller: both
//! are parse errors with a position (ADR-2026-10-29-2014).

mod common;

use common::{diagnostics, one_func, parse_err};
use funk_ir::dialects::core::int_type;
use funk_ir::{
    Attr, Block, Diagnostic, Func, LocRef, Location, Module, Op, Registry, TextPos, verify,
};

/// `@g(%a: i32, %b: i8) -> i32`, then `@f(%n: i32, %m: i8) -> i32` whose
/// entry block holds `op` at `@1` and returns `%n`. The table has `@0` and
/// `@1`.
fn caller(op: &str) -> String {
    format!(
        "func @g(%a: i32, %b: i8) -> i32 {{\n^entry:\n  ret %a @0\n}}\n\n\
         func @f(%n: i32, %m: i8) -> i32 {{\n^entry:\n  {op} @1\n  ret %n @0\n}}\n\n\
         locs {{\n  @0 = unknown\n  @1 = \"f.c\":1:1 to 1:9\n}}\n"
    )
}

/// A diagnostic about the call, op 0 of `@f`'s entry block, at `@1`.
fn at_call(message: &str) -> Diagnostic {
    Diagnostic {
        message: message.into(),
        func: Some("f".into()),
        block: Some("entry".into()),
        op: Some(0),
        loc: Some(LocRef(1)),
    }
}

/// Asserts that `@f` with the call `op` is rejected with exactly one
/// diagnostic at the call: that the call passes `passes` and defines
/// `defines`, and `@g` does not take and return them.
fn mismatched(op: &str, passes: &str, defines: &str) {
    let why = format!(
        "call @g passes {passes} and defines {defines}, but @g takes (i32, i8) and returns (i32)"
    );
    let text = caller(op);
    assert_eq!(diagnostics(&text), [at_call(&why)], "\n{text}");
}

#[test]
fn a_call_that_matches_its_callee_is_valid() {
    assert_eq!(diagnostics(&caller("%r: i32 = call @g %n, %m")), []);
}

#[test]
fn a_call_of_an_unknown_symbol_breaks_two_rules() {
    for (op, sym, passes, defines) in [
        ("%r: i32 = call @h %n, %m", "@h", "(i32, i8)", "(i32)"),
        ("call @\"g \"", "@\"g \"", "()", "()"),
        ("%r: i8 = call @\"\" %m", "@\"\"", "(i8)", "(i8)"),
        ("call @G %n", "@G", "(i32)", "()"),
    ] {
        let rule = format!(
            "call {sym} passes {passes} and defines {defines}, but no function is named {sym}"
        );
        let refers = format!("op call refers to {sym}, which names no function");
        let text = caller(op);
        assert_eq!(
            diagnostics(&text),
            [at_call(&refers), at_call(&rule)],
            "\n{text}"
        );
    }
}

#[test]
fn a_call_passes_as_many_arguments_as_its_callee_takes() {
    mismatched("%r: i32 = call @g %n", "(i32)", "(i32)");
    mismatched("%r: i32 = call @g", "()", "(i32)");
    mismatched("%r: i32 = call @g %n, %m, %m", "(i32, i8, i8)", "(i32)");
}

#[test]
fn a_call_passes_the_types_its_callee_takes() {
    mismatched("%r: i32 = call @g %n, %n", "(i32, i32)", "(i32)");
    mismatched("%r: i32 = call @g %m, %n", "(i8, i32)", "(i32)");
    mismatched("%r: i32 = call @g %m, %m", "(i8, i8)", "(i32)");
}

#[test]
fn a_call_defines_as_many_values_as_its_callee_returns() {
    mismatched("call @g %n, %m", "(i32, i8)", "()");
    mismatched(
        "%r: i32, %s: i32 = call @g %n, %m",
        "(i32, i8)",
        "(i32, i32)",
    );
}

#[test]
fn a_call_defines_values_of_the_types_its_callee_returns() {
    mismatched("%r: i8 = call @g %n, %m", "(i32, i8)", "(i8)");
    mismatched("%r: i64 = call @g %n, %m", "(i32, i8)", "(i64)");
}

#[test]
fn a_recursive_call_matches_its_own_function() {
    let text = caller("%r: i32 = call @f %n, %m");
    assert_eq!(diagnostics(&text), []);
    let text = caller("%r: i32 = call @f %n");
    let why = "call @f passes (i32) and defines (i32), but @f takes (i32, i8) and returns (i32)";
    assert_eq!(diagnostics(&text), [at_call(why)]);
}

#[test]
fn a_symbol_names_the_first_function_with_it() {
    // Both validation and the spec's symbol table take the first function
    // of a symbol (`Module.symbols`); the second breaks the rule that
    // symbols are unique.
    let text = one_func(
        "func @g(%a: i8) -> i8 {\n^entry:\n  ret %a @0\n}\n\n\
         func @g(%a: i32) -> i32 {\n^entry:\n  ret %a @0\n}\n\n\
         func @f(%x: i8) -> i8 {\n^entry:\n  %y: i8 = call @g %x @0\n  ret %y @0\n}\n",
    );
    let ds = diagnostics(&text);
    assert_eq!(ds.len(), 1, "{ds:#?}");
    assert_eq!(ds[0].message, "the symbol @g names more than one item");
}

#[test]
fn a_symbol_names_its_first_function_after_a_module() {
    // A nested module before a function of the same symbol does not hide
    // it: the spec's symbol table holds functions alone
    // (`SymbolTable.symbols`), so the call checks against @g.
    let text = one_func(
        "module @g() {\n}\n\n\
         func @g(%a: i8) -> i8 {\n^entry:\n  ret %a @0\n}\n\n\
         func @f(%x: i8) -> i8 {\n^entry:\n  %y: i8 = call @g %x @0\n  ret %y @0\n}\n",
    );
    let ds = diagnostics(&text);
    assert_eq!(ds.len(), 1, "{ds:#?}");
    assert_eq!(ds[0].message, "the symbol @g names more than one item");
}

/// A module of `@g() -> i32` and `@f(%n: i32) -> i32`, whose entry block
/// holds `op` and then returns `%n`, built with the builder.
fn built(op: Op) -> Module {
    let i32 = int_type(32);
    let mut m = Module::new();
    let l = m.locs.push(Location::Unknown);
    let g = Func::new("g").result(i32.clone()).block(
        Block::new("entry")
            .op(Op::new("const", l)
                .attr(Attr::int(1))
                .result("c", i32.clone()))
            .op(Op::new("ret", l).operand("c")),
    );
    let f = Func::new("f").param("n", i32.clone()).result(i32).block(
        Block::new("entry")
            .op(op)
            .op(Op::new("ret", l).operand("n")),
    );
    m.func(g).func(f)
}

#[test]
fn the_verifier_rejects_a_built_call_that_does_not_decode() {
    let call = || Op::new("call", LocRef(0)).result("r", int_type(32));
    for (op, why) in [
        (call(), "call takes one attribute, its callee's symbol"),
        (call().attr(Attr::word("g")), "call takes one attribute"),
        (
            call().attr(Attr::Str("g".into())),
            "call takes one attribute",
        ),
        (
            call()
                .attr(Attr::Sym("g".into()))
                .attr(Attr::Sym("g".into())),
            "call takes one attribute",
        ),
    ] {
        let ds = verify(&built(op), &Registry::core());
        assert_eq!(ds.len(), 1, "{ds:#?}");
        let d = &ds[0];
        assert!(
            d.message
                .starts_with(&format!("op call does not match its registration: {why}")),
            "{d}"
        );
        let place = (d.func.as_deref(), d.block.as_deref(), d.op, d.loc);
        assert_eq!(place, (Some("f"), Some("entry"), Some(0), Some(LocRef(0))));
    }
}

#[test]
fn the_verifier_rejects_a_built_call_that_does_not_match_its_callee() {
    let call = Op::new("call", LocRef(0))
        .attr(Attr::Sym("g".into()))
        .operand("n")
        .result("r", int_type(8));
    let ds = verify(&built(call), &Registry::core());
    let why = "call @g passes (i32) and defines (i8), but @g takes () and returns (i32)";
    assert_eq!(ds.len(), 1, "{ds:#?}");
    assert_eq!(ds[0].message, why);
    assert_eq!((ds[0].op, ds[0].loc), (Some(0), Some(LocRef(0))));
    let ok = Op::new("call", LocRef(0))
        .attr(Attr::Sym("g".into()))
        .result("r", int_type(32));
    assert_eq!(verify(&built(ok), &Registry::core()), []);
}

/// Asserts that the parser rejects `@f` with `op` at the position of the
/// first occurrence of `at` in `op`, for a reason that holds `needle`.
fn rejected_at(op: &str, at: &str, needle: &str) {
    let text = caller(op);
    let e = parse_err(&text);
    let col = 3 + op.find(at).expect("the op holds `at`");
    assert_eq!(e.pos, TextPos { line: 8, col }, "{op}: {e}");
    assert!(e.reason.contains(needle), "{op}: {e} lacks {needle:?}");
}

#[test]
fn a_call_without_one_symbol_does_not_decode() {
    let why = "op call does not decode: call takes one attribute, its callee's symbol";
    for op in [
        "%r: i32 = call %n, %m",
        "call",
        "%r: i32 = call g %n, %m",
        "%r: i32 = call \"g\" %n, %m",
        "%r: i32 = call 7 %n, %m",
        "%r: i32 = call @g @g %n, %m",
        "%r: i32 = call @g nsw %n, %m",
        "%r: i32 = call g(@g) %n, %m",
    ] {
        rejected_at(op, "call", why);
    }
}

#[test]
fn a_call_of_another_function_s_value_does_not_decode() {
    // `%a` is `@g`'s parameter: in `@f` it is undefined, and functions are
    // isolated from above (ADR-2026-10-29-2011).
    let why = "value %a is not defined in @f";
    rejected_at("%r: i32 = call @g %a, %m", "%a", why);
    rejected_at("%r: i32 = call @g %n, %a", "%a", why);
    rejected_at("%r: i32 = add %a, %n", "%a", why);
}

#[test]
fn a_location_reference_is_never_a_callee() {
    // `@1` is always a location reference; the function named `1` is
    // `@"1"`.
    let e = parse_err(&caller("%r: i32 = call @1 %n, %m"));
    assert_eq!(e.pos.line, 8, "{e}");
}
