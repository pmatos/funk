//! A function's signature (#239): the attributes after a parameter's or a
//! result's type, which the dialect of that type reads, and `...` at the end
//! of the parameters (ADR-2026-11-21-1307). The core allows one marker,
//! `sext` or `zext`, on an integer narrower than 32 bits, and no fir
//! function is variadic.

mod common;

use common::{diagnostics, one_func, parse_err, parse_ok, rejects};
use funk_ir::dialects::core::int_type;
use funk_ir::{Attr, Block, Func, LocRef, Location, Module, Op, Registry, print, verify};

/// A module of `f` whose location table has `@0`.
fn module_of(f: Func) -> Module {
    let mut m = Module::new();
    m.locs.push(Location::Unknown);
    m.func(f)
}

/// `@f(%c: i8 sext, %n: i32) -> i8 zext`, which returns `%c`.
fn marked() -> Func {
    Func::new("f")
        .marked_param("c", int_type(8), vec![Attr::word("sext")])
        .param("n", int_type(32))
        .marked_result(int_type(8), vec![Attr::word("zext")])
        .block(Block::new("e").op(Op::new("ret", LocRef(0)).operand("c")))
}

#[test]
fn markers_print_after_their_types_and_read_back() {
    let m = module_of(marked());
    let text = print(&m);
    assert!(
        text.starts_with("func @f(%c: i8 sext, %n: i32) -> i8 zext {\n"),
        "{text}"
    );
    assert_eq!(parse_ok(&text), m);
    assert!(verify(&m, &Registry::core()).is_empty());
}

#[test]
fn a_function_holds_no_empty_lists_of_attributes_at_the_end() {
    let text = one_func("func @f(%a: i8 sext, %b: i8) -> i8, i8 {\n^e:\n  ret %a, %b @0\n}\n");
    let m = parse_ok(&text);
    let funk_ir::Item::Func(f) = &m.items[0] else {
        panic!("{m:?}")
    };
    assert_eq!(f.param_attrs, vec![vec![Attr::word("sext")]]);
    assert!(f.result_attrs.is_empty());
    assert_eq!(f.param_attrs_of(1), &[] as &[Attr]);
}

#[test]
fn the_core_allows_one_marker_on_a_narrow_integer() {
    for ty in ["i1", "i8", "i16", "i31"] {
        for m in ["sext", "zext"] {
            let text = one_func(&format!(
                "func @f(%a: {ty} {m}) -> {ty} {m} {{\n^e:\n  ret %a @0\n}}\n"
            ));
            assert!(diagnostics(&text).is_empty(), "{text}");
        }
    }
    for (ty, m) in [
        ("i32", "sext"),
        ("i64", "zext"),
        ("f32", "zext"),
        ("ptr", "sext"),
        ("i8", "nsw"),
        ("i8", "sext zext"),
        ("i8", "sext(1)"),
    ] {
        let text = one_func(&format!("func @f(%a: {ty} {m}) {{\n^e:\n  ret @0\n}}\n"));
        rejects(
            &text,
            "the attributes of parameter %a are not ones its type allows",
        );
    }
}

#[test]
fn a_fir_function_is_not_variadic() {
    for params in ["...", "%a: i32, ..."] {
        let text = one_func(&format!("func @f({params}) {{\n^e:\n  ret @0\n}}\n"));
        rejects(&text, "a fir function is not variadic");
    }
    let m = module_of(marked().variadic());
    assert!(print(&m).starts_with("func @f(%c: i8 sext, %n: i32, ...) -> i8 zext {\n"));
}

#[test]
fn attributes_held_in_another_form_are_rejected() {
    let mut f = marked();
    f.param_attrs.push(Vec::new());
    let ds = verify(&module_of(f), &Registry::core());
    assert!(
        ds.iter()
            .any(|d| d.message.contains("in another form than the text reads")),
        "{ds:#?}"
    );
}

#[test]
fn only_a_funcs_signature_carries_attributes_or_ends_in_an_ellipsis() {
    for (text, line, column, message) in [
        (
            "func @f(%a: i8) sext {\n}\n",
            1,
            17,
            "a func with no results has no attributes",
        ),
        (
            "module @m(%a: i8 sext) {\n}\n",
            1,
            18,
            "only a func's or an extern's parameters carry attributes",
        ),
        (
            "module @m(...) {\n}\n",
            1,
            11,
            "only a func's or an extern's parameters end in ...",
        ),
        (
            "toy.c @c() -> i8 sext, i8 {\n}\n",
            1,
            18,
            "only a func's or an extern's results carry attributes",
        ),
        ("func @f(..., %a: i8) {\n}\n", 1, 12, "expected ), found ,"),
    ] {
        let e = parse_err(&one_func(text));
        assert_eq!(
            (e.pos.line, e.pos.col, e.reason.as_str()),
            (line, column, message),
            "{text}"
        );
    }
}
