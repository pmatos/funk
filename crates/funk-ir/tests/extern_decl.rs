//! External declarations (ADR-2026-11-09-1547), on the texts of
//! `lean/FirTest/Extern.lean`, so the two parsers reject each malformed
//! declaration at the same place and the two validators give the same
//! problems: the text reads back and prints as itself, a header that does
//! not decode is a parse error where it stops, and validation checks the
//! markers, types and memories of the declaration. A call to a declaration
//! stays rejected until the run can make one (#239).

mod common;

use common::{diagnostics, one_func, parse_err, parse_ok};
use funk_ir::{Attr, Def, Extern, Item, Type, print};

fn ext(params: &str, results: &str) -> String {
    one_func(&format!("extern @g({params}){results} {{\n}}\n"))
}

fn messages(text: &str) -> Vec<String> {
    diagnostics(text).into_iter().map(|d| d.message).collect()
}

fn round_trips(text: &str) {
    assert_eq!(print(&parse_ok(text)), text);
}

fn rejected_at(text: &str, col: usize, needle: &str) {
    let e = parse_err(text);
    assert_eq!((e.pos.line, e.pos.col), (1, col), "{text}: {e}");
    assert!(e.reason.contains(needle), "{text}: {e}");
}

#[test]
fn declarations_read_back_as_written() {
    round_trips(&ext("%fmt: ptr, ...", " -> i32"));
    round_trips(&ext("...", ""));
    round_trips(&ext("", ""));
    round_trips(&ext("%c: i8 sext, %n: i32", " -> i8 zext"));
    round_trips(&ext("%a: i16 zext, %b: f64, ...", " -> i32, i1 zext"));
    round_trips(&one_func("extern @\"a b\"(%x: i64) -> ptr {\n}\n"));
    round_trips(&one_func(
        "module @dev() {\n  extern @g(%x: i8 sext) -> i8 {\n  }\n\n}\n",
    ));
    round_trips(&one_func(
        "extern @puts(%s: ptr) -> i32 {\n}\n\nfunc @f() {\n^e:\n  ret @0\n}\n",
    ));
    let m = parse_ok(&ext("%fmt: ptr, %c: i8 sext, ...", " -> i32"));
    let mut want = Extern::new("g");
    want.params = vec![
        Def::new("fmt", Type::word("ptr")),
        Def::new("c", Type::word("i8")),
    ];
    want.results = vec![Type::word("i32")];
    want.param_attrs = vec![Vec::new(), vec![Attr::word("sext")]];
    want.variadic = true;
    assert_eq!(m.items, [Item::Extern(want)]);
}

#[test]
fn malformed_headers_are_rejected_where_they_stop() {
    rejected_at(
        &ext("", " zext"),
        13,
        "an extern with no results has no attributes",
    );
    rejected_at(
        &one_func("extern @g() {\n^e:\n  ret @0\n}\n"),
        1,
        "an extern has an empty body",
    );
    rejected_at(
        &one_func("extern @g() {\n  global @h() size(1) align(1) {\n  }\n\n}\n"),
        1,
        "an extern has an empty body",
    );
    rejected_at(
        &ext("%a: i32, %a: i32", ""),
        20,
        "value %a is defined twice",
    );
    rejected_at(
        &ext("%a: i16777216", ""),
        15,
        "type i16777216 does not decode",
    );
    rejected_at(
        &one_func("externs @g() {\n}\n"),
        1,
        "unknown item kind externs",
    );
    rejected_at(
        &one_func("toy.cell @c(%a: i8 sext) {\n}\n"),
        20,
        "only a func's or an extern's parameters carry attributes",
    );
}

#[test]
fn validation_checks_markers_types_and_memories() {
    assert_eq!(messages(&ext("%fmt: ptr, ...", " -> i32")), [""; 0]);
    assert_eq!(
        messages(&ext("%c: i8 sext, %n: i32", " -> i16 zext")),
        [""; 0]
    );
    assert_eq!(messages(&ext("%b: i1 zext", " -> i1 sext")), [""; 0]);
    let param = ["the attributes of parameter %a are not ones its type allows"];
    assert_eq!(messages(&ext("%a: i32 sext", "")), param);
    assert_eq!(messages(&ext("%a: ptr zext", "")), param);
    assert_eq!(messages(&ext("%a: i8 sext zext", "")), param);
    assert_eq!(messages(&ext("%a: i8 signext", "")), param);
    assert_eq!(
        messages(&ext("", " -> f32 sext")),
        ["the attributes of a result of the declaration are not ones its type allows"]
    );
    assert_eq!(
        messages(&ext("%a: i0", "")),
        ["a type of the declaration is not valid"]
    );
    assert_eq!(
        messages(&ext("%p: ptr(1)", "")),
        ["a type names memory 1, which the data layout does not declare"]
    );
    let declared = format!(
        "layout memory(1, unit(8), pointer(64), little)\n\n{}",
        ext("%p: ptr(1)", "")
    );
    assert_eq!(messages(&declared), [""; 0]);
    assert_eq!(
        messages(&one_func(
            "extern @f() {\n}\n\nfunc @f() {\n^e:\n  ret @0\n}\n"
        )),
        ["the symbol @f names more than one item"]
    );
}

/// A call to a declaration does not validate yet: the run cannot make one
/// until the external call rule (#239).
#[test]
fn a_call_to_a_declaration_is_rejected() {
    let text = one_func(
        "extern @g(%a: i32) -> i32 {\n}\n\nfunc @f(%a: i32) -> i32 {\n^e:\n  %r: i32 = call @g %a @0\n  ret %r @0\n}\n",
    );
    assert_eq!(
        messages(&text),
        [
            "op call refers to @g, which names no function",
            "call @g passes (i32) and defines (i32), but no function is named @g"
        ]
    );
}
