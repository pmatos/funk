//! Texts that follow the grammar but do not decode, and texts that break the
//! grammar or the lexical rules, are parse errors with a position
//! (ADR-2026-10-30-0815; `lean/Fir/Text/Grammar.lean`, "Reading a text").

mod common;

use common::{one_func, parse_err, parse_ok};
use funk_ir::{Registry, TextPos, text::parse_bytes};

/// A function `@f(%a: i32) -> i32` whose entry block holds `ops`, one per
/// line from line 3.
fn func(ops: &[&str]) -> String {
    let body: String = ops.iter().map(|o| format!("  {o}\n")).collect();
    one_func(&format!("func @f(%a: i32) -> i32 {{\n^entry:\n{body}}}\n"))
}

/// Asserts that `text` is rejected at `line:col` for a reason that holds
/// `needle`.
fn rejected_at(text: &str, line: usize, col: usize, needle: &str) {
    let e = parse_err(text);
    assert_eq!(e.pos, TextPos { line, col }, "{e}\n{text}");
    assert!(e.reason.contains(needle), "{e:?} lacks {needle:?}\n{text}");
}

#[test]
fn a_number_out_of_range_is_rejected_at_the_number() {
    rejected_at(&func(&["ret %a @4294967296"]), 3, 11, "out of range");
    parse_ok("func @f() {\n^e:\n  ret @4294967295\n}\n\nlocs {\n  @4294967295 = unknown\n}\n");
    rejected_at("locs {\n  @4294967296 = unknown\n}\n", 2, 4, "out of range");
    rejected_at(
        "locs {\n  @0 = \"f\":4294967296:1 to 1:1\n}\n",
        2,
        12,
        "line 4294967296 is out of range",
    );
    rejected_at(
        "locs {\n  @0 = \"f\":1:1 to 1:99999999999999999999\n}\n",
        2,
        21,
        "column",
    );
    rejected_at(
        &one_func("func @f(%a: i16777216) {\n^e:\n  ret @0\n}\n"),
        1,
        13,
        "above the limit",
    );
    parse_ok(&one_func("func @f(%a: i16777215) {\n^e:\n  ret @0\n}\n"));
}

#[test]
fn a_string_or_symbol_not_in_its_one_spelling_is_rejected() {
    rejected_at(
        &one_func("func @\"sum\"() {\n^e:\n  ret @0\n}\n"),
        1,
        6,
        "is written @sum",
    );
    let quoted = |s: &str| one_func(&format!("func @\"{s}\"() {{\n^e:\n  ret @0\n}}\n"));
    for (s, needle) in [
        ("\\u{41}", "written as itself"),
        ("\\u{9}", "is written '\\t'"),
        ("\\u{a}", "is written '\\n'"),
        ("\\u{001}", "leading zero"),
        ("\\u{1F}", "lowercase hexadecimal"),
        ("\\u{}", "lowercase hexadecimal"),
        ("\\u{d800}", "not a Unicode scalar value"),
        ("\\u{110000}", "not a Unicode scalar value"),
        ("\\x41", "a string escape is"),
        ("\\r", "a string escape is"),
    ] {
        rejected_at(&quoted(s), 1, 8, needle);
    }
    rejected_at(&quoted("a\tb"), 1, 9, "U+0009 must be escaped");
    rejected_at(&quoted("\u{202e}"), 1, 8, "U+202E must be escaped");
    rejected_at(&quoted("\u{85}"), 1, 8, "U+0085 must be escaped");
    rejected_at("locs {\n  @0 = name(\"open\n", 2, 18, "must be escaped");
    rejected_at("locs {\n  @0 = name(\"open", 2, 13, "not closed");
    parse_ok(&quoted("\\u{0}\\u{7f}\\u{2028}\\u{e007f}\\\\\\\""));
}

#[test]
fn an_item_of_an_unknown_kind_is_rejected() {
    rejected_at(
        &one_func("global @g() {\n}\n"),
        1,
        1,
        "unknown item kind global",
    );
    rejected_at(
        &one_func("func @f() inline {\n^e:\n  ret @0\n}\n"),
        1,
        11,
        "no attributes",
    );
    rejected_at(
        &one_func("func @f() {\n  func @g() {\n  }\n}\n"),
        2,
        3,
        "blocks, not items",
    );
    rejected_at(
        &one_func("module @m() {\n  func @g() {\n  }\n}\n"),
        1,
        1,
        "unknown item kind module",
    );
}

#[test]
fn a_type_that_does_not_decode_is_rejected() {
    for (ty, needle) in [
        ("i032", "leading zero"),
        ("i00", "leading zero"),
        ("u8", "not a type"),
        ("index", "not a type"),
        ("i32(1)", "not a type"),
        ("i", "not a type"),
    ] {
        rejected_at(
            &one_func(&format!("func @f(%a: {ty}) {{\n^e:\n  ret @0\n}}\n")),
            1,
            13,
            needle,
        );
    }
    rejected_at(
        &one_func("func @f() -> f32 {\n^e:\n  ret @0\n}\n"),
        1,
        14,
        "not a type",
    );
    rejected_at(
        &func(&["%c: i8x = const 1 @0", "ret %a @0"]),
        3,
        7,
        "not a type",
    );
    parse_ok(&one_func("func @f(%a: i0, %p: ptr) {\n^e:\n  ret @0\n}\n"));
}

#[test]
fn a_value_defined_twice_is_rejected_at_its_second_definition() {
    rejected_at(
        &func(&["%a: i32 = const 1 @0", "ret %a @0"]),
        3,
        3,
        "%a is defined twice",
    );
    rejected_at(
        &func(&["%b: i32 = const 1 @0", "%b: i32 = const 2 @0", "ret %b @0"]),
        4,
        3,
        "%b",
    );
    rejected_at(
        &one_func("func @f(%a: i8, %a: i8) {\n^e:\n  ret @0\n}\n"),
        1,
        17,
        "%a is defined twice",
    );
    let blocks = "func @f(%a: i8) {\n^e:\n  ret @0\n^b(%a: i8):\n  ret @0\n}\n";
    rejected_at(&one_func(blocks), 4, 4, "%a is defined twice");
}

#[test]
fn an_operand_that_the_function_does_not_define_is_rejected() {
    rejected_at(
        &func(&["%c: i32 = add %a, %nope @0", "ret %c @0"]),
        3,
        21,
        "%nope is not defined in @f",
    );
    let two = "func @g(%x: i32) {\n^e:\n  ret @0\n}\n\nfunc @h() -> i32 {\n^e:\n  ret %x @0\n}\n";
    rejected_at(&one_func(two), 8, 7, "%x is not defined in @h");
}

#[test]
fn a_symbol_in_a_parse_error_is_spelled_canonically() {
    let symbol = r#"@"a\nb\u{1b}[31m\u{202e}x""#;
    let text = one_func(&format!("func {symbol}() {{\n^e:\n  ret %x @0\n}}\n"));
    let e = parse_err(&text);
    assert!(
        e.reason.ends_with(&format!("is not defined in {symbol}")),
        "{e:?}"
    );
    assert!(!e.reason.chars().any(funk_ir::text::is_escaped), "{e:?}");
    rejected_at(
        &one_func("func @\"1\"() {\n^e:\n  ret %x @0\n}\n"),
        3,
        7,
        "%x is not defined in @\"1\"",
    );
}

#[test]
fn an_op_that_does_not_decode_is_rejected_at_its_name() {
    for (op, needle) in [
        (
            "%c: i32 = add %a, %b @0",
            "add takes two operands of one integer type",
        ),
        ("%c: i32 = add %a @0", "add takes two operands"),
        ("%c: i32 = add %a, %a, %a @0", "add takes two operands"),
        ("%c: i64 = add %a, %a @0", "add takes two operands"),
        (
            "%c: i32 = add nsw %a, %a @0",
            "flags are not registered yet",
        ),
        (
            "%c: i1 = const 1 @0",
            "an i1 constant is written true or false",
        ),
        (
            "%c: i1 = const -1 @0",
            "an i1 constant is written true or false",
        ),
        ("%c: i8 = const 128 @0", "the constant 128 does not fit i8"),
        ("%c: i8 = const -129 @0", "does not fit i8"),
        ("%c: i8 = const true @0", "true is an i1 constant"),
        ("%c: i8 = const @0", "one attribute"),
        ("%c: i8 = const 1 2 @0", "one attribute"),
        ("%c: i8 = const \"1\" @0", "an integer"),
        ("%c: i8 = const 1 %a @0", "no operands"),
        ("%c: ptr = const 1 @0", "an integer"),
        ("%c: i8, %d: i8 = const 1 @0", "one value"),
        ("%c: i8 = ret @0", "ret defines no values"),
        ("ret nsw %a @0", "ret takes no attributes"),
        ("%c: i8 = sub %a, %a @0", "unknown op sub"),
        ("%c: i8 = toy.mix %a @0", "unknown op toy.mix"),
    ] {
        let b = if op.contains("%b") {
            "%b: i64 = const 0 @0"
        } else {
            "%z: i1 = const true @0"
        };
        let col = op.find(['=']).map_or(3, |i| i + 5);
        rejected_at(&func(&[b, op, "ret %a @0"]), 4, col, needle);
    }
    rejected_at(
        &func(&["%c: i8 = const 99999999999999999999999999999999999999999 @0"]),
        3,
        12,
        "does not fit",
    );
    parse_ok(&func(&[
        "%c: i16777215 = const 99999999999999999999999999999999999999999 @0",
        "ret %a @0",
    ]));
}

#[test]
fn hidden_characters_are_rejected_outside_strings_even_in_comments() {
    let seven = "func @seven() -> i32 {\n^entry:\n  %c: i32 = const 7 @0\n  ret %c @0\n}\n\nlocs {\n  @0 = unknown\n}\n";
    rejected_at(
        &seven.replace('\n', "\r\n"),
        1,
        23,
        "U+000D is not allowed outside strings",
    );
    rejected_at(&format!("\u{feff}{seven}"), 1, 1, "U+FEFF");
    rejected_at(&format!("// \u{202e} reversed\n{seven}"), 1, 4, "U+202E");
    rejected_at(&format!("// \u{2066}\n{seven}"), 1, 4, "U+2066");
    rejected_at(
        &seven.replace("@0\n  ret", "@0 // \u{200e}\n  ret"),
        3,
        27,
        "U+200E",
    );
    rejected_at(&seven.replace("^entry:", "^entry:\u{2028}"), 2, 8, "U+2028");
    rejected_at(&seven.replace("^entry:", "^entry:\u{85}"), 2, 8, "U+0085");
    rejected_at(&seven.replace("^entry:", "^entry:\u{b}"), 2, 8, "U+000B");
    parse_ok(&seven.replace("^entry:", "^entry: // \"quotes\", \\ and é\t"));
    parse_ok(&seven.replace("@0\n  ret", "@0\n\tret"));
}

#[test]
fn tokens_must_not_run_into_name_characters() {
    rejected_at(&func(&["ret %a @1x"]), 3, 11, "must not run into");
    rejected_at(
        &func(&["%c: i32 = const 1.5 @0", "ret %c @0"]),
        3,
        19,
        "float",
    );
    rejected_at(
        &func(&["%c: i32 = const 1abc @0", "ret %c @0"]),
        3,
        19,
        "must not run into",
    );
    rejected_at(
        &func(&["%c: i32 = const 007 @0", "ret %c @0"]),
        3,
        19,
        "leading zeros",
    );
    rejected_at(&func(&["ret %a @01"]), 3, 11, "must not run into");
    rejected_at(
        &func(&["%c: i32 = const -0 @0", "ret %c @0"]),
        3,
        19,
        "-0 is not an integer",
    );
    rejected_at(
        &func(&["%c: i32 = const - 1 @0", "ret %c @0"]),
        3,
        19,
        "negative integer",
    );
    rejected_at(
        &func(&["% c: i32 = const 1 @0"]),
        3,
        3,
        "% must be followed by a value name",
    );
    rejected_at(&func(&["ret %a @ 0"]), 3, 10, "@ must be followed");
    rejected_at(
        &func(&["ret %a @0 #"]),
        3,
        13,
        "unexpected character U+0023",
    );
    rejected_at(
        &func(&["ret %a @0 /"]),
        3,
        13,
        "unexpected character U+002F",
    );
    parse_ok(&func(&["%c: i32 = const-1 @0", "ret %c @0"]));
}

#[test]
fn text_that_breaks_the_grammar_is_rejected() {
    rejected_at("", 1, 1, "the location table");
    rejected_at("locs {\n}\nfunc", 3, 1, "the end of the text");
    rejected_at(&func(&["ret %a"]), 4, 1, "location reference");
    rejected_at(
        &one_func("func @f() {\n^e():\n  ret @0\n}\n"),
        2,
        4,
        "value definition",
    );
    rejected_at(
        &one_func("func @f() {\n^e:\n  ret ^x() @0\n}\n"),
        3,
        10,
        "a value passed to the successor",
    );
    rejected_at(
        &one_func("func @f() {\n^e:\n  ret ^x, %a @0\n}\n"),
        3,
        11,
        "a successor",
    );
    rejected_at(&one_func("func f() {\n}\n"), 1, 6, "symbol");
    rejected_at(
        &one_func("func @f() {\n^e:\n  %x = const 1 @0\n}\n"),
        3,
        6,
        ": and the value's type",
    );
    rejected_at(
        "locs {\n  @0 = somewhere\n}\n",
        2,
        8,
        "not a kind of location",
    );
    rejected_at("locs {\n  @0 = \"f\":-1:1 to 1:1\n}\n", 2, 12, "a line");
    rejected_at(
        "locs {\n  @0 = name(x)\n}\n",
        2,
        13,
        "the name, as a string",
    );
    rejected_at("locs {\n  @0 = fused(@1 @2)\n}\n", 2, 17, ")");
}

#[test]
fn bytes_that_are_not_utf8_are_rejected_where_they_start() {
    let e = parse_bytes(b"locs {\n  @0 = name(\"a\xffb\")\n}\n", &Registry::core()).unwrap_err();
    assert_eq!(e.pos, TextPos { line: 2, col: 15 });
    assert!(e.reason.contains("not UTF-8"));
}
