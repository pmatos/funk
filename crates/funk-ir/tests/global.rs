//! Globals (ADR-2026-11-09-1546, ADR-2026-11-19-0124), on the texts of
//! `lean/FirTest/Global.lean`, so the two parsers reject each malformed
//! global at the same place and the two validators give the same problems:
//! the text reads back and prints as itself, an attribute that does not
//! decode is a parse error at the attribute, and validation checks the
//! global's memory, alignment, units, addresses and size, in memory 0 and
//! in a memory of 16-bit units.

mod common;

use common::{diagnostics, one_func, parse_err, parse_ok};
use funk_ir::{Global, InitPiece, Int, Item, Linkage, print};

fn glob(attrs: &str) -> String {
    one_func(&format!("global @g() {attrs} {{\n}}\n"))
}

fn glob_in(layout: &str, attrs: &str) -> String {
    format!("layout {layout}\n\n{}", glob(attrs))
}

fn globs(a: &str, g: &str) -> String {
    one_func(&format!(
        "global @a() {a} {{\n}}\n\nglobal @g() {g} {{\n}}\n"
    ))
}

const MEM16: &str = "memory(1, unit(16), pointer(32), little)";

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

fn size_over(units: u64, size: u64) -> String {
    format!("the initializer takes {units} units, more than the global's size, {size}")
}

#[test]
fn globals_read_back_as_written() {
    round_trips(&glob("size(8) align(1) const units(104, 105, 0)"));
    round_trips(&glob("size(0) align(1)"));
    round_trips(&glob("size(4) align(4) const export units(1, 0, 0, 0)"));
    round_trips(&glob("size(16) align(8) export zeros(8) addr(@g)"));
    round_trips(&globs(
        "size(4) align(4) units(7) zeros(3)",
        "size(16) align(8) addr(@a) addr(@a, 2)",
    ));
    round_trips(&glob_in(
        MEM16,
        "memory(1) size(4) align(2) units(65535) addr(@g, 1)",
    ));
    round_trips(&glob(
        "size(1) align(1) units(340282366920938463463374607431768211456)",
    ));
    round_trips(&glob("size(18446744073709551615) align(1)"));
    round_trips(&format!(
        "global @\"a b\"() size(8) align(8) addr(@\"a b\") {{\n}}\n\n{}",
        one_func("func @f() {\n^e:\n  ret @0\n}\n")
    ));
    round_trips(&one_func(
        "module @dev() {\n  global @g() size(1) align(1) units(1) {\n  }\n\n}\n",
    ));
    let m = parse_ok(&glob("size(2) align(2)"));
    let mut want = Global::new("g", 0, 2, 2);
    assert_eq!(m.items, [Item::Global(want.clone())]);
    let m = parse_ok(&glob("size(4) align(4) const export units(1) addr(@g, 2)"));
    want = Global::new("g", 0, 4, 4);
    want.constant = true;
    want.linkage = Linkage::Exported;
    want.init = vec![
        InitPiece::Units(vec![Int::from(1)]),
        InitPiece::Addr("g".into(), 2),
    ];
    assert_eq!(m.items, [Item::Global(want)]);
}

/// The global's words are the core's too (#237 Q4): a global sits beside
/// `alloca`'s kind `global` and the op `const` in one module, and each
/// reads back as itself (`beside` in `lean/FirTest/Global.lean`).
#[test]
fn a_global_sits_beside_the_core_words_it_shares() {
    let text = one_func(concat!(
        "global @g() size(4) align(4) const units(1, 0, 0, 0) {\n}\n\n",
        "func @f() -> i32 {\n^e:\n  %p: ptr = alloca global i32 @0\n",
        "  %c: i32 = const 1 @0\n  ret %c @0\n}\n",
    ));
    round_trips(&text);
    let m = parse_ok(&text);
    let mut want = Global::new("g", 0, 4, 4);
    want.constant = true;
    want.init = vec![InitPiece::Units(
        [1, 0, 0, 0].into_iter().map(Int::from).collect(),
    )];
    assert_eq!(m.items.first(), Some(&Item::Global(want)));
    assert_eq!(
        messages(&text),
        ["alloca allocates on the stack in M1, not as global: global and heap are hooks"]
    );
}

#[test]
fn attributes_that_do_not_decode_fail_where_the_spec_says() {
    rejected_at(
        &glob("memory(0) size(1) align(1)"),
        13,
        "writes memory(N) first",
    );
    rejected_at(
        &glob("memory(-1) size(1) align(1)"),
        13,
        "writes memory(N) first",
    );
    rejected_at(&glob("align(1) size(1)"), 13, "writes size(S)");
    rejected_at(&glob("size(-1) align(1)"), 13, "writes size(S)");
    rejected_at(&glob("size(1) align(a)"), 21, "writes align(A)");
    rejected_at(
        &glob("memory(1) size(1) align(18446744073709551616)"),
        31,
        "writes align(A)",
    );
    rejected_at(&glob("size(1)"), 1, "writes size(S) and align(A)");
    rejected_at(&glob("size(1) align(1) export const"), 37, "not a piece");
    rejected_at(&glob("size(1) align(1) const const"), 36, "not a piece");
    rejected_at(&glob("size(1) align(1) units(1) const"), 39, "not a piece");
    for piece in [
        "addr(@g, 0)",
        "addr(g)",
        "units(-1)",
        "zeros(18446744073709551616)",
        "bytes(1)",
    ] {
        rejected_at(
            &glob(&format!("size(1) align(1) {piece}")),
            30,
            "not a piece",
        );
    }
    rejected_at(
        &one_func("global @g(%x: i8) size(1) align(1) {\n}\n"),
        11,
        "a global has no parameters",
    );
    rejected_at(
        &one_func("global @g() -> i8 size(1) align(1) {\n}\n"),
        16,
        "a global has no results",
    );
    rejected_at(
        &one_func("global @g() size(1) align(1) {\n^e:\n  ret @0\n}\n"),
        1,
        "a global has an empty body",
    );
}

#[test]
fn validation_checks_the_initializer() {
    assert!(messages(&glob("size(8) align(1) const units(104, 105, 0)")).is_empty());
    assert!(messages(&glob("size(0) align(1)")).is_empty());
    assert!(
        messages(&globs(
            "size(4) align(4) units(7)",
            "size(16) align(8) addr(@a) addr(@a, 4)"
        ))
        .is_empty()
    );
    assert!(messages(&glob("size(16) align(8) addr(@g) addr(@g, 8)")).is_empty());
    assert_eq!(
        messages(&glob("size(2) align(1) units(1, 2, 3)")),
        [size_over(3, 2)]
    );
    assert_eq!(
        messages(&glob("size(4) align(4) zeros(5)")),
        [size_over(5, 4)]
    );
    assert_eq!(
        messages(&glob("size(8) align(8) units(1) addr(@g)")),
        [size_over(9, 8)]
    );
    assert_eq!(
        messages(&glob("size(2) align(1) units(255, 256)")),
        ["the unit 256 of the initializer does not fit in 8 bits"]
    );
    assert_eq!(
        messages(&glob("size(8) align(8) addr(@h)")),
        ["the initializer's address of @h names no global of its table"]
    );
    assert_eq!(
        messages(&one_func(
            "global @g() size(8) align(8) addr(@f) {\n}\n\nfunc @f() {\n^e:\n  ret @0\n}\n"
        )),
        ["the initializer's address of @f names no global of its table"]
    );
    assert_eq!(
        messages(&one_func(
            "global @a() size(1) align(1) {\n}\n\nmodule @dev() {\n  global @g() size(8) align(8) addr(@a) {\n  }\n\n}\n"
        )),
        ["the initializer's address of @a names no global of its table"]
    );
}

#[test]
fn validation_checks_the_memory_alignment_and_symbols() {
    assert_eq!(
        messages(&glob("memory(1) size(1) align(1)")),
        ["the global lives in memory 1, which the data layout does not declare"]
    );
    for a in [3, 16_777_216] {
        assert_eq!(
            messages(&glob(&format!("size(1) align({a})"))),
            [format!(
                "the global is aligned to {a} units: an alignment is a power of two no larger than 16777215"
            )]
        );
    }
    assert_eq!(
        messages(&one_func(
            "global @f() size(1) align(1) {\n}\n\nfunc @f() {\n^e:\n  ret @0\n}\n"
        )),
        ["the symbol @f names more than one item"]
    );
    assert_eq!(
        messages(&one_func(
            "module @dev() {\n  global @g() memory(1) size(1) align(1) {\n  }\n\n}\n"
        )),
        ["the global lives in memory 1, which the data layout does not declare"]
    );
}

#[test]
fn a_memory_of_16_bit_units_counts_its_own_units() {
    assert!(
        messages(&glob_in(
            MEM16,
            "memory(1) size(3) align(2) units(65535) addr(@g, 1)"
        ))
        .is_empty()
    );
    assert_eq!(
        messages(&glob_in(MEM16, "memory(1) size(1) align(1) units(65536)")),
        ["the unit 65536 of the initializer does not fit in 16 bits"]
    );
    assert!(messages(&glob_in(MEM16, "memory(1) size(4) align(1) zeros(4)")).is_empty());
    assert_eq!(
        messages(&format!(
            "layout {MEM16}\n\n{}",
            globs("size(1) align(1)", "memory(1) size(3) align(1) addr(@a)")
        )),
        [size_over(4, 3)]
    );
}
