//! Aggregates' layouts (ADR-2026-11-16-1546), on the texts of
//! `lean/FirTest/Aggregate.lean`, so the two parsers reject each malformed
//! layout at the same place and the two validators give the same problems:
//! the text reads back and prints as itself, an attribute that does not
//! decode is a parse error at the attribute, and validation checks the
//! layout's memory, alignment, types and fields, in memory 0 and in a
//! memory of 16-bit units.

mod common;

use common::{diagnostics, one_func, parse_err, parse_ok};
use funk_ir::{Aggregate, Item, Type, print};

fn agg(attrs: &str) -> String {
    one_func(&format!("aggregate @s() {attrs} {{\n}}\n"))
}

fn agg_in(layout: &str, attrs: &str) -> String {
    format!("layout {layout}\n\n{}", agg(attrs))
}

const PAIR: &str = "memory(0) size(16) align(8) field(0, i64) field(8, ptr)";
const MEM16: &str = "memory(1, unit(16), pointer(32), little)";

fn field_at(o: u64, s: &str) -> String {
    format!("the field at offset {o} {s}")
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
fn layouts_read_back_as_written() {
    round_trips(&agg(PAIR));
    round_trips(&agg("memory(0) size(16) align(4) field(0, i24, 4)"));
    round_trips(&agg("memory(0) size(0) align(1)"));
    round_trips(&agg(
        "memory(0) size(4) align(4) field(0, i32) field(4, i32, 0)",
    ));
    round_trips(&agg("memory(0) size(18446744073709551615) align(1)"));
    round_trips(&agg_in(
        MEM16,
        "memory(1) size(4) align(2) field(0, ptr(1)) field(2, i16)",
    ));
    round_trips(&format!(
        "aggregate @\"a b\"() memory(0) size(1) align(1) field(0, i8) {{\n}}\n\n{}",
        one_func("func @f() {\n^e:\n  ret @0\n}\n")
    ));
    round_trips(&one_func(&format!(
        "module @dev() {{\n  aggregate @s() {PAIR} {{\n  }}\n\n}}\n"
    )));
    let m = parse_ok(&agg(PAIR));
    let want = Aggregate::new("s", 0, 16, 8)
        .field(0, Type::word("i64"), None)
        .field(8, Type::word("ptr"), None);
    assert_eq!(m.items, [Item::Aggregate(want)]);
}

#[test]
fn attributes_that_do_not_decode_fail_where_the_spec_says() {
    rejected_at(
        &agg("size(16) memory(0) align(8)"),
        16,
        "writes memory(N) first",
    );
    rejected_at(
        &agg("memory(0) size(-1) align(8)"),
        26,
        "writes size(S) second",
    );
    rejected_at(
        &agg("memory(0) size(18446744073709551616) align(1)"),
        26,
        "size(S)",
    );
    rejected_at(
        &agg("memory(0) size(16) align(a)"),
        35,
        "writes align(A) third",
    );
    rejected_at(
        &agg("memory(0) size(16)"),
        1,
        "writes memory(N), size(S) and align(A)",
    );
    for field in [
        "field(0)",
        "field(0, 5)",
        "field(0, i8, 1, 2)",
        "field(0, i0x)",
        "field(-1, i8)",
        "fields(0, i8)",
    ] {
        rejected_at(
            &agg(&format!("memory(0) size(16) align(8) {field}")),
            44,
            "not a field",
        );
    }
    // The first field that does not decode is reported, its type included,
    // before a later field that is not a field at all.
    rejected_at(
        &agg("memory(0) size(16) align(8) field(0, i16777216) field(-1, i8)"),
        44,
        "not a field",
    );
    rejected_at(
        &one_func("aggregate @s(%x: i8) memory(0) size(1) align(1) {\n}\n"),
        14,
        "an aggregate has no parameters",
    );
    rejected_at(
        &one_func("aggregate @s() -> i8 memory(0) size(1) align(1) {\n}\n"),
        19,
        "an aggregate has no results",
    );
    rejected_at(
        &one_func("aggregate @s() memory(0) size(1) align(1) {\n^e:\n  ret @0\n}\n"),
        1,
        "an aggregate has an empty body",
    );
}

#[test]
fn validation_places_each_field() {
    assert!(messages(&agg(PAIR)).is_empty());
    assert!(messages(&agg("memory(0) size(0) align(1)")).is_empty());
    // Four `i24` take 16 units of memory 0, each rounded up to 4.
    assert!(messages(&agg("memory(0) size(16) align(4) field(0, i24, 4)")).is_empty());
    assert_eq!(
        messages(&agg("memory(0) size(12) align(4) field(0, i24, 4)")),
        [field_at(0, "ends past the layout's size, 12")]
    );
    assert_eq!(
        messages(&agg(
            "memory(0) size(16) align(4) field(0, i24, 4) field(12, i8)"
        )),
        ["two fields of the layout share a unit"]
    );
    assert!(
        messages(&agg(
            "memory(0) size(4) align(4) field(0, i32) field(4, i32, 0)"
        ))
        .is_empty()
    );
    assert!(
        messages(&agg(
            "memory(0) size(4) align(4) field(0, i32) field(0, i32, 0)"
        ))
        .is_empty()
    );
    assert_eq!(
        messages(&agg(
            "memory(0) size(16) align(8) field(0, i64) field(4, i32)"
        )),
        ["two fields of the layout share a unit"]
    );
    assert_eq!(
        messages(&agg("memory(0) size(16) align(8) field(4, i64)")),
        [field_at(4, "is not a multiple of its type's alignment, 8")]
    );
    assert_eq!(
        messages(&agg("memory(0) size(8) align(8) field(4, i64)")),
        [
            field_at(4, "is not a multiple of its type's alignment, 8"),
            field_at(4, "ends past the layout's size, 8"),
        ]
    );
    assert_eq!(
        messages(&agg("memory(0) size(16) align(4) field(0, i64)")),
        [field_at(
            0,
            "has a type aligned to 8 units, more than the layout's 4"
        )]
    );
    for a in [6, 0] {
        assert_eq!(
            messages(&agg(&format!("memory(0) size(12) align({a})"))),
            [format!(
                "the layout is aligned to {a} units: an alignment is a power of two no larger than 16777215"
            )]
        );
    }
}

#[test]
fn validation_checks_the_memories_and_types() {
    assert_eq!(
        messages(&agg("memory(1) size(4) align(4) field(0, i32)")),
        ["the layout describes memory 1, which the data layout does not declare"]
    );
    assert_eq!(
        messages(&agg("memory(0) size(8) align(8) field(0, ptr(1))")),
        ["a type names memory 1, which the data layout does not declare"]
    );
    assert_eq!(
        messages(&agg("memory(0) size(4) align(4) field(0, i0)")),
        ["a type of the layout is not valid"]
    );
    // A float takes the units of its bits, at the natural alignment of its
    // size, as `alloca` places it.
    assert!(
        messages(&agg(
            "memory(0) size(16) align(8) field(0, f32) field(4, f16, 2) field(8, f64)"
        ))
        .is_empty()
    );
    assert_eq!(
        messages(&agg("memory(0) size(8) align(4) field(2, f32)")),
        [field_at(2, "is not a multiple of its type's alignment, 4")]
    );
    assert_eq!(
        messages(&one_func(&format!(
            "aggregate @f() {PAIR} {{\n}}\n\nfunc @f() {{\n^e:\n  ret @0\n}}\n"
        ))),
        ["the symbol @f names more than one item"]
    );
    let nested = "module @dev() {\n  aggregate @s() memory(1) size(4) align(4) {\n  }\n\n}\n";
    assert_eq!(
        messages(&one_func(nested)),
        ["the layout describes memory 1, which the data layout does not declare"]
    );
}

#[test]
fn a_memory_of_16_bit_units_counts_its_own_units() {
    let ok = |attrs: &str| assert!(messages(&agg_in(MEM16, attrs)).is_empty(), "{attrs}");
    ok("memory(1) size(4) align(2) field(0, ptr(1)) field(2, i16)");
    ok("memory(1) size(8) align(4) field(0, ptr, 2)");
    ok("memory(1) size(6) align(2) field(0, i24, 2)");
    assert_eq!(
        messages(&agg_in(MEM16, "memory(1) size(6) align(4) field(2, ptr)")),
        [field_at(2, "is not a multiple of its type's alignment, 4")]
    );
    assert_eq!(
        messages(&agg_in(
            MEM16,
            "memory(1) size(3) align(2) field(0, i24, 2)"
        )),
        [field_at(0, "ends past the layout's size, 3")]
    );
    assert_eq!(
        messages(&agg_in(
            "memory(1, unit(16), pointer(32), little, align(4))",
            "memory(1) size(4) align(2) field(0, ptr(1))"
        )),
        [field_at(
            0,
            "has a type aligned to 4 units, more than the layout's 2"
        )]
    );
}
