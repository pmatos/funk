//! A module's data layout (ADR-2026-11-12-1821), on the texts of
//! `lean/FirTest/Layout.lean`, so the two parsers reject each malformed
//! entry at the same place and the two validators give the same problems:
//! the text reads back and prints as itself, an entry that does not decode
//! is a parse error at the entry, and validation checks the entries and the
//! memories that each type names, nested modules included.

mod common;

use common::{diagnostics, one_func, parse_err, parse_ok};
use funk_ir::{ByteOrder, MemLayout, Registry, print, verify};

fn with_layout(l: &str, f: &str) -> String {
    format!("layout {l}\n\n{}", one_func(f))
}

const PTR1: &str = "func @f(%p: ptr(1)) -> ptr(1) {\n^e:\n  ret %p @0\n}\n";
const MEM1: &str = "memory(1, unit(8), pointer(32), little)";

fn undeclared(n: u32) -> String {
    format!("a type names memory {n}, which the data layout does not declare")
}

fn messages(text: &str) -> Vec<String> {
    diagnostics(text).into_iter().map(|d| d.message).collect()
}

fn round_trips(text: &str) {
    assert_eq!(print(&parse_ok(text)), text);
}

#[test]
fn layouts_read_back_as_written() {
    round_trips(&with_layout(MEM1, PTR1));
    round_trips(&with_layout(
        "memory(0, unit(16), pointer(32), little, align(1)), \
         memory(7, unit(8), pointer(64), big, nonintegral), \
         memory(1, unit(8), pointer(32), little, align(2), nonintegral)",
        PTR1,
    ));
    round_trips(&format!("dialects toy\n\n{}", with_layout(MEM1, PTR1)));
    let m = parse_ok(&with_layout(
        "memory(7, unit(16), pointer(24), big, align(4), nonintegral)",
        PTR1,
    ));
    assert_eq!(
        m.layout,
        vec![MemLayout {
            mem: 7,
            unit: 16,
            pointer: 24,
            order: ByteOrder::Big,
            align: Some(4),
            non_integral: true,
        }]
    );
}

#[test]
fn entries_that_do_not_decode_fail_at_the_entry() {
    for entry in [
        "memory(1)",
        "memory(1, unit(8), pointer(32), middle)",
        "memory(16777216, unit(8), pointer(32), little)",
        "memory(-1, unit(8), pointer(32), little)",
        "memory(1, unit(8), pointer(16777216), little)",
        "memory(1, pointer(32), unit(8), little)",
        "memory(1, unit(8), pointer(32), little, nonintegral, align(2))",
        "memory(1, unit(8), pointer(32), little, align)",
    ] {
        let e = parse_err(&with_layout(entry, PTR1));
        assert_eq!((e.pos.line, e.pos.col), (1, 8), "{entry}: {e}");
        assert!(e.reason.contains("not an entry of the data layout"), "{e}");
    }
    let e = parse_err(&with_layout(&format!("{MEM1}, mem(2)"), PTR1));
    assert_eq!((e.pos.line, e.pos.col), (1, 49), "{e}");
    let e = parse_err(&format!("layout\n\n{}", one_func(PTR1)));
    assert_eq!((e.pos.line, e.pos.col), (3, 6), "{e}");
    assert!(e.reason.contains("an item or the location table"), "{e}");
    parse_err(&format!(
        "layout {MEM1}\n\ndialects toy\n\n{}",
        one_func(PTR1)
    ));
    parse_err(&one_func(&format!(
        "module @dev() {{\n  layout {MEM1}\n\n}}\n"
    )));
}

#[test]
fn validation_checks_the_layout_and_its_memories() {
    assert!(messages(&with_layout(MEM1, PTR1)).is_empty());
    assert_eq!(messages(&one_func(PTR1)), [undeclared(1)]);
    assert_eq!(
        messages(&with_layout(
            "memory(2, unit(8), pointer(32), little)",
            PTR1
        )),
        [undeclared(1)]
    );
    assert!(
        messages(&with_layout(
            "memory(0, unit(8), pointer(32), little)",
            "func @f(%p: ptr) {\n^e:\n  ret @0\n}\n"
        ))
        .is_empty()
    );
    assert_eq!(
        messages(&with_layout("memory(1, unit(8), pointer(32), big)", PTR1)),
        ["data layout: memory 1 is big-endian: M1 admits only little-endian memories"]
    );
    assert_eq!(
        messages(&with_layout(
            "memory(1, unit(0), pointer(0), little, align(3))",
            PTR1
        )),
        [
            "data layout: memory 1 has a unit of 0 bits: a unit has 1 to 16777215 bits",
            "data layout: memory 1 has pointers of 0 bits: a pointer has 1 to 16777215 bits",
            "data layout: memory 1 aligns its pointers to 3 units: \
             an alignment is a power of two no larger than 16777215",
        ]
    );
    assert_eq!(
        messages(&with_layout(&format!("{MEM1}, {MEM1}"), PTR1)),
        ["data layout: memory 1 is declared more than once"]
    );
    assert!(
        messages(&with_layout(
            "memory(1, unit(16), pointer(16), little, align(1), nonintegral)",
            PTR1
        ))
        .is_empty()
    );
}

#[test]
fn a_nested_module_uses_the_layout_of_the_module_that_holds_it() {
    let nested = "module @dev() {\n  func @g(%p: ptr(1)) {\n  ^e:\n    ret @0\n  }\n\n}\n";
    assert!(messages(&with_layout(MEM1, nested)).is_empty());
    let ds = diagnostics(&one_func(nested));
    assert_eq!(ds.len(), 1, "{ds:#?}");
    assert_eq!(ds[0].message, undeclared(1));
    assert_eq!(ds[0].func.as_deref(), Some("g"));
}

#[test]
fn a_builder_declares_memories_without_text() {
    let entry = MemLayout {
        mem: 3,
        ..MemLayout::DEFAULT
    };
    let m = parse_ok(&one_func("func @f(%p: ptr(3)) {\n^e:\n  ret @0\n}\n"));
    assert!(!verify(&m, &Registry::core()).is_empty());
    let m = m.memory(entry);
    assert!(verify(&m, &Registry::core()).is_empty());
    assert!(print(&m).starts_with("layout memory(3, unit(8), pointer(64), little)\n\nfunc"));
}
