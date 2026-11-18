//! The field address `fieldaddr` (#236), on the texts of
//! `lean/FirTest/FieldAddr.lean`, so the two parsers read the same op and
//! the two validators accept and reject the same uses: the op reads back
//! and prints as itself, and validation checks that its layout is one of
//! its table's, of its pointer's memory, that its field is one of the
//! layout's, and that only a repeated field takes an index, in memory 0 and
//! in a memory of 16-bit units.

mod common;

use common::{diagnostics, parse_ok, rejects};
use funk_ir::print;

const LAYOUTS: &str = "aggregate @pair() memory(0) size(16) align(8) field(0, i64) field(8, ptr) {\n}\n\n\
     aggregate @i24s() memory(0) size(16) align(4) field(0, i24, 4) {\n}\n\n\
     aggregate @wide() memory(1) size(4) align(2) field(0, ptr(1)) field(2, i16, 1) {\n}\n\n";

const MEM16: &str = "layout memory(1, unit(16), pointer(32), little)\n\n";

/// A module with the layouts above, and a function of the body `body` that
/// takes a pointer `%p` of memory `n` and an index `%k`, and returns the
/// pointer `%q`.
fn module(n: u32, body: &str) -> String {
    let ptr = if n == 0 {
        "ptr".to_string()
    } else {
        format!("ptr({n})")
    };
    format!(
        "{MEM16}{LAYOUTS}func @f(%p: {ptr}, %k: i32) -> {ptr} {{\n^entry:\n  {body}\n  ret %q @0\n}}\n\n\
         locs {{\n  @0 = unknown\n}}\n"
    )
}

fn valid(text: &str) {
    assert!(
        diagnostics(text).is_empty(),
        "{:#?}\n{text}",
        diagnostics(text)
    );
}

#[test]
fn fieldaddr_reads_back_as_written() {
    for (n, body) in [
        (0, "%q: ptr = fieldaddr @pair 1 %p @0"),
        (0, "%q: ptr = fieldaddr @i24s 0 %p, %k @0"),
        (1, "%q: ptr(1) = fieldaddr @wide 1 %p, %k @0"),
    ] {
        let text = module(n, body);
        assert_eq!(print(&parse_ok(&text)), text);
    }
}

#[test]
fn validation_accepts_a_field_or_an_element_of_the_tables_layouts() {
    valid(&module(0, "%q: ptr = fieldaddr @pair 0 %p @0"));
    valid(&module(0, "%q: ptr = fieldaddr @pair 1 %p @0"));
    valid(&module(0, "%q: ptr = fieldaddr @i24s 0 %p, %k @0"));
    // A repeated field named with no index gives its first element.
    valid(&module(0, "%q: ptr = fieldaddr @i24s 0 %p @0"));
    valid(&module(1, "%q: ptr(1) = fieldaddr @wide 0 %p @0"));
    valid(&module(1, "%q: ptr(1) = fieldaddr @wide 1 %p, %k @0"));
}

#[test]
fn validation_rejects_a_layout_or_field_the_op_cannot_name() {
    rejects(
        &module(0, "%q: ptr = fieldaddr @none 0 %p @0"),
        "fieldaddr @none names no aggregate's layout",
    );
    rejects(
        &module(0, "%q: ptr = fieldaddr @f 0 %p @0"),
        "fieldaddr @f names no aggregate's layout",
    );
    rejects(
        &module(0, "%q: ptr = fieldaddr @pair 2 %p @0"),
        "fieldaddr @pair 2 names no field: @pair has 2 fields",
    );
    rejects(
        &module(0, "%q: ptr = fieldaddr @pair 1 %p, %k @0"),
        "fieldaddr @pair 1 takes an index, but the field is not repeated",
    );
    rejects(
        &module(0, "%q: ptr = fieldaddr @wide 0 %p @0"),
        "fieldaddr @wide is a layout of memory 1, but its pointer is of memory 0",
    );
    rejects(
        &module(1, "%q: ptr(1) = fieldaddr @pair 0 %p @0"),
        "fieldaddr @pair is a layout of memory 0, but its pointer is of memory 1",
    );
}

#[test]
fn an_op_names_only_the_layouts_of_its_own_table() {
    let nested = |outer: &str, inner: &str| {
        format!(
            "aggregate @out() memory(0) size(8) align(8) field(0, i64) {{\n}}\n\n\
             module @dev() {{\n  aggregate @in() memory(0) size(4) align(4) field(0, i32) {{\n  }}\n\n\
             \x20 func @g(%p: ptr) -> ptr {{\n  ^entry:\n    %q: ptr = fieldaddr {inner} 0 %p @0\n    \
             ret %q @0\n  }}\n\n}}\n\n\
             func @f(%p: ptr) -> ptr {{\n^entry:\n  %q: ptr = fieldaddr {outer} 0 %p @0\n  ret %q @0\n}}\n\n\
             locs {{\n  @0 = unknown\n}}\n"
        )
    };
    valid(&nested("@out", "@in"));
    rejects(
        &nested("@in", "@in"),
        "fieldaddr @in names no aggregate's layout",
    );
    rejects(
        &nested("@out", "@out"),
        "fieldaddr @out names no aggregate's layout",
    );
}
