//! The address of a global `globaladdr` (#237), on the texts of
//! `lean/FirTest/GlobalAddr.lean`, so the two parsers read the same op and
//! the two validators accept and reject the same uses: the op reads back
//! and prints as itself, and validation checks that its symbol names a
//! global of its own table, of its result's memory, in memory 0 and in a
//! memory of 16-bit units.

mod common;

use common::{diagnostics, parse_ok, rejects};
use funk_ir::print;

const GLOBALS: &str = "global @msg() size(8) align(1) const units(104, 105, 0) {\n}\n\n\
     global @wide() memory(1) size(4) align(2) {\n}\n\n\
     aggregate @pair() memory(0) size(16) align(8) field(0, i64) field(8, ptr) {\n}\n\n";

const MEM16: &str = "layout memory(1, unit(16), pointer(32), little)\n\n";

/// A module with the globals above, and a function of the body `body` that
/// returns the pointer `%q` of memory `n`.
fn module(n: u32, body: &str) -> String {
    let ptr = if n == 0 {
        "ptr".to_string()
    } else {
        format!("ptr({n})")
    };
    format!(
        "{MEM16}{GLOBALS}func @f() -> {ptr} {{\n^entry:\n  {body}\n  ret %q @0\n}}\n\n\
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
fn globaladdr_reads_back_as_written() {
    for (n, body) in [
        (0, "%q: ptr = globaladdr @msg @0"),
        (1, "%q: ptr(1) = globaladdr @wide @0"),
        (0, "%q: ptr = globaladdr @\"a b\" @0"),
    ] {
        let text = module(n, body);
        assert_eq!(print(&parse_ok(&text)), text);
    }
}

#[test]
fn validation_accepts_a_global_of_the_table_in_its_memory() {
    valid(&module(0, "%q: ptr = globaladdr @msg @0"));
    valid(&module(1, "%q: ptr(1) = globaladdr @wide @0"));
}

#[test]
fn validation_rejects_a_symbol_the_op_cannot_name() {
    rejects(
        &module(0, "%q: ptr = globaladdr @none @0"),
        "globaladdr @none names no global of its table",
    );
    rejects(
        &module(0, "%q: ptr = globaladdr @f @0"),
        "globaladdr @f names no global of its table",
    );
    rejects(
        &module(0, "%q: ptr = globaladdr @pair @0"),
        "globaladdr @pair names no global of its table",
    );
    rejects(
        &module(0, "%q: ptr = globaladdr @wide @0"),
        "globaladdr @wide is a global of memory 1, but its result is a pointer of memory 0",
    );
    rejects(
        &module(1, "%q: ptr(1) = globaladdr @msg @0"),
        "globaladdr @msg is a global of memory 0, but its result is a pointer of memory 1",
    );
}

#[test]
fn an_op_names_only_the_globals_of_its_own_table() {
    let nested = |outer: &str, inner: &str| {
        format!(
            "global @out() size(8) align(8) {{\n}}\n\n\
             module @dev() {{\n  global @in() size(4) align(4) {{\n  }}\n\n\
             \x20 func @g() -> ptr {{\n  ^entry:\n    %q: ptr = globaladdr {inner} @0\n    \
             ret %q @0\n  }}\n\n}}\n\n\
             func @f() -> ptr {{\n^entry:\n  %q: ptr = globaladdr {outer} @0\n  ret %q @0\n}}\n\n\
             locs {{\n  @0 = unknown\n}}\n"
        )
    };
    valid(&nested("@out", "@in"));
    rejects(
        &nested("@in", "@in"),
        "globaladdr @in names no global of its table",
    );
    rejects(
        &nested("@out", "@out"),
        "globaladdr @out names no global of its table",
    );
}

#[test]
fn an_op_names_the_first_global_of_its_symbol_whatever_else_shares_it() {
    // The module is invalid for its two items @msg, but the op names the
    // global, as `SymbolTable.globalMems` gives it in Lean.
    let text = module(0, "%q: ptr = globaladdr @msg @0")
        .replace("locs {", "func @msg() {\n^entry:\n  ret @0\n}\n\nlocs {");
    let found = diagnostics(&text);
    assert!(!found.is_empty(), "{text}");
    assert!(
        found.iter().all(|d| !d.message.contains("globaladdr")),
        "{found:#?}"
    );
}
