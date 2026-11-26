//! The address of a function `funcaddr` (#235), on the texts of
//! `lean/FirTest/FuncAddr.lean`, so the two parsers read the same op and
//! the two validators accept and reject the same uses: the op reads back
//! and prints as itself, and validation checks that its symbol names a
//! function of its own table and that its result is a pointer of memory 0.

mod common;

use common::{diagnostics, parse_ok, rejects};
use funk_ir::print;

const ITEMS: &str = "layout memory(1, unit(16), pointer(32), little)\n\n\
     global @msg() size(1) align(1) {\n}\n\n\
     aggregate @pair() memory(0) size(16) align(8) field(0, i64) field(8, ptr) {\n}\n\n\
     extern @ext() {\n}\n\n";

/// A module with the items above, and a function `@f` of the body `body`
/// that returns the pointer `%q` of memory `n`.
fn module(n: u32, body: &str) -> String {
    let ptr = if n == 0 {
        "ptr".to_string()
    } else {
        format!("ptr({n})")
    };
    format!(
        "{ITEMS}func @f() -> {ptr} {{\n^entry:\n  {body}\n  ret %q @0\n}}\n\n\
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
fn funcaddr_reads_back_as_written() {
    for (n, body) in [
        (0, "%q: ptr = funcaddr @f @0"),
        (0, "%q: ptr = funcaddr @\"a b\" @0"),
        (1, "%q: ptr(1) = funcaddr @f @0"),
    ] {
        let text = module(n, body);
        assert_eq!(print(&parse_ok(&text)), text);
    }
}

#[test]
fn validation_accepts_a_function_of_the_table_in_memory_0() {
    valid(&module(0, "%q: ptr = funcaddr @f @0"));
}

#[test]
fn validation_rejects_a_symbol_that_names_no_function() {
    for s in ["@none", "@msg", "@pair", "@ext"] {
        rejects(
            &module(0, &format!("%q: ptr = funcaddr {s} @0")),
            &format!("op funcaddr refers to {s}, which names no function"),
        );
    }
}

#[test]
fn validation_rejects_a_result_of_another_memory() {
    rejects(
        &module(1, "%q: ptr(1) = funcaddr @f @0"),
        "funcaddr @f gives a pointer of memory 0, where functions are, but its result is a \
         pointer of memory 1",
    );
}

#[test]
fn an_op_names_only_the_functions_of_its_own_table() {
    let nested = |outer: &str, inner: &str| {
        format!(
            "func @out() {{\n^e:\n  ret @0\n}}\n\n\
             module @dev() {{\n  func @in() {{\n  ^e:\n    ret @0\n  }}\n\n\
             \x20 func @g() -> ptr {{\n  ^e:\n    %q: ptr = funcaddr {inner} @0\n    \
             ret %q @0\n  }}\n\n}}\n\n\
             func @f() -> ptr {{\n^e:\n  %q: ptr = funcaddr {outer} @0\n  ret %q @0\n}}\n\n\
             locs {{\n  @0 = unknown\n}}\n"
        )
    };
    valid(&nested("@out", "@in"));
    rejects(
        &nested("@in", "@in"),
        "op funcaddr refers to @in, which names no function",
    );
    rejects(
        &nested("@out", "@out"),
        "op funcaddr refers to @out, which names no function",
    );
}
