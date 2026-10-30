//! Validation errors on modules that parse: every rule of `Module.Valid`
//! that a text of the tracer subset can break, each with a negative test
//! (`lean/Fir/Validation/Rules.lean`, `lean/Fir/Core/Validation.lean`).

mod common;

use common::{diagnostics, one_func, rejects};
use funk_ir::LocRef;

/// A function `@f(%a: i32) -> i32` with these lines in its body.
fn func(lines: &[&str]) -> String {
    let body: String = lines.iter().map(|l| format!("{l}\n")).collect();
    one_func(&format!("func @f(%a: i32) -> i32 {{\n{body}}}\n"))
}

#[test]
fn the_dead_block_of_the_spec_is_rejected_and_named() {
    let text = "func @f() -> i32 {\n^entry:\n  %c: i32 = const 0 @0\n  ret %c @0\n^dead:\n  %d: i32 = const 1 @0\n  ret %d @0\n}\n\nlocs {\n  @0 = unknown\n}\n";
    let ds = diagnostics(text);
    assert_eq!(ds.len(), 1, "{ds:#?}");
    let d = &ds[0];
    assert!(d.message.contains("^dead"), "{d}");
    assert_eq!(
        (d.func.as_deref(), d.block.as_deref(), d.loc),
        (Some("f"), Some("dead"), Some(LocRef(0)))
    );
}

#[test]
fn a_function_needs_an_entry_block_without_arguments() {
    rejects(&one_func("func @f() {\n}\n"), "has no entry block");
    rejects(
        &func(&["^entry(%x: i32):", "  ret %x @0"]),
        "declares arguments",
    );
}

#[test]
fn labels_are_unique() {
    let ds = rejects(
        &func(&["^entry:", "  ret %a @0", "^entry:", "  ret %a @0"]),
        "names more than one block",
    );
    assert!(ds.iter().all(|d| d.block.as_deref() == Some("entry")));
}

#[test]
fn every_stated_type_is_valid() {
    rejects(
        &one_func("func @f(%x: i0) {\n^e:\n  ret @0\n}\n"),
        "the type of %x, i0, is not valid",
    );
    rejects(
        &one_func("func @f() -> i0 {\n^e:\n  %c: i0 = const 0 @0\n  ret %c @0\n}\n"),
        "a result type",
    );
    rejects(
        &one_func("func @f() -> i0 {\n^e:\n  %c: i0 = const 0 @0\n  ret %c @0\n}\n"),
        "%c, i0",
    );
    rejects(
        &one_func("func @f(%p: ptr) {\n^e:\n  ret @0\n}\n"),
        "ptr is reserved",
    );
    rejects(
        &one_func("func @f(%p: ptr) -> ptr {\n^e:\n  ret %p @0\n}\n"),
        "a result type of the function, ptr",
    );
}

#[test]
fn every_block_holds_an_op() {
    rejects(&func(&["^entry:"]), "block ^entry holds no ops");
}

#[test]
fn no_op_owns_a_region_yet() {
    rejects(&func(&["^entry:", "  ret %a {", "  } @0"]), "owns a region");
    let text = func(&[
        "^entry:",
        "  ret %v {",
        "  ^r:",
        "    %v: i32 = const 1 @0",
        "    ret %v @0",
        "  } @0",
    ]);
    rejects(
        &text,
        "%v is defined inside a region, and is not in scope here",
    );
}

#[test]
fn the_terminator_is_the_last_op_and_only_the_last() {
    let ds = rejects(
        &func(&["^entry:", "  ret %a @0", "  %c: i32 = const 1 @0"]),
        "is not the last op of ^entry",
    );
    assert!(
        ds.iter()
            .any(|d| d.message.contains("does not end with a terminator") && d.op == Some(1))
    );
    rejects(
        &func(&["^entry:", "  %c: i32 = const 1 @0"]),
        "does not end with a terminator",
    );
}

#[test]
fn only_terminators_have_successors_and_as_many_as_registered() {
    let text = func(&[
        "^entry:",
        "  %c: i32 = const 1 ^b @0",
        "  ret %a @0",
        "^b:",
        "  ret %a @0",
    ]);
    rejects(&text, "only terminators have successors");
    let text = func(&["^entry:", "  ret %a, ^b @0", "^b:", "  ret %a @0"]);
    rejects(&text, "ret has 1 successors, and its registration says 0");
}

#[test]
fn successors_name_blocks_other_than_the_entry_and_pass_their_arguments() {
    rejects(
        &func(&["^entry:", "  ret %a, ^entry @0"]),
        "no branch may go to the entry block ^entry",
    );
    rejects(
        &func(&["^entry:", "  ret %a, ^nowhere @0"]),
        "successor ^nowhere is not a block",
    );
    let b = ["^b(%x: i64):", "  ret %a @0"];
    let text = func(&["^entry:", "  ret %a, ^b(%undefined) @0", b[0], b[1]]);
    rejects(&text, "successor argument %undefined is not defined");
    rejects(
        &func(&["^entry:", "  ret %a, ^b(%a) @0", b[0], b[1]]),
        "passes (i32) but the block takes (i64)",
    );
    rejects(
        &func(&["^entry:", "  ret %a, ^b @0", b[0], b[1]]),
        "passes () but the block takes (i64)",
    );
}

#[test]
fn a_use_comes_after_its_definition() {
    let text = func(&[
        "^entry:",
        "  %b: i32 = add %c, %a @0",
        "  %c: i32 = const 1 @0",
        "  ret %b @0",
    ]);
    let ds = rejects(&text, "%c is used before it is defined");
    assert_eq!(ds[0].op, Some(0));
    rejects(
        &func(&["^entry:", "  %b: i32 = add %b, %a @0", "  ret %b @0"]),
        "%b is used before",
    );
}

#[test]
fn ret_returns_the_function_result_types() {
    rejects(
        &one_func("func @f(%a: i32) -> i64 {\n^e:\n  ret %a @0\n}\n"),
        "ret returns (i32) but the function returns (i64)",
    );
    rejects(
        &one_func("func @f(%a: i32) {\n^e:\n  ret %a @0\n}\n"),
        "returns (i32) but the function returns ()",
    );
    rejects(
        &one_func("func @f(%a: i32) -> i32, i32 {\n^e:\n  ret %a @0\n}\n"),
        "returns (i32, i32)",
    );
}

#[test]
fn every_location_reference_is_in_the_table() {
    let ds = rejects(
        &func(&["^entry:", "  ret %a @7"]),
        "location reference @7 is not in the location table",
    );
    assert_eq!(ds[0].loc, Some(LocRef(7)));
}

#[test]
fn symbols_are_unique() {
    let f = "func @f() {\n^e:\n  ret @0\n}\n\n";
    rejects(
        &one_func(&format!("{f}{f}")),
        "the symbol @f names more than one item",
    );
    let q = "func @\"a b\"() {\n^e:\n  ret @0\n}\n\n";
    rejects(
        &one_func(&format!("{q}{q}")),
        "@\"a b\" names more than one item",
    );
}

#[test]
fn the_location_table_is_valid() {
    let table = |entries: &str| format!("locs {{\n{entries}}}\n");
    for (entries, needle) in [
        ("  @1 = unknown\n  @0 = unknown\n", "@0 comes after @1"),
        ("  @0 = unknown\n  @0 = unknown\n", "@0 comes after @0"),
        ("  @0 = \"f\":0:1 to 1:1\n", "starts at line 1 or later"),
        ("  @0 = \"f\":2:1 to 1:1\n", "does not end before it starts"),
        ("  @0 = \"f\":2:5 to 2:4\n", "does not end before it starts"),
        ("  @0 = fused()\n", "fuses at least two"),
        ("  @0 = unknown\n  @1 = fused(@0)\n", "fuses at least two"),
        (
            "  @0 = derived(@0)\n",
            "@0 refers to @0, which does not come before it",
        ),
        (
            "  @0 = derived(@1)\n  @1 = unknown\n",
            "@0 refers to @1, which does not come before it",
        ),
        (
            "  @0 = callsite(@0 at @9)\n",
            "@0 refers to @9, which the table does not hold",
        ),
        (
            "  @1 = unknown\n  @3 = fused(@1, @2)\n",
            "@3 refers to @2, which the table does not hold",
        ),
    ] {
        let ds = rejects(&table(entries), needle);
        assert!(
            ds.iter().all(|d| d.func.is_none() && d.loc.is_none()),
            "{ds:#?}"
        );
    }
    for ok in [
        "  @0 = \"f\":2:5 to 2:0\n",
        "  @0 = \"f\":2:0 to 2:4\n",
        "  @0 = \"f\":2:9 to 3:1\n",
    ] {
        assert!(diagnostics(&table(ok)).is_empty(), "{ok}");
    }
}

#[test]
fn every_broken_rule_is_reported() {
    let text = "func @f() -> i64 {\n^entry(%x: i0):\n  ret %x @3\n^dead:\n}\n\nfunc @f() {\n}\n\nlocs {\n  @1 = unknown\n  @0 = unknown\n}\n";
    let ds = diagnostics(text);
    for needle in [
        "@0 comes after @1",
        "the symbol @f names more than one item",
        "declares arguments",
        "%x, i0, is not valid",
        "block ^dead is not reachable",
        "block ^dead holds no ops",
        "@3 is not in the location table",
        "ret returns (i0) but the function returns (i64)",
        "has no entry block",
    ] {
        assert!(
            ds.iter().any(|d| d.message.contains(needle)),
            "{needle}: {ds:#?}"
        );
    }
}
