//! The branches `br` and `cond_br` (#19) through the builder, the parser,
//! the printer and the verifier (`Op.decode` in `lean/Fir/Core/Text.lean`).
//! In text, a use that does not decode, such as a `cond_br` whose condition
//! is not `i1`, is a parse error at the op's name (ADR-2026-10-30-0815); in
//! IR that a builder made, it is a validation error at the op and its
//! location. `branch_verify.rs` holds the rules of the control-flow graph.

mod common;

use common::{one_func, parse_err, parse_ok};
use funk_ir::dialects::core::int_type;
use funk_ir::{Attr, Block, Func, LocRef, Location, Module, Op, Registry, TextPos, print, verify};

/// A loop that passes values of `iW` round it: `@f(%n: iW, %c: i1) -> iW`
/// goes to `^loop` with `%n` and `%c`, which swaps its two `iW` arguments
/// each time round until its `i1` argument is `false`, then returns one.
fn loop_text(w: u32) -> String {
    one_func(&format!(
        "func @f(%n: i{w}, %c: i1) -> i{w} {{
^entry:
  %z: i{w} = freeze %n @0
  br ^loop(%n, %z, %c) @0
^loop(%a: i{w}, %b: i{w}, %go: i1):
  %f: i1 = const false @0
  cond_br %go, ^loop(%b, %a, %f), ^exit(%a, %a) @0
^exit(%r: i{w}, %s: i{w}):
  ret %s @0
}}
"
    ))
}

/// The module of [`loop_text`], made with the builder.
fn loop_built(w: u32) -> Module {
    let (t, i1) = (int_type(w), int_type(1));
    let at = LocRef(0);
    let f = Func::new("f")
        .param("n", t.clone())
        .param("c", i1.clone())
        .result(t.clone())
        .block(
            Block::new("entry")
                .op(Op::new("freeze", at).operand("n").result("z", t.clone()))
                .op(Op::new("br", at).succ("loop", &["n", "z", "c"])),
        )
        .block(
            Block::new("loop")
                .param("a", t.clone())
                .param("b", t.clone())
                .param("go", i1.clone())
                .op(Op::new("const", at)
                    .attr(Attr::word("false"))
                    .result("f", i1))
                .op(Op::new("cond_br", at)
                    .operand("go")
                    .succ("loop", &["b", "a", "f"])
                    .succ("exit", &["a", "a"])),
        )
        .block(
            Block::new("exit")
                .param("r", t.clone())
                .param("s", t)
                .op(Op::new("ret", at).operand("s")),
        );
    let mut m = Module::new();
    m.locs.push(Location::Unknown);
    m.func(f)
}

#[test]
fn branches_parse_verify_and_print_at_any_width() {
    let reg = Registry::core();
    for w in [1, 7, 8, 16, 32, 33, 64, 128, 16_777_215] {
        let text = loop_text(w);
        let m = parse_ok(&text);
        assert_eq!(verify(&m, &reg), vec![], "i{w}");
        assert_eq!(print(&m), text, "i{w}");
        assert_eq!(loop_built(w), m, "i{w}");
    }
}

#[test]
fn the_spec_s_sum_is_valid() {
    // `@sum` of `lean/Fir/Text/Example.lean`, with its locations; its
    // `@sum10` calls it, and `call` is #20's.
    let text = "func @sum(%n: i32) -> i32 {
^entry:
  %zero: i32 = const 0 @1
  br ^loop(%zero, %zero) @1
^loop(%i: i32, %acc: i32):
  %done: i1 = icmp sge %i, %n @2
  cond_br %done, ^exit(%acc), ^body @2
^body:
  %acc1: i32 = add nsw %acc, %i @3
  %one: i32 = const 1 @3
  %i1: i32 = add nsw %i, %one @3
  br ^loop(%i1, %acc1) @3
^exit(%r: i32):
  ret %r @4
}

locs {
  @0 = unknown
  @1 = \"sum.c\":2:3 to 2:15
  @2 = \"sum.c\":3:10 to 3:16
  @3 = \"sum.c\":4:5 to 4:17
  @4 = \"sum.c\":6:3 to 6:14
}
";
    let m = parse_ok(text);
    assert_eq!(verify(&m, &Registry::core()), vec![]);
    assert_eq!(print(&m), text);
}

#[test]
fn successors_may_repeat_a_block_or_a_value() {
    // Both successors of a `cond_br` may name one block, with other values,
    // and one value may go to several arguments.
    let text = one_func(
        "func @f(%a: i8, %b: i8, %c: i1) -> i8 {
^entry:
  cond_br %c, ^j(%a, %b), ^j(%b, %b) @0
^j(%x: i8, %y: i8):
  br ^k(%x, %x, %y) @0
^k(%p: i8, %q: i8, %r: i8):
  ret %r @0
}
",
    );
    let m = parse_ok(&text);
    assert_eq!(verify(&m, &Registry::core()), vec![]);
    assert_eq!(print(&m), text);
}

#[test]
fn a_successor_that_validation_rejects_still_parses() {
    // A successor's label and arguments are not decoded: an unknown block, a
    // value the function does not define and a wrong count all parse, and
    // print as they were written (ADR-2026-10-30-0815).
    for line in [
        "br ^nowhere",
        "br ^b(%undefined)",
        "br ^b(%a, %a)",
        "br ^entry(%a)",
        "br ^b, ^b",
        "cond_br %c, ^b(%a)",
        "cond_br %c, ^b(%a), ^b(%a), ^b(%a)",
    ] {
        let text = one_func(&format!(
            "func @f(%a: i8, %c: i1) -> i8 {{\n^entry:\n  {line} @0\n^b(%x: i8):\n  ret %x @0\n}}\n"
        ));
        let m = parse_ok(&text);
        assert_eq!(print(&m), text);
        assert_ne!(verify(&m, &Registry::core()), vec![], "{line}");
    }
}

/// `@f(%a: i32, %b: i64, %p: ptr, %c: i1, %d: i1)` with one op on line 3,
/// and a block `^b` that takes no arguments.
fn with_op(op: &str) -> String {
    one_func(&format!(
        "func @f(%a: i32, %b: i64, %p: ptr, %c: i1, %d: i1) {{\n^entry:\n  {op} @0\n^b:\n  ret @0\n}}\n"
    ))
}

/// Asserts that the parser rejects `op` at its name, for a reason that
/// holds `needle`.
fn rejected_at_name(op: &str, name: &str, needle: &str) {
    let e = parse_err(&with_op(op));
    let col = op.find(" = ").map_or(3, |i| i + 6);
    assert_eq!(e.pos, TextPos { line: 3, col }, "{op}: {e}");
    assert!(e.reason.contains(needle), "{op}: {e} lacks {needle:?}");
    assert!(
        e.reason.starts_with(&format!("op {name} does not decode")),
        "{e}"
    );
}

#[test]
fn a_cond_br_on_anything_but_one_i1_does_not_decode() {
    let why = "cond_br takes one operand, its i1 condition";
    for op in [
        "cond_br %a, ^b, ^b",
        "cond_br %b, ^b, ^b",
        "cond_br %p, ^b, ^b",
        "cond_br ^b, ^b",
        "cond_br %c, %d, ^b, ^b",
        "cond_br %c, %c, ^b, ^b",
        "cond_br %a, %c, ^b, ^b",
    ] {
        rejected_at_name(op, "cond_br", why);
    }
}

#[test]
fn a_br_with_an_operand_does_not_decode() {
    for op in ["br %a, ^b", "br %c, ^b", "br %c, %d, ^b", "br %p, ^b"] {
        rejected_at_name(op, "br", "br takes no operands");
    }
}

#[test]
fn a_branch_with_a_result_or_an_attribute_does_not_decode() {
    for (name, rest) in [("br", "^b"), ("cond_br", "%c, ^b, ^b")] {
        for result in ["%r: i1", "%r: i32", "%r: i32, %s: i32"] {
            let op = format!("{result} = {name} {rest}");
            rejected_at_name(&op, name, &format!("{name} defines no values"));
        }
        for attr in ["nsw", "exact", "likely", "1", "\"s\"", "@f", "w()", "true"] {
            let op = format!("{name} {attr} {rest}");
            rejected_at_name(&op, name, &format!("{name} takes no attributes"));
        }
    }
}

#[test]
fn an_undefined_condition_is_rejected_at_the_operand() {
    let e = parse_err(&with_op("cond_br %nope, ^b, ^b"));
    assert_eq!(e.pos, TextPos { line: 3, col: 11 }, "{e}");
    assert!(e.reason.contains("value %nope is not defined in @f"), "{e}");
}

/// The text `@f(%a: i32, %c: i1)` whose entry block holds one op made with
/// the builder, and whose block `^b` returns.
fn with_built(op: Op) -> Module {
    let (i32, i1) = (int_type(32), int_type(1));
    let f = Func::new("f")
        .param("a", i32)
        .param("c", i1)
        .block(Block::new("entry").op(op))
        .block(Block::new("b").op(Op::new("ret", LocRef(0))));
    let mut m = Module::new();
    m.locs.push(Location::Unknown);
    m.locs.push(Location::Name("branch".into()));
    m.func(f)
}

#[test]
fn ill_typed_branches_made_with_the_builder_are_located_validation_errors() {
    let here = LocRef(1);
    for (op, why) in [
        (
            Op::new("cond_br", here)
                .operand("a")
                .succ("b", &[])
                .succ("b", &[]),
            "cond_br takes one operand, its i1 condition, not (i32)",
        ),
        (
            Op::new("cond_br", here).succ("b", &[]).succ("b", &[]),
            "cond_br takes one operand, its i1 condition, not ()",
        ),
        (
            Op::new("br", here).operand("c").succ("b", &[]),
            "br takes no operands, not (i1)",
        ),
        (
            Op::new("br", here).result("r", int_type(1)).succ("b", &[]),
            "br defines no values",
        ),
        (
            Op::new("cond_br", here)
                .attr(Attr::word("likely"))
                .operand("c")
                .succ("b", &[])
                .succ("b", &[]),
            "cond_br takes no attributes",
        ),
    ] {
        let name = op.name.clone();
        let ds = verify(&with_built(op), &Registry::core());
        assert_eq!(ds.len(), 1, "{ds:#?}");
        let d = &ds[0];
        assert!(
            d.message
                .starts_with(&format!("op {name} does not match its registration: {why}")),
            "{d}"
        );
        assert_eq!(
            (d.func.as_deref(), d.block.as_deref(), d.op, d.loc),
            (Some("f"), Some("entry"), Some(0), Some(here)),
            "{d}"
        );
    }
}
