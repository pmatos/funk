//! `poison` (#122), through the builder, the verifier, the parser and the
//! printer (`Op.decode` in `lean/Fir/Core/Text.lean`). It has no
//! attributes and no operands, so its name comes right before its
//! location: `%p: i32 = poison @0`. In text, a use that does not decode is
//! a parse error at the op's name (ADR-2026-10-30-0815); in IR that a
//! builder made, it is a validation error at the op and its location.

mod common;

use common::{one_func, parse_err, parse_ok};
use funk_ir::dialects::core::int_type;
use funk_ir::{Attr, Block, Func, LocRef, Location, Module, Op, Registry, TextPos, print, verify};

/// `@f(%a: iW) -> iW`, which makes the poison `%p`, adds it to `%a`, and
/// returns the sum.
fn poison_text(w: u32) -> String {
    one_func(&format!(
        "func @f(%a: i{w}) -> i{w} {{\n^entry:\n  %p: i{w} = poison @0\n  \
         %s: i{w} = add %a, %p @0\n  ret %s @0\n}}\n"
    ))
}

/// The module of [`poison_text`], made with the builder.
fn poison_built(w: u32) -> Module {
    let t = int_type(w);
    let b = Block::new("entry")
        .op(Op::new("poison", LocRef(0)).result("p", t.clone()))
        .op(Op::new("add", LocRef(0))
            .operand("a")
            .operand("p")
            .result("s", t.clone()))
        .op(Op::new("ret", LocRef(0)).operand("s"));
    let mut m = Module::new();
    m.locs.push(Location::Unknown);
    m.func(Func::new("f").param("a", t.clone()).result(t).block(b))
}

#[test]
fn poison_parses_verifies_and_prints_at_any_width() {
    let reg = Registry::core();
    for w in [1, 7, 8, 16, 32, 33, 64, 128, 16_777_215] {
        let text = poison_text(w);
        let m = parse_ok(&text);
        assert_eq!(verify(&m, &reg), vec![], "i{w}");
        assert_eq!(print(&m), text, "i{w}");
        assert_eq!(poison_built(w), m, "i{w}");
    }
}

/// `@f(%a: i32) -> i32` with one op on line 3, then `ret %a`.
fn with_op(op: &str) -> String {
    one_func(&format!(
        "func @f(%a: i32) -> i32 {{\n^entry:\n  {op} @0\n  ret %a @0\n}}\n"
    ))
}

/// Asserts that the parser rejects `op` at the name `poison`, for a reason
/// that holds `needle`.
fn rejected_at_name(op: &str, needle: &str) {
    let e = parse_err(&with_op(op));
    let col = op.find(" = ").map_or(3, |i| i + 6);
    assert_eq!(e.pos, TextPos { line: 3, col }, "{op}: {e}");
    assert!(e.reason.contains(needle), "{op}: {e} lacks {needle:?}");
    assert!(e.reason.starts_with("op poison does not decode"), "{e}");
}

#[test]
fn ill_typed_uses_of_poison_are_rejected_at_the_name() {
    for (line, needle) in [
        ("%r: i32 = poison %a", "poison takes no operands"),
        ("%r: i32 = poison %a, %a", "poison takes no operands"),
        ("poison", "poison defines one value"),
        ("%r: i32, %s: i32 = poison", "poison defines one value"),
        ("%r: ptr = poison", "an integer, not a value of type ptr"),
        ("%r: i32 = poison 0", "poison takes no attributes"),
        ("%r: i32 = poison true", "poison takes no attributes"),
        ("%r: i32 = poison @g", "poison takes no attributes"),
        ("%r: i32 = poison \"p\"", "poison takes no attributes"),
    ] {
        rejected_at_name(line, needle);
    }
}

/// Asserts that the verifier rejects `op`, the second op of the entry
/// block of `@f(%a: i32) -> i32`, with one diagnostic at the op and its
/// location `@5`, for a reason that holds `needle`.
fn rejected_at_op(op: Op, needle: &str) {
    let here = LocRef(5);
    let c = Op::new("const", LocRef(0))
        .attr(Attr::int(1))
        .result("c", int_type(32));
    let f = Func::new("f")
        .param("a", int_type(32))
        .result(int_type(32))
        .block(
            Block::new("entry")
                .op(c)
                .op(Op { loc: here, ..op })
                .op(Op::new("ret", LocRef(0)).operand("a")),
        );
    let mut m = Module::new();
    m.locs.push(Location::Unknown);
    m.locs.insert(here, Location::Name("here".into()));
    let ds = verify(&m.func(f), &Registry::core());
    assert_eq!(ds.len(), 1, "{ds:#?}");
    let d = &ds[0];
    assert!(
        d.message
            .starts_with("op poison does not match its registration"),
        "{d}"
    );
    assert!(d.message.contains(needle), "{d} lacks {needle:?}");
    assert_eq!(
        (d.func.as_deref(), d.block.as_deref(), d.op, d.loc),
        (Some("f"), Some("entry"), Some(1), Some(here)),
        "{d}"
    );
}

/// The uses that the parser rejects in
/// `ill_typed_uses_of_poison_are_rejected_at_the_name`, made with the
/// builder; a result of type `ptr` is left out, as the verifier rejects
/// the type on its own.
#[test]
fn the_verifier_rejects_ill_typed_poisons_that_a_builder_made() {
    let i32 = int_type(32);
    let poison = || Op::new("poison", LocRef(0));
    assert!(
        verify(&poison_built(32), &Registry::core()).is_empty(),
        "a poison that the builder made is valid"
    );
    rejected_at_op(
        poison().operand("a").result("r", i32.clone()),
        "poison takes no operands",
    );
    rejected_at_op(poison(), "poison defines one value");
    rejected_at_op(
        poison().result("r", i32.clone()).result("s", i32.clone()),
        "poison defines one value",
    );
    for attr in [Attr::int(0), Attr::word("nsw"), Attr::Sym("g".into())] {
        rejected_at_op(
            poison().attr(attr).result("r", i32.clone()),
            "poison takes no attributes",
        );
    }
}
