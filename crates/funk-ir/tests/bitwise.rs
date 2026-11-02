//! The bitwise ops `and`, `or` and `xor`, and the shifts `shl`, `lshr` and
//! `ashr` (#15), through the builder, the verifier, the parser and the
//! printer (`plainBinOps` and `Op.decode` in `lean/Fir/Core/Text.lean`).
//! In text, a use that does not decode is a parse error at the op's name
//! (ADR-2026-10-30-0815); in IR that a builder made, it is a validation
//! error at the op and its location. None of the six has flags.

mod common;

use common::{one_func, parse_err, parse_ok};
use funk_ir::dialects::core::{BITWISE_OPS, SHIFT_OPS, int_type};
use funk_ir::{
    Attr, Block, Diagnostic, Func, LocRef, Location, Module, Op, Registry, TextPos, Type, print,
    verify,
};

/// The six ops: the bitwise ops, then the shifts.
fn ops() -> impl Iterator<Item = &'static str> {
    BITWISE_OPS.into_iter().chain(SHIFT_OPS)
}

/// `@f(%a: iW, %b: iW) -> iW`: each op of `%a` and `%b` in turn, then
/// `ret` of the last result.
fn every_op_text(w: u32) -> String {
    let mut text = format!("func @f(%a: i{w}, %b: i{w}) -> i{w} {{\n^entry:\n");
    for (n, op) in ops().enumerate() {
        text += &format!("  %r{n}: i{w} = {op} %a, %b @0\n");
    }
    text += "  ret %r5 @0\n}\n";
    one_func(&text)
}

/// The module of [`every_op_text`], made with the builder.
fn every_op_built(w: u32) -> Module {
    let t = int_type(w);
    let mut b = Block::new("entry");
    for (n, op) in ops().enumerate() {
        let o = Op::new(op, LocRef(0)).operand("a").operand("b");
        b = b.op(o.result(format!("r{n}"), t.clone()));
    }
    b = b.op(Op::new("ret", LocRef(0)).operand("r5"));
    let f = Func::new("f")
        .param("a", t.clone())
        .param("b", t.clone())
        .result(t);
    let mut m = Module::new();
    m.locs.push(Location::Unknown);
    m.func(f.block(b))
}

#[test]
fn every_op_parses_verifies_and_prints_at_any_width() {
    let reg = Registry::core();
    for w in [1, 7, 8, 16, 32, 33, 64, 128, 16_777_215] {
        let text = every_op_text(w);
        let m = parse_ok(&text);
        assert_eq!(verify(&m, &reg), vec![], "i{w}");
        assert_eq!(print(&m), text, "i{w}");
        assert_eq!(every_op_built(w), m, "i{w}");
    }
}

#[test]
fn a_shift_by_n_or_more_is_valid() {
    // Such a shift gives poison when it runs, which is not an error.
    let reg = Registry::core();
    for (w, n) in [
        (1, "true"),
        (8, "8"),
        (8, "-1"),
        (32, "-2147483648"),
        (64, "64"),
    ] {
        for op in SHIFT_OPS {
            let text = one_func(&format!(
                "func @f(%a: i{w}) -> i{w} {{\n^entry:\n  %n: i{w} = const {n} @0\n  \
                 %r: i{w} = {op} %a, %n @0\n  ret %r @0\n}}\n"
            ));
            let m = parse_ok(&text);
            assert_eq!(verify(&m, &reg), vec![], "{op} by {n} at i{w}");
            assert_eq!(print(&m), text);
        }
    }
}

/// `@f(%a: i32, %b: i64, %p: ptr) -> i32` with one op on line 3, then
/// `ret %a`.
fn with_op(op: &str) -> String {
    one_func(&format!(
        "func @f(%a: i32, %b: i64, %p: ptr) -> i32 {{\n^entry:\n  {op} @0\n  ret %a @0\n}}\n"
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
fn ill_typed_uses_are_rejected_at_the_name() {
    let types = "takes two operands of one integer type";
    for op in ops() {
        for line in [
            format!("%r: i32 = {op} %a, %b"),
            format!("%r: i64 = {op} %a, %a"),
            format!("%r: i64 = {op} %b, %a"),
            format!("%r: i32 = {op} %a"),
            format!("%r: i32 = {op} %a, %a, %a"),
            format!("{op} %a, %a"),
            format!("%r: i32, %s: i32 = {op} %a, %a"),
            format!("%r: ptr = {op} %p, %p"),
        ] {
            rejected_at_name(&line, op, types);
        }
    }
}

#[test]
fn a_flag_or_any_attribute_is_rejected_at_the_name() {
    let none = "takes no attributes";
    for op in ops() {
        for attrs in [
            "nuw",
            "nsw",
            "nuw nsw",
            "exact",
            "nuw exact",
            "1",
            "\"nuw\"",
            "@nuw",
        ] {
            rejected_at_name(&format!("%r: i32 = {op} {attrs} %a, %a"), op, none);
        }
        // An attribute is checked before the types, as Lean's `bare` does.
        rejected_at_name(&format!("%r: i64 = {op} nuw %a, %a"), op, none);
    }
}

const L: LocRef = LocRef(5);

/// Whether `d` is the diagnostic of the function that rejects a value of
/// the reserved type `ptr` (`verify_text.rs`), such as `%p` below.
fn rejects_ptr(d: &Diagnostic) -> bool {
    d.op.is_none() && d.message.contains(", ptr, is not valid: ptr is reserved")
}

/// The diagnostics of `@f(%a: i32, %b: i64, %p: ptr) -> i32`, whose entry
/// block holds a constant `%c: i32`, `op` at index 1, and `ret %a`, less
/// those that reject a value of type `ptr`.
fn verify_op(op: Op) -> Vec<Diagnostic> {
    let c = Op::new("const", LocRef(0))
        .attr(Attr::int(1))
        .result("c", int_type(32));
    let f = Func::new("f")
        .param("a", int_type(32))
        .param("b", int_type(64))
        .param("p", Type::word("ptr"))
        .result(int_type(32))
        .block(
            Block::new("entry")
                .op(c)
                .op(op)
                .op(Op::new("ret", LocRef(0)).operand("a")),
        );
    let mut m = Module::new();
    m.locs.push(Location::Unknown);
    m.locs.insert(L, Location::Name("here".into()));
    let mut ds = verify(&m.func(f), &Registry::core());
    ds.retain(|d| !rejects_ptr(d));
    ds
}

/// Asserts that the verifier rejects `op` with one diagnostic at the op and
/// its location, for a reason that holds `needle`.
fn rejected_at_op(op: Op, needle: &str) {
    let name = op.name.clone();
    let ds = verify_op(op);
    assert_eq!(ds.len(), 1, "{ds:#?}");
    let d = &ds[0];
    let head = format!("op {name} does not match its registration");
    assert!(d.message.starts_with(&head), "{d}");
    assert!(d.message.contains(needle), "{d} lacks {needle:?}");
    assert_eq!(
        (d.func.as_deref(), d.block.as_deref(), d.op, d.loc),
        (Some("f"), Some("entry"), Some(1), Some(L)),
        "{d}"
    );
    assert_eq!(
        d.to_string(),
        format!("@f ^entry op 1 at @5: {}", d.message)
    );
}

/// `op` with these attributes, these operands and results of these types.
fn built(op: &str, attrs: &[Attr], operands: &[&str], results: &[Type]) -> Op {
    let o = attrs.iter().fold(Op::new(op, L), |o, a| o.attr(a.clone()));
    let o = operands.iter().fold(o, |o, x| o.operand(*x));
    results
        .iter()
        .enumerate()
        .fold(o, |o, (k, t)| o.result(format!("r{k}"), t.clone()))
}

/// The uses that the parser rejects in the two tests above, made with the
/// builder.
#[test]
fn the_verifier_rejects_ill_typed_uses_that_a_builder_made() {
    let (i32, i64, ptr) = (int_type(32), int_type(64), Type::word("ptr"));
    let types = "takes two operands of one integer type";
    for op in ops() {
        let ok = built(op, &[], &["a", "c"], std::slice::from_ref(&i32));
        assert_eq!(verify_op(ok), vec![], "{op}");
        for (operands, results) in [
            (&["a", "b"][..], std::slice::from_ref(&i32)),
            (&["a", "c"], std::slice::from_ref(&i64)),
            (&["b", "a"], std::slice::from_ref(&i64)),
            (&["a"], std::slice::from_ref(&i32)),
            (&["a", "a", "a"], std::slice::from_ref(&i32)),
            (&["a", "c"], &[]),
            (&["a", "a"], &[i32.clone(), i32.clone()]),
            (&["p", "p"], std::slice::from_ref(&ptr)),
        ] {
            rejected_at_op(built(op, &[], operands, results), types);
        }
        for attrs in [
            vec![Attr::word("nuw")],
            vec![Attr::word("nsw")],
            vec![Attr::word("nuw"), Attr::word("nsw")],
            vec![Attr::word("exact")],
            vec![Attr::int(1)],
            vec![Attr::Str("nuw".into())],
            vec![Attr::Sym("nuw".into())],
        ] {
            let o = built(op, &attrs, &["a", "a"], std::slice::from_ref(&i32));
            rejected_at_op(o, "takes no attributes");
        }
    }
}
