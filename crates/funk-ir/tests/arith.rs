//! `add`, `sub` and `mul` with their flags, and `freeze` (#14), through the
//! builder, the verifier, the parser and the printer (`Op.decode` in
//! `lean/Fir/Core/Text.lean`). In text, a use that does not decode is a
//! parse error at the op's name (ADR-2026-10-30-0815); in IR that a builder
//! made, it is a validation error at the op and its location.

mod common;

use common::{one_func, parse_err, parse_ok};
use funk_ir::dialects::core::WRAP_FLAG_SETS;
use funk_ir::dialects::core::int_type;
use funk_ir::{
    Attr, Block, Diagnostic, Func, LocRef, Location, Module, Op, Registry, TextPos, Type, print,
    verify,
};

const OPS: [&str; 3] = ["add", "sub", "mul"];

/// The text of `op` with the flags `flags`, as in `add nuw nsw`.
fn spelled(op: &str, flags: &[&str]) -> String {
    std::iter::once(op)
        .chain(flags.iter().copied())
        .collect::<Vec<_>>()
        .join(" ")
}

/// `@f(%a: iW, %b: iW) -> iW`: each op with each set of flags, then
/// `freeze` of the last result, which it returns.
fn every_op_text(w: u32) -> String {
    let mut text = format!("func @f(%a: i{w}, %b: i{w}) -> i{w} {{\n^entry:\n");
    let mut n = 0;
    for op in OPS {
        for flags in WRAP_FLAG_SETS {
            text += &format!("  %r{n}: i{w} = {} %a, %b @0\n", spelled(op, flags));
            n += 1;
        }
    }
    text += &format!("  %f: i{w} = freeze %r{} @0\n  ret %f @0\n}}\n", n - 1);
    one_func(&text)
}

/// The module of [`every_op_text`], made with the builder.
fn every_op_built(w: u32) -> Module {
    let t = int_type(w);
    let mut b = Block::new("entry");
    let mut n = 0;
    for op in OPS {
        for flags in WRAP_FLAG_SETS {
            let o = flags
                .iter()
                .fold(Op::new(op, LocRef(0)), |o, f| o.attr(Attr::word(*f)));
            b = b.op(o
                .operand("a")
                .operand("b")
                .result(format!("r{n}"), t.clone()));
            n += 1;
        }
    }
    let freeze = Op::new("freeze", LocRef(0)).operand(format!("r{}", n - 1));
    b = b.op(freeze.result("f", t.clone()));
    b = b.op(Op::new("ret", LocRef(0)).operand("f"));
    let f = Func::new("f")
        .param("a", t.clone())
        .param("b", t.clone())
        .result(t);
    let mut m = Module::new();
    m.locs.push(Location::Unknown);
    m.func(f.block(b))
}

#[test]
fn every_op_and_set_of_flags_parses_verifies_and_prints_at_any_width() {
    let reg = Registry::core();
    for w in [1, 7, 8, 16, 32, 33, 64, 128, 16_777_215] {
        let text = every_op_text(w);
        let m = parse_ok(&text);
        assert_eq!(verify(&m, &reg), vec![], "i{w}");
        assert_eq!(print(&m), text, "i{w}");
        assert_eq!(every_op_built(w), m, "i{w}");
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
fn ill_typed_uses_of_add_sub_and_mul_are_rejected_at_the_name() {
    let types = "takes two operands of one integer type";
    for op in OPS {
        for (line, needle) in [
            (format!("%r: i32 = {op} %a, %b"), types),
            (format!("%r: i64 = {op} %a, %a"), types),
            (format!("%r: i64 = {op} %b, %a"), types),
            (format!("%r: i32 = {op} %a"), types),
            (format!("%r: i32 = {op} %a, %a, %a"), types),
            (format!("{op} %a, %a"), types),
            (format!("%r: i32, %s: i32 = {op} %a, %a"), types),
            (format!("%r: ptr = {op} %p, %p"), types),
            (format!("%r: i32 = {op} nsw nuw %a, %a"), "nuw before nsw"),
            (
                format!("%r: i32 = {op} nuw nsw nuw %a, %a"),
                "nuw more than once",
            ),
            (
                format!("%r: i32 = {op} nuw nuw %a, %a"),
                "nuw more than once",
            ),
            (
                format!("%r: i32 = {op} nsw nsw %a, %a"),
                "nsw more than once",
            ),
            (format!("%r: i32 = {op} exact %a, %a"), "not exact"),
            (format!("%r: i32 = {op} nuw exact %a, %a"), "not exact"),
            (format!("%r: i32 = {op} wrap %a, %a"), "not wrap"),
            (
                format!("%r: i32 = {op} 1 %a, %a"),
                "attributes are its flags",
            ),
            (
                format!("%r: i32 = {op} \"nsw\" %a, %a"),
                "attributes are its flags",
            ),
            (
                format!("%r: i32 = {op} @nsw %a, %a"),
                "attributes are its flags",
            ),
        ] {
            rejected_at_name(&line, op, needle);
        }
    }
}

#[test]
fn ill_typed_uses_of_freeze_are_rejected_at_the_name() {
    let types = "freeze takes one operand of an integer type";
    for (line, needle) in [
        ("%r: i64 = freeze %a", types),
        ("%r: i32 = freeze %b", types),
        ("%r: i32 = freeze %a, %a", types),
        ("%r: i32 = freeze", types),
        ("freeze %a", types),
        ("%r: i32, %s: i32 = freeze %a", types),
        ("%r: ptr = freeze %p", types),
        ("%r: i32 = freeze nsw %a", "freeze takes no attributes"),
        ("%r: i32 = freeze 0 %a", "freeze takes no attributes"),
    ] {
        rejected_at_name(line, "freeze", needle);
    }
}

#[test]
fn the_flags_have_one_spelling_and_one_order() {
    for (flags, ok) in [
        ("", true),
        ("nuw", true),
        ("nsw", true),
        ("nuw nsw", true),
        ("nsw nuw", false),
        ("nuw nuw", false),
        ("nsw nsw", false),
        ("exact", false),
    ] {
        for op in OPS {
            let line = format!("%r: i32 = {op} {flags} %a, %a").replace("  ", " ");
            let text = with_op(&line);
            let parsed = funk_ir::parse(&text, &Registry::core());
            assert_eq!(parsed.is_ok(), ok, "{line}: {parsed:?}");
            if let Ok(m) = parsed {
                assert_eq!(print(&m), text);
            }
        }
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

fn words(ws: &[&str]) -> Vec<Attr> {
    ws.iter().map(|w| Attr::word(*w)).collect()
}

/// The uses that the parser rejects in
/// `ill_typed_uses_of_add_sub_and_mul_are_rejected_at_the_name`, made with
/// the builder.
#[test]
fn the_verifier_rejects_ill_typed_add_sub_and_mul_that_a_builder_made() {
    let (i32, i64, ptr) = (int_type(32), int_type(64), Type::word("ptr"));
    let types = "takes two operands of one integer type";
    for op in OPS {
        for flags in WRAP_FLAG_SETS {
            let attrs = words(flags);
            let ok = built(op, &attrs, &["a", "c"], std::slice::from_ref(&i32));
            assert_eq!(verify_op(ok), vec![], "{op} {flags:?}");
            rejected_at_op(
                built(op, &attrs, &["a", "b"], std::slice::from_ref(&i32)),
                types,
            );
            rejected_at_op(
                built(op, &attrs, &["a", "c"], std::slice::from_ref(&i64)),
                types,
            );
        }
        for (operands, results) in [
            (&["b", "a"][..], std::slice::from_ref(&i64)),
            (&["a"], std::slice::from_ref(&i32)),
            (&["a", "a", "a"], std::slice::from_ref(&i32)),
            (&["a", "c"], &[]),
            (&["a", "a"], &[i32.clone(), i32.clone()]),
            (&["p", "p"], std::slice::from_ref(&ptr)),
        ] {
            rejected_at_op(built(op, &[], operands, results), types);
        }
        let flag = "its flags nuw and nsw";
        for (attrs, needle) in [
            (words(&["nsw", "nuw"]), "nuw before nsw"),
            (words(&["nuw", "nsw", "nuw"]), "nuw more than once"),
            (words(&["nuw", "nuw"]), "nuw more than once"),
            (words(&["nsw", "nsw"]), "nsw more than once"),
            (words(&["exact"]), "not exact"),
            (words(&["nuw", "exact"]), "not exact"),
            (words(&["wrap"]), "not wrap"),
            (vec![Attr::int(1)], flag),
            (vec![Attr::Str("nsw".into())], flag),
            (vec![Attr::Sym("nsw".into())], flag),
        ] {
            let o = built(op, &attrs, &["a", "a"], std::slice::from_ref(&i32));
            rejected_at_op(o, needle);
        }
    }
}

/// The uses that the parser rejects in
/// `ill_typed_uses_of_freeze_are_rejected_at_the_name`, made with the
/// builder.
#[test]
fn the_verifier_rejects_ill_typed_freezes_that_a_builder_made() {
    let (i32, i64, ptr) = (int_type(32), int_type(64), Type::word("ptr"));
    let ok = built("freeze", &[], &["c"], std::slice::from_ref(&i32));
    assert_eq!(verify_op(ok), vec![]);
    let types = "freeze takes one operand of an integer type";
    for (operands, results) in [
        (&["a"][..], std::slice::from_ref(&i64)),
        (&["b"], std::slice::from_ref(&i32)),
        (&["a", "a"], std::slice::from_ref(&i32)),
        (&[], std::slice::from_ref(&i32)),
        (&["a"], &[]),
        (&["a"], &[i32.clone(), i32.clone()]),
        (&["p"], std::slice::from_ref(&ptr)),
    ] {
        rejected_at_op(built("freeze", &[], operands, results), types);
    }
    for attrs in [words(&["nsw"]), vec![Attr::int(0)]] {
        let o = built("freeze", &attrs, &["a"], std::slice::from_ref(&i32));
        rejected_at_op(o, "freeze takes no attributes");
    }
}
