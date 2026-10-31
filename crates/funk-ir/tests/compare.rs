//! Comparison and selection: `icmp` with each of its ten predicates and
//! `select` (#16), through the builder, the verifier, the parser and the
//! printer (`Op.decode` in `lean/Fir/Core/Text.lean`). In text, a use that
//! does not decode is a parse error at the op's name (ADR-2026-10-30-0815);
//! in IR that a builder made, it is a validation error at the op and its
//! location.

mod common;

use common::{one_func, parse_err, parse_ok};
use funk_ir::dialects::core::{PREDICATES, int_type};
use funk_ir::{
    Attr, Block, Diagnostic, Func, LocRef, Location, Module, Op, Registry, TextPos, Type, print,
    verify,
};

const WIDTHS: [u32; 9] = [1, 7, 8, 16, 32, 33, 64, 128, 16_777_215];

/// `@f(%c: i1, %a: iW, %b: iW) -> iW`: `icmp` of `%a` and `%b` with each
/// predicate, `select` on `%c` and on each comparison, then `ret`.
fn every_use_text(w: u32) -> String {
    let mut text = format!("func @f(%c: i1, %a: i{w}, %b: i{w}) -> i{w} {{\n^entry:\n");
    for (n, p) in PREDICATES.iter().enumerate() {
        text += &format!("  %p{n}: i1 = icmp {p} %a, %b @0\n");
    }
    text += &format!("  %s: i{w} = select %c, %a, %b @0\n");
    for n in 0..PREDICATES.len() {
        text += &format!("  %s{n}: i{w} = select %p{n}, %b, %s @0\n");
    }
    text += "  ret %s9 @0\n}\n";
    one_func(&text)
}

/// The module of [`every_use_text`], made with the builder.
fn every_use_built(w: u32) -> Module {
    let t = int_type(w);
    let mut b = Block::new("entry");
    for (n, p) in PREDICATES.iter().enumerate() {
        b = b.op(Op::new("icmp", LocRef(0))
            .attr(Attr::word(*p))
            .operand("a")
            .operand("b")
            .result(format!("p{n}"), int_type(1)));
    }
    let select = |c: &str, x: &str, y: &str, r: String| {
        Op::new("select", LocRef(0))
            .operand(c)
            .operand(x)
            .operand(y)
            .result(r, t.clone())
    };
    b = b.op(select("c", "a", "b", "s".into()));
    for n in 0..PREDICATES.len() {
        b = b.op(select(&format!("p{n}"), "b", "s", format!("s{n}")));
    }
    b = b.op(Op::new("ret", LocRef(0)).operand("s9"));
    let f = Func::new("f")
        .param("c", int_type(1))
        .param("a", t.clone())
        .param("b", t.clone())
        .result(t);
    let mut m = Module::new();
    m.locs.push(Location::Unknown);
    m.func(f.block(b))
}

#[test]
fn every_predicate_and_select_parse_verify_and_print_at_any_width() {
    let reg = Registry::core();
    for w in WIDTHS {
        let text = every_use_text(w);
        let m = parse_ok(&text);
        assert_eq!(verify(&m, &reg), vec![], "i{w}");
        assert_eq!(print(&m), text, "i{w}");
        assert_eq!(every_use_built(w), m, "i{w}");
    }
}

/// `@f(%a: i32, %b: i64, %p: ptr, %c: i1) -> i32` with one op on line 3,
/// then `ret %a`.
fn with_op(op: &str) -> String {
    one_func(&format!(
        "func @f(%a: i32, %b: i64, %p: ptr, %c: i1) -> i32 {{\n^entry:\n  {op} @0\n  \
         ret %a @0\n}}\n"
    ))
}

/// Asserts that the parser rejects `op` at its name, for a reason that
/// starts with `head` and holds `needle`.
fn rejected_at_name(op: &str, head: &str, needle: &str) {
    let e = parse_err(&with_op(op));
    let col = op.find(" = ").map_or(3, |i| i + 6);
    assert_eq!(e.pos, TextPos { line: 3, col }, "{op}: {e}");
    assert!(
        e.reason.starts_with(head),
        "{op}: {e} does not start {head:?}"
    );
    assert!(e.reason.contains(needle), "{op}: {e} lacks {needle:?}");
}

const ICMP: &str = "op icmp does not decode";
const SELECT: &str = "op select does not decode";
const ICMP_TYPES: &str = "takes two operands of one integer type and defines one i1";
const SELECT_TYPES: &str = "takes an i1 condition and two operands of one integer type";

#[test]
fn ill_typed_comparisons_are_rejected_at_the_name() {
    for p in PREDICATES {
        for line in [
            format!("%r: i1 = icmp {p} %a, %b"),
            format!("%r: i1 = icmp {p} %b, %a"),
            format!("%r: i1 = icmp {p} %c, %a"),
            format!("%r: i32 = icmp {p} %a, %a"),
            format!("%r: i64 = icmp {p} %b, %b"),
            format!("%r: ptr = icmp {p} %a, %a"),
            format!("%r: i1 = icmp {p} %a"),
            format!("%r: i1 = icmp {p}"),
            format!("%r: i1 = icmp {p} %a, %a, %a"),
            format!("icmp {p} %a, %a"),
            format!("%r: i1, %s: i1 = icmp {p} %a, %a"),
            format!("%r: i1 = icmp {p} %p, %p"),
            format!("%r: i1 = icmp {p} %a, %p"),
        ] {
            rejected_at_name(&line, ICMP, ICMP_TYPES);
        }
    }
}

#[test]
fn icmp_has_one_predicate_of_ten_spelled_as_llvm_spells_them() {
    for (attrs, needle) in [
        ("", "its predicate, and has none"),
        ("slt slt", "its predicate, not 2"),
        ("slt sgt", "its predicate, not 2"),
        ("eq ne uge", "its predicate, not 3"),
        ("slt nsw", "its predicate, not 2"),
        ("nuw ult", "its predicate, not 2"),
        ("lt", "not lt"),
        ("SLT", "not SLT"),
        ("Eq", "not Eq"),
        ("oeq", "not oeq"),
        ("true", "not true"),
        ("nsw", "not nsw"),
        ("exact", "not exact"),
        ("1", "attribute is its predicate, not 1"),
        ("\"slt\"", "attribute is its predicate"),
        ("@slt", "attribute is its predicate"),
        ("slt()", "attribute is its predicate"),
        ("slt(1)", "attribute is its predicate"),
    ] {
        rejected_at_name(&format!("%r: i1 = icmp {attrs} %a, %a"), ICMP, needle);
    }
    // `icmp.slt` is the spelling before the predicate became an attribute.
    // It names no op, so it does not decode either.
    for p in PREDICATES {
        let op = format!("icmp.{p}");
        let why = format!("unknown op {op}");
        rejected_at_name(&format!("%r: i1 = {op} %a, %a"), &why, &why);
    }
    let reg = Registry::core();
    for p in PREDICATES {
        let text = with_op(&format!("%r: i1 = icmp {p} %a, %a"));
        assert_eq!(print(&funk_ir::parse(&text, &reg).unwrap()), text);
    }
}

#[test]
fn ill_typed_selects_are_rejected_at_the_name() {
    for line in [
        "%r: i32 = select %a, %a, %a",
        "%r: i64 = select %b, %b, %b",
        "%r: i32 = select %c, %a, %b",
        "%r: i64 = select %c, %a, %b",
        "%r: i64 = select %c, %b, %a",
        "%r: i64 = select %c, %a, %a",
        "%r: i1 = select %c, %a, %a",
        "%r: i32 = select %p, %a, %a",
        "%r: ptr = select %c, %p, %p",
        "%r: i32 = select %c, %a",
        "%r: i32 = select %a, %a",
        "%r: i32 = select %c",
        "%r: i32 = select",
        "%r: i32 = select %c, %c, %a, %a",
        "select %c, %a, %a",
        "%r: i32, %s: i32 = select %c, %a, %a",
    ] {
        rejected_at_name(line, SELECT, SELECT_TYPES);
    }
    for attrs in [
        "nsw", "slt", "exact", "true", "1", "\"x\"", "@x", "nuw nsw", "slt()",
    ] {
        let line = format!("%r: i32 = select {attrs} %c, %a, %a");
        rejected_at_name(&line, SELECT, "select takes no attributes");
    }
    let text = with_op("%r: i1 = select %c, %c, %c");
    assert_eq!(print(&parse_ok(&text)), text);
}

const L: LocRef = LocRef(5);

/// Whether `d` is the diagnostic of the function that rejects a value of
/// the reserved type `ptr` (`verify_text.rs`), such as `%p` below.
fn rejects_ptr(d: &Diagnostic) -> bool {
    d.op.is_none() && d.message.contains(", ptr, is not valid: ptr is reserved")
}

/// The diagnostics of `@f(%a: i32, %b: i64, %p: ptr, %c: i1) -> i32`,
/// whose entry block holds a constant `%k: i32`, `op` at index 1, and
/// `ret %a`, less those that reject a value of type `ptr`.
fn verify_op(op: Op) -> Vec<Diagnostic> {
    let k = Op::new("const", LocRef(0))
        .attr(Attr::int(1))
        .result("k", int_type(32));
    let f = Func::new("f")
        .param("a", int_type(32))
        .param("b", int_type(64))
        .param("p", Type::word("ptr"))
        .param("c", int_type(1))
        .result(int_type(32))
        .block(
            Block::new("entry")
                .op(k)
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
/// its location, which starts with `head` and holds `needle`.
fn rejected_at_op(op: Op, head: &str, needle: &str) {
    let ds = verify_op(op);
    assert_eq!(ds.len(), 1, "{ds:#?}");
    let d = &ds[0];
    assert!(d.message.starts_with(head), "{d}");
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

const ICMP_BUILT: &str = "op icmp does not match its registration";
const SELECT_BUILT: &str = "op select does not match its registration";

/// The comparisons that the parser rejects above, made with the builder.
#[test]
fn the_verifier_rejects_ill_typed_comparisons_that_a_builder_made() {
    let (i1, i32, i64, ptr) = (int_type(1), int_type(32), int_type(64), Type::word("ptr"));
    let one = |t: &Type| vec![t.clone()];
    for p in PREDICATES {
        let pred = [Attr::word(p)];
        assert_eq!(verify_op(built("icmp", &pred, &["a", "k"], &one(&i1))), []);
        for (operands, results) in [
            (&["a", "b"][..], one(&i1)),
            (&["c", "a"], one(&i1)),
            (&["a", "k"], one(&i32)),
            (&["b", "b"], one(&i64)),
            (&["a", "a"], one(&ptr)),
            (&["a"], one(&i1)),
            (&[], one(&i1)),
            (&["a", "a", "a"], one(&i1)),
            (&["a", "a"], vec![]),
            (&["a", "a"], vec![i1.clone(), i1.clone()]),
            (&["p", "p"], one(&i1)),
        ] {
            rejected_at_op(
                built("icmp", &pred, operands, &results),
                ICMP_BUILT,
                ICMP_TYPES,
            );
        }
    }
    for (attrs, needle) in [
        (vec![], "and has none"),
        (vec![Attr::word("slt"), Attr::word("slt")], "not 2"),
        (vec![Attr::word("slt"), Attr::word("nsw")], "not 2"),
        (vec![Attr::word("lt")], "not lt"),
        (vec![Attr::word("SLT")], "not SLT"),
        (vec![Attr::int(1)], "attribute is its predicate, not 1"),
        (vec![Attr::Str("slt".into())], "attribute is its predicate"),
        (vec![Attr::Sym("slt".into())], "attribute is its predicate"),
        (
            vec![Attr::App("slt".into(), vec![])],
            "attribute is its predicate",
        ),
    ] {
        let o = built("icmp", &attrs, &["a", "a"], &one(&i1));
        rejected_at_op(o, ICMP_BUILT, needle);
    }
    let old = built("icmp.slt", &[], &["a", "a"], &one(&i1));
    let why = "op icmp.slt is not registered";
    rejected_at_op(old, why, why);
}

/// The selects that the parser rejects above, made with the builder.
#[test]
fn the_verifier_rejects_ill_typed_selects_that_a_builder_made() {
    let (i1, i32, i64, ptr) = (int_type(1), int_type(32), int_type(64), Type::word("ptr"));
    let one = |t: &Type| vec![t.clone()];
    let ok = built("select", &[], &["c", "a", "k"], &one(&i32));
    assert_eq!(verify_op(ok), []);
    for (operands, results) in [
        (&["a", "a", "a"][..], one(&i32)),
        (&["k", "a", "k"], one(&i32)),
        (&["c", "a", "b"], one(&i32)),
        (&["c", "a", "b"], one(&i64)),
        (&["c", "a", "a"], one(&i64)),
        (&["c", "a", "a"], one(&i1)),
        (&["p", "a", "a"], one(&i32)),
        (&["c", "p", "p"], one(&ptr)),
        (&["c", "a"], one(&i32)),
        (&["c"], one(&i32)),
        (&[], one(&i32)),
        (&["c", "c", "a", "a"], one(&i32)),
        (&["c", "a", "a"], vec![]),
        (&["c", "a", "a"], vec![i32.clone(), i32.clone()]),
    ] {
        let o = built("select", &[], operands, &results);
        rejected_at_op(o, SELECT_BUILT, SELECT_TYPES);
    }
    for a in [
        Attr::word("nsw"),
        Attr::word("slt"),
        Attr::int(0),
        Attr::App("x".into(), vec![]),
    ] {
        let o = built("select", &[a], &["c", "a", "a"], &one(&i32));
        rejected_at_op(o, SELECT_BUILT, "select takes no attributes");
    }
}
