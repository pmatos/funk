//! Division and remainder: `sdiv` and `udiv` with and without `exact`,
//! `srem` and `urem` (#18), through the builder, the verifier, the parser
//! and the printer (`Op.decode` and `decodeExact` in
//! `lean/Fir/Core/Text.lean`). In text, a use that does not decode is a
//! parse error at the op's name (ADR-2026-10-30-0815); in IR that a builder
//! made, it is a validation error at the op and its location.

mod common;

use common::{one_func, parse_err, parse_ok};
use funk_ir::dialects::core::{DIVISION_OPS, int_type};
use funk_ir::{
    Attr, Block, Diagnostic, Func, LocRef, Location, Module, Op, Registry, TextPos, Type, print,
    verify,
};

/// Each op as the text writes it, with each set of its flags: `sdiv`,
/// `sdiv exact`, `udiv`, `udiv exact`, `srem` and `urem`.
fn spellings() -> Vec<(&'static str, &'static [&'static str])> {
    let mut out = Vec::new();
    for (op, exact) in DIVISION_OPS {
        out.push((op, &[][..]));
        if exact {
            out.push((op, &["exact"][..]));
        }
    }
    out
}

/// `@f(%a: iW, %b: iW) -> iW`: each op with each set of flags, of `%a` by
/// `%b`, then `ret` of the last result.
fn every_op_text(w: u32) -> String {
    let mut text = format!("func @f(%a: i{w}, %b: i{w}) -> i{w} {{\n^entry:\n");
    let ops = spellings();
    for (n, (op, flags)) in ops.iter().enumerate() {
        let words: Vec<&str> = std::iter::once(*op).chain(flags.iter().copied()).collect();
        text += &format!("  %r{n}: i{w} = {} %a, %b @0\n", words.join(" "));
    }
    text += &format!("  ret %r{} @0\n}}\n", ops.len() - 1);
    one_func(&text)
}

/// The module of [`every_op_text`], made with the builder.
fn every_op_built(w: u32) -> Module {
    let t = int_type(w);
    let mut b = Block::new("entry");
    let ops = spellings();
    for (n, (op, flags)) in ops.iter().enumerate() {
        let o = flags
            .iter()
            .fold(Op::new(*op, LocRef(0)), |o, f| o.attr(Attr::word(*f)));
        b = b.op(o
            .operand("a")
            .operand("b")
            .result(format!("r{n}"), t.clone()));
    }
    b = b.op(Op::new("ret", LocRef(0)).operand(format!("r{}", ops.len() - 1)));
    let f = Func::new("f")
        .param("a", t.clone())
        .param("b", t.clone())
        .result(t);
    let mut m = Module::new();
    m.locs.push(Location::Unknown);
    m.func(f.block(b))
}

#[test]
fn every_op_and_flag_parses_verifies_and_prints_at_any_width() {
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
fn a_division_that_is_ub_when_it_runs_is_valid() {
    // A zero divisor and the signed minimum by -1 are UB when they run,
    // and a broken `exact` gives poison: none of them is an error.
    let reg = Registry::core();
    for (w, a, b) in [
        (1, "true", "false"),
        (1, "true", "true"),
        (8, "5", "0"),
        (8, "-128", "-1"),
        (8, "7", "2"),
        (64, "-9223372036854775808", "-1"),
    ] {
        for (op, flags) in spellings() {
            let words: Vec<&str> = std::iter::once(op).chain(flags.iter().copied()).collect();
            let text = one_func(&format!(
                "func @f() -> i{w} {{\n^entry:\n  %a: i{w} = const {a} @0\n  \
                 %b: i{w} = const {b} @0\n  %r: i{w} = {} %a, %b @0\n  ret %r @0\n}}\n",
                words.join(" ")
            ));
            let m = parse_ok(&text);
            assert_eq!(verify(&m, &reg), vec![], "{text}");
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
    for (op, flags) in spellings() {
        let op = std::iter::once(op)
            .chain(flags.iter().copied())
            .collect::<Vec<_>>()
            .join(" ");
        let name = op.split(' ').next().unwrap_or_default();
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
            rejected_at_name(&line, name, types);
        }
    }
}

#[test]
fn exact_is_a_flag_of_sdiv_and_udiv_only_and_comes_once() {
    for op in ["sdiv", "udiv"] {
        for (attrs, needle) in [
            ("exact exact", "exact more than once"),
            ("exact exact exact", "exact more than once"),
            ("nuw", "flag is exact, not nuw"),
            ("nsw", "flag is exact, not nsw"),
            ("exact nsw", "flag is exact, not nsw"),
            ("nuw exact", "flag is exact, not nuw"),
            ("1", "attributes are its flag exact"),
            ("\"exact\"", "attributes are its flag exact"),
            ("@exact", "attributes are its flag exact"),
            ("exact()", "attributes are its flag exact"),
            ("exact(1)", "attributes are its flag exact"),
        ] {
            rejected_at_name(&format!("%r: i32 = {op} {attrs} %a, %a"), op, needle);
        }
    }
    for op in ["srem", "urem"] {
        for attrs in [
            "exact",
            "exact exact",
            "nuw",
            "nsw",
            "1",
            "\"exact\"",
            "@x",
            "exact()",
        ] {
            let line = format!("%r: i32 = {op} {attrs} %a, %a");
            rejected_at_name(&line, op, "takes no attributes");
        }
    }
    let reg = Registry::core();
    for (line, ok) in [
        ("%r: i32 = sdiv %a, %a", true),
        ("%r: i32 = sdiv exact %a, %a", true),
        ("%r: i32 = udiv exact %a, %a", true),
        ("%r: i32 = srem exact %a, %a", false),
        ("%r: i32 = urem exact %a, %a", false),
        ("%r: i32 = add exact %a, %a", false),
    ] {
        let text = with_op(line);
        let parsed = funk_ir::parse(&text, &reg);
        assert_eq!(parsed.is_ok(), ok, "{line}: {parsed:?}");
        if let Ok(m) = parsed {
            assert_eq!(print(&m), text);
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

/// The uses that the parser rejects above, made with the builder.
#[test]
fn the_verifier_rejects_ill_typed_divisions_that_a_builder_made() {
    let (i32, i64, ptr) = (int_type(32), int_type(64), Type::word("ptr"));
    let types = "takes two operands of one integer type";
    for (op, flags) in spellings() {
        let attrs = words(flags);
        let ok = built(op, &attrs, &["a", "c"], std::slice::from_ref(&i32));
        assert_eq!(verify_op(ok), vec![], "{op} {flags:?}");
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
            rejected_at_op(built(op, &attrs, operands, results), types);
        }
    }
    let flag = "its flag exact";
    for op in ["sdiv", "udiv"] {
        for (attrs, needle) in [
            (words(&["exact", "exact"]), "exact more than once"),
            (words(&["nsw"]), "flag is exact, not nsw"),
            (words(&["exact", "nuw"]), "flag is exact, not nuw"),
            (vec![Attr::int(1)], flag),
            (vec![Attr::Str("exact".into())], flag),
            (vec![Attr::Sym("exact".into())], flag),
            (vec![Attr::App("exact".into(), vec![])], flag),
        ] {
            let o = built(op, &attrs, &["a", "a"], std::slice::from_ref(&i32));
            rejected_at_op(o, needle);
        }
    }
    for op in ["srem", "urem"] {
        for attrs in [
            words(&["exact"]),
            words(&["nuw"]),
            vec![Attr::int(0)],
            vec![Attr::App("exact".into(), vec![])],
        ] {
            let o = built(op, &attrs, &["a", "a"], std::slice::from_ref(&i32));
            rejected_at_op(o, &format!("{op} takes no attributes"));
        }
    }
}
