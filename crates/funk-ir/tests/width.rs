//! The width changes `zext`, `sext` and `trunc` (#17), through the builder,
//! the verifier, the parser and the printer (`decodeCast` in
//! `lean/Fir/Core/Text.lean`, `Op.Valid` in `lean/Fir/Core/Validation.lean`).
//! A use that does not decode, such as an attribute on `zext`, is a parse
//! error at the op's name in text (ADR-2026-10-30-0815). A width change that
//! decodes but does not strictly widen, or strictly narrow, is a validation
//! error at the op and its location, in text and in IR that a builder made.

mod common;

use common::{one_func, parse_err, parse_ok};
use funk_ir::dialects::core::{WIDTH_CHANGES, int_type};
use funk_ir::{
    Attr, Block, Diagnostic, Func, LocRef, Location, Module, Op, Registry, TextPos, Type, print,
    verify,
};

const WIDTHS: [u32; 9] = [1, 7, 8, 16, 32, 33, 64, 128, 16_777_215];

/// Whether `op` may change `iM` to `iN`: `zext` and `sext` strictly widen,
/// and `trunc` strictly narrows.
fn allowed(op: &str, m: u32, n: u32) -> bool {
    if op == "trunc" { n < m } else { m < n }
}

/// Every width change between two of [`WIDTHS`], the same width included,
/// that validation admits if `valid` and rejects if not, as `(op, M, N)`.
fn changes(valid: bool) -> Vec<(&'static str, u32, u32)> {
    let mut out = Vec::new();
    for op in WIDTH_CHANGES {
        for m in WIDTHS {
            for n in WIDTHS {
                if allowed(op, m, n) == valid {
                    out.push((op, m, n));
                }
            }
        }
    }
    out
}

/// `@OP_M_N(%a: iM) -> iN`, which changes `%a` to `iN` and returns it.
fn change_text(op: &str, m: u32, n: u32) -> String {
    format!(
        "func @{op}_{m}_{n}(%a: i{m}) -> i{n} {{\n^entry:\n  %r: i{n} = {op} %a @0\n  ret %r @0\n}}\n"
    )
}

/// The function of [`change_text`], made with the builder.
fn change_built(op: &str, m: u32, n: u32) -> Func {
    let b = Block::new("entry")
        .op(Op::new(op, LocRef(0)).operand("a").result("r", int_type(n)))
        .op(Op::new("ret", LocRef(0)).operand("r"));
    Func::new(format!("{op}_{m}_{n}"))
        .param("a", int_type(m))
        .result(int_type(n))
        .block(b)
}

#[test]
fn every_valid_width_change_parses_verifies_and_prints() {
    let valid = changes(true);
    assert_eq!(valid.len(), 3 * 36);
    let funcs: Vec<String> = valid
        .iter()
        .map(|(op, m, n)| change_text(op, *m, *n))
        .collect();
    let text = one_func(&funcs.join("\n"));
    let m = parse_ok(&text);
    assert_eq!(verify(&m, &Registry::core()), vec![]);
    assert_eq!(print(&m), text);
    let mut built = Module::new();
    built.locs.push(Location::Unknown);
    for (op, from, to) in &valid {
        built = built.func(change_built(op, *from, *to));
    }
    assert_eq!(built, m);
}

/// `@f(%a: i32, %b: i64, %c: i8, %p: ptr) -> i32` with one op on line 3,
/// then `ret %a`.
fn with_op(op: &str) -> String {
    one_func(&format!(
        "func @f(%a: i32, %b: i64, %c: i8, %p: ptr) -> i32 {{\n^entry:\n  {op} @0\n  ret %a @0\n}}\n"
    ))
}

/// The type that `op` may change `%a: i32` to: `i64` for `zext` and
/// `sext`, `i8` for `trunc`.
fn target(op: &str) -> &'static str {
    if op == "trunc" { "i8" } else { "i64" }
}

#[test]
fn ill_typed_width_changes_are_rejected_at_the_name() {
    let types = "takes one operand of an integer type and defines one value";
    for op in WIDTH_CHANGES {
        let t = target(op);
        let no_attrs = format!("{op} takes no attributes");
        for (line, needle) in [
            (format!("%r: {t} = {op} %a, %a"), types),
            (format!("%r: {t} = {op}"), types),
            (format!("{op} %a"), types),
            (format!("%r: {t}, %s: {t} = {op} %a"), types),
            (format!("%r: ptr = {op} %a"), types),
            (format!("%r: {t} = {op} %p"), types),
            (format!("%r: {t} = {op} nuw %a"), &no_attrs),
            (format!("%r: {t} = {op} nsw %a"), &no_attrs),
            (format!("%r: {t} = {op} exact %a"), &no_attrs),
            (format!("%r: {t} = {op} i64 %a"), &no_attrs),
            (format!("%r: {t} = {op} 1 %a"), &no_attrs),
            (format!("%r: {t} = {op} \"nsw\" %a"), &no_attrs),
            (format!("%r: {t} = {op} @g %a"), &no_attrs),
        ] {
            let e = parse_err(&with_op(&line));
            let col = line.find(" = ").map_or(3, |i| i + 6);
            assert_eq!(e.pos, TextPos { line: 3, col }, "{line}: {e}");
            assert!(e.reason.contains(needle), "{line}: {e} lacks {needle:?}");
            let head = format!("op {op} does not decode");
            assert!(e.reason.starts_with(&head), "{e}");
        }
    }
}

const L: LocRef = LocRef(5);

/// The validation error of `op` from `iM` to `iN`, where validation
/// rejects it.
fn wrong_direction(op: &str, m: u32, n: u32) -> String {
    let rule = if op == "trunc" {
        "strictly narrows, from iM to iN with N < M"
    } else {
        "strictly widens, from iM to iN with M < N"
    };
    format!("{op} {rule}, not from i{m} to i{n}")
}

/// Asserts that `ds` is one diagnostic with `message`, at the op at index
/// `index` of block `^entry` of `@f`, at the location reference `@5`.
fn one_at_op(ds: &[Diagnostic], index: usize, message: &str) {
    assert_eq!(ds.len(), 1, "{message}: {ds:#?}");
    let d = &ds[0];
    assert_eq!(d.message, message);
    assert_eq!(
        (d.func.as_deref(), d.block.as_deref(), d.op, d.loc),
        (Some("f"), Some("entry"), Some(index), Some(L)),
        "{d}"
    );
    assert_eq!(
        d.to_string(),
        format!("@f ^entry op {index} at @5: {message}")
    );
}

#[test]
fn a_width_change_that_does_not_widen_or_narrow_parses_and_fails_validation() {
    let invalid = changes(false);
    assert_eq!(invalid.len(), 3 * 81 - 3 * 36);
    let reg = Registry::core();
    for (op, m, n) in invalid {
        let text = format!(
            "func @f(%a: i{m}) -> i{n} {{\n^entry:\n  %r: i{n} = {op} %a @5\n  ret %r @0\n}}\n\n\
             locs {{\n  @0 = unknown\n  @5 = name(\"here\")\n}}\n"
        );
        let parsed = parse_ok(&text);
        assert_eq!(print(&parsed), text);
        one_at_op(&verify(&parsed, &reg), 0, &wrong_direction(op, m, n));
    }
}

/// The diagnostics of `@f(%a: i32, %b: i64, %c: i8, %p: ptr) -> i32`, whose
/// entry block holds a constant `%k: i32`, `op` at index 1, and `ret %a`,
/// less those that reject a value of the reserved type `ptr`.
fn verify_op(op: Op) -> Vec<Diagnostic> {
    let k = Op::new("const", LocRef(0))
        .attr(Attr::int(1))
        .result("k", int_type(32));
    let f = Func::new("f")
        .param("a", int_type(32))
        .param("b", int_type(64))
        .param("c", int_type(8))
        .param("p", Type::word("ptr"))
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
    ds.retain(|d| !(d.op.is_none() && d.message.contains("ptr is reserved")));
    ds
}

/// `op` with these attributes, these operands and results of these types,
/// at `@5`.
fn built(op: &str, attrs: &[Attr], operands: &[&str], results: &[Type]) -> Op {
    let o = attrs.iter().fold(Op::new(op, L), |o, a| o.attr(a.clone()));
    let o = operands.iter().fold(o, |o, x| o.operand(*x));
    results
        .iter()
        .enumerate()
        .fold(o, |o, (k, t)| o.result(format!("r{k}"), t.clone()))
}

/// The uses that the parser rejects in
/// `ill_typed_width_changes_are_rejected_at_the_name`, made with the
/// builder: each a validation error at the op.
#[test]
fn the_verifier_rejects_ill_typed_width_changes_that_a_builder_made() {
    let ptr = Type::word("ptr");
    for op in WIDTH_CHANGES {
        let t = Type::word(target(op));
        let ok = built(op, &[], &["a"], std::slice::from_ref(&t));
        assert_eq!(verify_op(ok), vec![], "{op}");
        let types = format!(
            "op {op} does not match its registration: {op} takes one operand of an \
             integer type and defines one value of an integer type"
        );
        for (operands, results) in [
            (&["a", "a"][..], std::slice::from_ref(&t)),
            (&[], std::slice::from_ref(&t)),
            (&["a"], &[]),
            (&["a"], &[t.clone(), t.clone()]),
            (&["a"], std::slice::from_ref(&ptr)),
            (&["p"], std::slice::from_ref(&t)),
        ] {
            let ds = verify_op(built(op, &[], operands, results));
            assert_eq!(ds.len(), 1, "{op} {operands:?}: {ds:#?}");
            assert!(ds[0].message.starts_with(&types), "{}", ds[0]);
            assert_eq!((ds[0].op, ds[0].loc), (Some(1), Some(L)), "{}", ds[0]);
        }
        let no_attrs = format!("op {op} does not match its registration: {op} takes no attributes");
        for a in [
            Attr::word("nuw"),
            Attr::word("exact"),
            Attr::int(1),
            Attr::Str("nsw".into()),
            Attr::Sym("g".into()),
        ] {
            let ds = verify_op(built(op, &[a], &["a"], std::slice::from_ref(&t)));
            one_at_op(&ds, 1, &no_attrs);
        }
    }
}

#[test]
fn the_verifier_rejects_width_changes_that_a_builder_made_in_the_wrong_direction() {
    for (op, operand, to) in [
        ("zext", "a", 32),
        ("sext", "a", 32),
        ("trunc", "a", 32),
        ("zext", "b", 32),
        ("sext", "a", 8),
        ("zext", "c", 1),
        ("trunc", "c", 32),
        ("trunc", "a", 64),
    ] {
        let from = match operand {
            "a" => 32,
            "b" => 64,
            _ => 8,
        };
        let o = built(op, &[], &[operand], &[int_type(to)]);
        one_at_op(&verify_op(o), 1, &wrong_direction(op, from, to));
    }
}
