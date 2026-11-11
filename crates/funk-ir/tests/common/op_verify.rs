//! The verifier on one op that a builder made: a function whose entry block
//! holds a constant, the op under test at index 1, and `ret %a`. The op
//! tests of each core family share it.

use funk_ir::dialects::core::{int_type, ptr_type};
use funk_ir::{
    Attr, Block, Diagnostic, Func, LocRef, Location, Module, Op, Registry, Type, verify,
};

/// The location reference of the op under test, `@5`.
pub const L: LocRef = LocRef(5);

/// The diagnostics of `@f` with the parameters `params` and one `i32`
/// result, whose entry block holds `%constant: i32 = const 1`, `op` at
/// index 1, and `ret %a`.
pub fn verify_in(params: &[(&str, Type)], constant: &str, op: Op) -> Vec<Diagnostic> {
    let k = Op::new("const", LocRef(0))
        .attr(Attr::int(1))
        .result(constant, int_type(32));
    let f = params
        .iter()
        .fold(Func::new("f"), |f, (n, t)| f.param(*n, t.clone()))
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
    verify(&m.func(f), &Registry::core())
}

/// Asserts that `ds` is one diagnostic at the op under test and its
/// location, which starts with `head` and holds `needle`.
pub fn rejected_at(ds: &[Diagnostic], head: &str, needle: &str) {
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

/// The diagnostics of `@f(%a: i32, %b: i64, %p: ptr) -> i32`, whose entry
/// block holds a constant `%c: i32`, `op` at index 1, and `ret %a`: the
/// function that most families test their ops in.
pub fn verify_op(op: Op) -> Vec<Diagnostic> {
    verify_in(
        &[("a", int_type(32)), ("b", int_type(64)), ("p", ptr_type(0))],
        "c",
        op,
    )
}

/// Asserts that the verifier rejects `op`, in [`verify_op`]'s function,
/// with one diagnostic at the op and its location, for a reason that holds
/// `needle`.
pub fn rejected_at_op(op: Op, needle: &str) {
    let head = format!("op {} does not match its registration", op.name);
    rejected_at(&verify_op(op), &head, needle);
}

/// `op` with these attributes, these operands and results of these types,
/// at `@5`.
pub fn built(op: &str, attrs: &[Attr], operands: &[&str], results: &[Type]) -> Op {
    let o = attrs.iter().fold(Op::new(op, L), |o, a| o.attr(a.clone()));
    let o = operands.iter().fold(o, |o, x| o.operand(*x));
    results
        .iter()
        .enumerate()
        .fold(o, |o, (k, t)| o.result(format!("r{k}"), t.clone()))
}

/// Each of `ws` as a word attribute.
pub fn words(ws: &[&str]) -> Vec<Attr> {
    ws.iter().map(|w| Attr::word(*w)).collect()
}
