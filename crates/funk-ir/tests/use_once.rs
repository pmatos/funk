//! A test-only dialect with a use-once rule, registered from outside
//! `funk-ir`: the result of `toy.once` is used exactly once in its function,
//! by an op of any dialect, or by a branch that passes it to a block. No rule
//! of one op can state that, so it is a [`FuncSpec`].
//!
//! The cases are in `tests/dialects/use-once.cases`, and
//! `lean/FirTest/UseOnce.lean` reads the same file, so the two validators
//! agree on each of them.

use funk_ir::dialects::core::{self, int_width};
use funk_ir::{
    Block, Diagnostic, Dialect, Effects, Func, FuncContext, FuncSpec, LocRef, Op, OpShape, OpSpec,
    OpTypes, Registry, parse, verify,
};

const CASES: &str = include_str!("../../../tests/dialects/use-once.cases");

struct Once;

impl OpSpec for Once {
    fn name(&self) -> &str {
        "toy.once"
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        match (op.attrs, op.operands, op.results) {
            ([], [], [r]) if int_width(r).is_some() => Ok(OpShape::default()),
            _ => Err("toy.once takes nothing and gives one integer".into()),
        }
    }

    fn effects(&self, _op: &OpTypes<'_>) -> Effects {
        Effects::PURE
    }
}

struct Sink;

impl OpSpec for Sink {
    fn name(&self) -> &str {
        "toy.sink"
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        match (op.attrs, op.operands, op.results) {
            ([], [t], []) if int_width(t).is_some() => Ok(OpShape::default()),
            _ => Err("toy.sink takes one integer and gives nothing".into()),
        }
    }

    fn effects(&self, _op: &OpTypes<'_>) -> Effects {
        Effects::PURE
    }
}

/// Every op of the blocks, at any depth.
fn ops(blocks: &[Block]) -> Vec<&Op> {
    let mut out = Vec::new();
    let mut pending: Vec<&Block> = blocks.iter().rev().collect();
    while let Some(b) = pending.pop() {
        for op in &b.ops {
            out.push(op);
            pending.extend(op.regions.iter().rev().flat_map(|r| r.blocks.iter().rev()));
        }
    }
    out
}

struct UseOnce;

impl FuncSpec for UseOnce {
    fn check(&self, _cx: &FuncContext<'_>, func: &Func) -> Result<(), String> {
        let ops = ops(&func.body.blocks);
        for def in ops
            .iter()
            .filter(|o| o.name == "toy.once")
            .flat_map(|o| &o.results)
        {
            let uses = ops
                .iter()
                .flat_map(|o| {
                    o.operands
                        .iter()
                        .chain(o.succs.iter().flat_map(|s| &s.args))
                })
                .filter(|x| **x == def.name)
                .count();
            if uses != 1 {
                return Err(format!(
                    "%{} is used {uses} times, and must be used exactly once",
                    def.name
                ));
            }
        }
        Ok(())
    }
}

fn registry() -> Registry {
    let mut r = Registry::core();
    r.register(
        Dialect::new("toy")
            .depends_on(core::NAME)
            .op(Once)
            .op(Sink)
            .func_rule(UseOnce),
    )
    .expect("the use-once dialect registers");
    r
}

struct Case {
    accept: bool,
    name: &'static str,
    text: String,
}

fn cases() -> Vec<Case> {
    CASES
        .split("=== ")
        .skip(1)
        .map(|piece| {
            let (head, text) = piece.split_once('\n').expect("a case has a first line");
            let (verdict, name) = head.split_once(' ').expect("a verdict and a name");
            Case {
                accept: verdict == "accept",
                name,
                text: text.to_string(),
            }
        })
        .collect()
}

#[test]
fn the_shared_cases_are_all_read() {
    let cases = cases();
    assert_eq!(cases.len(), 9);
    assert_eq!(cases.iter().filter(|c| c.accept).count(), 4);
}

#[test]
fn the_verifier_runs_the_function_rule_and_reports_where() {
    let reg = registry();
    for c in cases() {
        let m = parse(&c.text, &reg).unwrap_or_else(|e| panic!("{}: {e}", c.name));
        let ds = verify(&m, &reg);
        if c.accept {
            assert_eq!(ds, Vec::<Diagnostic>::new(), "{}", c.name);
        } else {
            assert_eq!(ds.len(), 1, "{}: {ds:#?}", c.name);
            let d = &ds[0];
            assert!(
                d.message.contains("must be used exactly once"),
                "{}: {d}",
                c.name
            );
            assert_eq!(d.func.as_deref(), Some("f"), "{}", c.name);
            assert_eq!(d.block.as_deref(), Some("entry"), "{}", c.name);
            assert_eq!(d.op, None, "{}", c.name);
            assert_eq!(d.loc, Some(LocRef(1)), "{}", c.name);
        }
    }
}

#[test]
fn the_core_dialect_alone_has_no_function_rule() {
    assert_eq!(Registry::core().func_rules().count(), 0);
}
