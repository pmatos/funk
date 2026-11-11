//! A region kind whose ops are unordered (ADR-2026-11-10-1941), on the
//! shared cases of `tests/dialects/region-kinds.cases`, which
//! `lean/FirTest/RegionKindCases.lean` reads too, so the two validators
//! agree on each of them and both print each case as itself.
//!
//! A test dialect named `toy` has the ops `toy.graph`, which owns one region
//! of the kind `toy.dataflow`, and `toy.node`, which takes any number of
//! values of one type `iN` and gives one of that type. The kind's rule asks
//! for one block with no arguments, whose ops are all `toy`'s, none a
//! terminator, and whose ops use only results of ops of the same block, in
//! any order, and the function's parameters.

use std::collections::HashSet;

use funk_ir::dialects::core::{self, int_width};
use funk_ir::{
    Dialect, Effects, Func, FuncContext, OpShape, OpSpec, OpTypes, Region, RegionKindSpec,
    Registry, parse, print, verify,
};

const CASES: &str = include_str!("../../../tests/dialects/region-kinds.cases");

/// The words of the diagnostic for a region that breaks its kind's rule.
const BREAKS: &str = "breaks the rule of its kind toy.dataflow";

/// `toy.graph`: it takes and gives nothing, and owns one region of the kind
/// `toy.dataflow`.
struct Graph;

impl OpSpec for Graph {
    fn name(&self) -> &str {
        "toy.graph"
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        match (op.attrs, op.operands, op.results) {
            ([], [], []) => Ok(OpShape {
                regions: vec!["toy.dataflow".to_string()],
                ..OpShape::default()
            }),
            _ => Err("toy.graph takes and gives nothing".to_string()),
        }
    }

    fn effects(&self, _op: &OpTypes<'_>) -> Effects {
        Effects::PURE
    }
}

/// `toy.node`: any number of values of one type `iN`, and one result of
/// that type.
struct Node;

impl OpSpec for Node {
    fn name(&self) -> &str {
        "toy.node"
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        match (op.attrs, op.results) {
            ([], [r]) if int_width(r).is_some() && op.operands.iter().all(|t| t == r) => {
                Ok(OpShape::default())
            }
            _ => Err("toy.node takes values of its result's type iN".to_string()),
        }
    }

    fn effects(&self, _op: &OpTypes<'_>) -> Effects {
        Effects::PURE
    }
}

/// The kind `toy.dataflow`, whose ops are unordered.
struct Dataflow;

impl RegionKindSpec for Dataflow {
    fn name(&self) -> &str {
        "toy.dataflow"
    }

    fn check(&self, _cx: &FuncContext<'_>, func: &Func, region: &Region) -> Result<(), String> {
        let [block] = region.blocks.as_slice() else {
            return Err(format!(
                "a dataflow region holds one block, not {}",
                region.blocks.len()
            ));
        };
        if !block.params.is_empty() {
            return Err(format!("^{} takes arguments", block.label));
        }
        if let Some(op) = block.ops.iter().find(|o| !o.name.starts_with("toy.")) {
            return Err(format!("{} is not an op of toy", op.name));
        }
        let defined: HashSet<&str> = block
            .ops
            .iter()
            .flat_map(|o| &o.results)
            .chain(&func.params)
            .map(|d| d.name.as_str())
            .collect();
        match block
            .ops
            .iter()
            .flat_map(|o| &o.operands)
            .find(|x| !defined.contains(x.as_str()))
        {
            Some(x) => Err(format!(
                "%{x} is neither a result of an op of the region nor a parameter"
            )),
            None => Ok(()),
        }
    }
}

fn registry() -> Registry {
    let mut r = Registry::core();
    r.register(
        Dialect::new("toy")
            .depends_on(core::NAME)
            .op(Graph)
            .op(Node)
            .region_kind(Dataflow),
    )
    .expect("the toy dialect registers");
    r
}

#[derive(Clone, Copy, PartialEq, Debug)]
enum Verdict {
    Accept,
    Reject,
    RejectByKind,
}

struct Case {
    verdict: Verdict,
    name: &'static str,
    text: &'static str,
}

fn cases() -> Vec<Case> {
    CASES
        .split("=== ")
        .skip(1)
        .map(|piece| {
            let (head, text) = piece.split_once('\n').expect("a case has a first line");
            let (verdict, name) = head.split_once(' ').expect("a verdict and a name");
            let verdict = match verdict {
                "accept" => Verdict::Accept,
                "reject" => Verdict::Reject,
                "reject-by-kind" => Verdict::RejectByKind,
                v => panic!("{name}: unknown verdict {v}"),
            };
            Case {
                verdict,
                name,
                text,
            }
        })
        .collect()
}

#[test]
fn the_shared_cases_are_all_read() {
    let cases = cases();
    assert_eq!(cases.len(), 16);
    let count = |v| cases.iter().filter(|c| c.verdict == v).count();
    assert_eq!(count(Verdict::Accept), 5);
    assert_eq!(count(Verdict::RejectByKind), 7);
}

#[test]
fn each_case_parses_prints_as_itself_and_gets_its_verdict() {
    let reg = registry();
    for c in cases() {
        let m = parse(c.text, &reg).unwrap_or_else(|e| panic!("{}: {e}", c.name));
        assert_eq!(print(&m), c.text, "{}", c.name);
        let ds = verify(&m, &reg);
        let by_kind = ds.iter().any(|d| d.message.contains(BREAKS));
        match c.verdict {
            Verdict::Accept => assert!(ds.is_empty(), "{}: {ds:#?}", c.name),
            Verdict::Reject => assert!(!ds.is_empty() && !by_kind, "{}: {ds:#?}", c.name),
            Verdict::RejectByKind => assert!(by_kind, "{}: {ds:#?}", c.name),
        }
    }
}

/// The messages of the diagnostics of the case named `name`.
fn messages(reg: &Registry, all: &[Case], name: &str) -> Vec<String> {
    let c = all.iter().find(|c| c.name == name).unwrap();
    verify(&parse(c.text, reg).unwrap(), reg)
        .into_iter()
        .map(|d| d.message)
        .collect()
}

#[test]
fn a_region_that_breaks_the_kind_says_why() {
    let reg = registry();
    let all = cases();
    let prefix = "a region of toy.graph breaks the rule of its kind toy.dataflow: ";
    let unscoped =
        |x: &str| format!("%{x} is neither a result of an op of the region nor a parameter");
    for (case, reason) in [
        (
            "two-blocks",
            "a dataflow region holds one block, not 2".to_string(),
        ),
        ("a-block-argument", "^g takes arguments".to_string()),
        ("a-core-op-inside", "add is not an op of toy".to_string()),
        ("a-terminator-inside", "ret is not an op of toy".to_string()),
        ("a-use-of-a-value-of-the-body", unscoped("s")),
        ("a-use-of-another-graphs-node", unscoped("a")),
        ("a-use-of-the-outer-graphs-node", unscoped("a")),
    ] {
        assert_eq!(
            messages(&reg, &all, case),
            [format!("{prefix}{reason}")],
            "{case}"
        );
    }
}

#[test]
fn a_value_of_a_region_is_not_in_scope_in_the_body() {
    // `lean/FirTest/RegionKindCases.lean` pins the same words.
    assert_eq!(
        messages(&registry(), &cases(), "a-use-of-a-node-in-the-body"),
        ["%a is defined inside a region, and is not in scope here"]
    );
}
