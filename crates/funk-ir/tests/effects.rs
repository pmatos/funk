//! The effects of each core op instance (ADR-2026-11-09-1541), on the shared
//! cases of `tests/dialects/effects.cases`, which
//! `lean/FirTest/EffectCases.lean` reads too, so the registry's sets are
//! `Core.Op.effects`. Each case pins the first op of the entry block of
//! `@f`, which takes its operands from `@f`'s parameters. Each pinned op is
//! control exactly when it is a terminator, as Lean's `notControl` asks.

use std::collections::BTreeSet;

use funk_ir::dialects::core::{self, DIVISION_OPS, WRAP_FLAG_SETS};
use funk_ir::{Attr, Effects, Module, Op, OpTypes, Registry, Type, parse, verify};

const CASES: &str = include_str!("../../../tests/dialects/effects.cases");

struct Case {
    name: &'static str,
    effects: &'static str,
    text: &'static str,
}

fn cases() -> Vec<Case> {
    CASES
        .split("=== ")
        .skip(1)
        .map(|piece| {
            let (head, text) = piece.split_once('\n').expect("a case has a text");
            let (name, effects) = head.split_once(' ').expect("a case names its effects");
            Case {
                name,
                effects,
                text,
            }
        })
        .collect()
}

/// The pinned op of a case, with the types of its operands.
fn pinned(m: &Module) -> (Op, Vec<Type>) {
    let f = m.funcs().find(|f| f.name == "f").expect("the case has @f");
    let op = f.body.blocks[0].ops[0].clone();
    let operands = op
        .operands
        .iter()
        .map(|x| {
            let p = f.params.iter().find(|p| &p.name == x);
            p.expect("an operand is a parameter").ty.clone()
        })
        .collect();
    (op, operands)
}

fn effects_of(reg: &Registry, c: &Case) -> Effects {
    let m = parse(c.text, reg).unwrap_or_else(|e| panic!("{}: {e}", c.name));
    assert_eq!(verify(&m, reg), vec![], "{}", c.name);
    let (op, operands) = pinned(&m);
    let results: Vec<Type> = op.results.iter().map(|d| d.ty.clone()).collect();
    let types = OpTypes {
        attrs: &op.attrs,
        operands: &operands,
        results: &results,
    };
    let effects = reg
        .effects(&op.name, &types)
        .unwrap_or_else(|| panic!("{}: {} is registered", c.name, op.name));
    let spec = reg.op(&op.name).expect("the op is registered");
    let shape = spec.decode(&types).expect("the op decodes");
    assert_eq!(effects.control, shape.terminator, "{}: control", c.name);
    effects
}

#[test]
fn each_core_op_has_the_effects_of_its_lean_declaration() {
    let reg = Registry::core();
    let cs = cases();
    assert_eq!(cs.len(), 36);
    for c in &cs {
        assert_eq!(effects_of(&reg, c).to_string(), c.effects, "{}", c.name);
    }
}

fn words(attrs: &[Attr]) -> Vec<String> {
    attrs
        .iter()
        .filter_map(|a| match a {
            Attr::Word(w) => Some(w.clone()),
            _ => None,
        })
        .collect()
}

/// The cases pin every core op, and every attribute that changes a set: each
/// flag set of `add`, `sub` and `mul`, and `exact` on `sdiv` and `udiv`.
#[test]
fn the_cases_pin_every_core_op_and_every_flag() {
    let reg = Registry::core();
    let pinned: BTreeSet<(String, Vec<String>)> = cases()
        .iter()
        .map(|c| {
            let (op, _) = pinned(&parse(c.text, &reg).expect("the case parses"));
            let flags = if op.name == "icmp" {
                vec![]
            } else {
                words(&op.attrs)
            };
            (op.name, flags)
        })
        .collect();
    let mut want = BTreeSet::new();
    for op in &core::dialect().ops {
        want.insert((op.name().to_string(), vec![]));
    }
    for name in ["add", "sub", "mul"] {
        for flags in WRAP_FLAG_SETS {
            want.insert((name.into(), flags.iter().map(|f| f.to_string()).collect()));
        }
    }
    for (name, exact) in DIVISION_OPS {
        if exact {
            want.insert((name.into(), vec!["exact".into()]));
        }
    }
    assert_eq!(pinned, want);
}

#[test]
fn an_unregistered_op_has_no_effects() {
    let types = OpTypes {
        attrs: &[],
        operands: &[],
        results: &[],
    };
    assert_eq!(Registry::core().effects("toy.make", &types), None);
    assert_eq!(Registry::new().effects("ret", &types), None);
}
