//! Checks of the programs that the differential harness runs (#165).

use std::collections::HashSet;

use funk_ir::dialects::core::int_width;
use funk_ir::generate::program::{self, Expect, Program};
use funk_ir::generate::{BACKEND_WIDTHS, Rng};
use funk_ir::text::print_symbol;
use funk_ir::{Attr, Module, Op, Registry, print, verify};

const SEEDS: u64 = 400;

fn programs() -> impl Iterator<Item = (u64, Program)> {
    (0..SEEDS).map(|seed| (seed, program::program(&mut Rng::new(seed))))
}

fn ops(m: &Module) -> impl Iterator<Item = (&str, &Op)> {
    m.funcs().flat_map(|f| {
        f.body
            .blocks
            .iter()
            .flat_map(move |b| b.ops.iter().map(move |o| (f.name.as_str(), o)))
    })
}

#[test]
fn programs_are_valid_and_deterministic() {
    let reg = Registry::core();
    for (seed, p) in programs() {
        assert_eq!(verify(&p.module, &reg), vec![], "seed {seed}");
        let again = program::program(&mut Rng::new(seed));
        assert_eq!(print(&p.module), print(&again.module), "seed {seed}");
        assert_eq!(p.sidecar(), again.sidecar(), "seed {seed}");
    }
}

#[test]
fn programs_take_only_the_widths_that_the_backend_lowers() {
    for (seed, p) in programs() {
        for f in p.module.funcs() {
            let types = f.params.iter().map(|d| &d.ty).chain(&f.results);
            for t in types {
                let w = int_width(t).expect("an integer type");
                assert!(BACKEND_WIDTHS.contains(&w), "seed {seed}: i{w}");
            }
        }
        for (_, o) in ops(&p.module) {
            for d in &o.results {
                let w = int_width(&d.ty).expect("an integer type");
                assert!(BACKEND_WIDTHS.contains(&w), "seed {seed}: i{w}");
            }
        }
    }
}

#[test]
fn every_function_runs_on_arguments_of_its_types() {
    for (seed, p) in programs() {
        let mut ran = HashSet::new();
        let symbols: Vec<String> = p.module.funcs().map(|f| print_symbol(&f.name)).collect();
        for r in &p.runs {
            let f = p
                .module
                .funcs()
                .find(|f| print_symbol(&f.name) == r.func)
                .unwrap_or_else(|| panic!("seed {seed}: no function {}", r.func));
            assert_eq!(r.args.len(), f.params.len(), "seed {seed}: {}", r.func);
            for (a, d) in r.args.iter().zip(&f.params) {
                let w = int_width(&d.ty).expect("an integer type");
                if w == 1 {
                    assert!(a == "true" || a == "false", "seed {seed}: {a}");
                } else {
                    let v: i128 = a.parse().unwrap_or_else(|_| panic!("seed {seed}: {a}"));
                    if w < 128 {
                        let bound = 1i128 << (w - 1);
                        assert!((-bound..bound).contains(&v), "seed {seed}: {a} at i{w}");
                    }
                }
            }
            ran.insert(r.func.clone());
        }
        for s in symbols {
            assert!(ran.contains(&s), "seed {seed}: {s} never runs");
        }
    }
}

#[test]
fn some_runs_are_planted_to_end_in_ub_and_some_to_run_out_of_fuel() {
    let (mut ub, mut fuel) = (0, 0);
    for (_, p) in programs() {
        ub += p
            .runs
            .iter()
            .filter(|r| r.expect == Some(Expect::Ub))
            .count();
        fuel += p
            .runs
            .iter()
            .filter(|r| r.expect == Some(Expect::FuelExhausted))
            .count();
    }
    assert!(ub >= SEEDS as usize / 4, "{ub} planted UB runs");
    assert!(fuel >= SEEDS as usize / 4, "{fuel} planted fuel runs");
}

#[test]
fn programs_have_what_the_harness_must_run() {
    let (mut freezes, mut poisons, mut calls, mut recursion, mut branches) = (0, 0, 0, 0, 0);
    for (_, p) in programs() {
        for (caller, o) in ops(&p.module) {
            match o.name.as_str() {
                "freeze" => freezes += 1,
                "poison" => poisons += 1,
                "cond_br" => branches += 1,
                "call" => {
                    calls += 1;
                    if o.attrs
                        .iter()
                        .any(|a| matches!(a, Attr::Sym(s) if s == caller))
                    {
                        recursion += 1;
                    }
                }
                _ => {}
            }
        }
    }
    for (what, n) in [
        ("freeze", freezes),
        ("poison", poisons),
        ("call", calls),
        ("recursive call", recursion),
        ("cond_br", branches),
    ] {
        assert!(n >= 50, "{n} of {what}");
    }
}

#[test]
fn programs_hold_functions_that_iterate_and_end() {
    let (mut loops, mut selves, mut pairs) = (0, 0, 0);
    for (seed, p) in programs() {
        let names: Vec<&str> = p.module.funcs().map(|f| f.name.as_str()).collect();
        assert!(
            names.iter().any(|n| n.starts_with("bounded.")),
            "seed {seed}: no bounded function"
        );
        loops += names
            .iter()
            .filter(|n| n.starts_with("bounded.loop"))
            .count();
        selves += names
            .iter()
            .filter(|n| n.starts_with("bounded.self"))
            .count();
        pairs += names
            .iter()
            .filter(|n| n.starts_with("bounded.even"))
            .count();
    }
    for (what, n) in [
        ("loop", loops),
        ("recursion", selves),
        ("mutual recursion", pairs),
    ] {
        assert!(n >= 50, "{n} of {what}");
    }
}

#[test]
fn the_sidecar_spells_a_quoted_symbol_with_escapes() {
    let run = program::Run {
        func: "@\"a\\\"b\n\"".into(),
        args: vec!["-1".into()],
        fuel: 7,
        expect: Some(Expect::Ub),
    };
    assert_eq!(
        program::sidecar_of(&[run]),
        "tests = [\n  { func = \"@\\\"a\\\\\\\"b\\u000a\\\"\", args = [\"-1\"], fuel = 7, expect = \"ub\" },\n]\n"
    );
}
