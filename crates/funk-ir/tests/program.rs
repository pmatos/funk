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
fn no_run_is_made_twice() {
    for (seed, p) in programs() {
        let mut seen = HashSet::new();
        for r in &p.runs {
            assert!(
                seen.insert((r.func.clone(), r.args.clone())),
                "seed {seed}: {} {:?} runs twice",
                r.func,
                r.args
            );
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
            names
                .iter()
                .any(|n| n.starts_with("bounded.") || n.starts_with(program::SAFE_PREFIX)),
            "seed {seed}: no bounded function"
        );
        loops += names.iter().filter(|n| n.contains(".loop")).count();
        selves += names.iter().filter(|n| n.contains(".self")).count();
        pairs += names.iter().filter(|n| n.contains(".even")).count();
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
fn every_program_has_a_function_built_to_stay_defined() {
    for (seed, p) in programs() {
        assert!(
            p.module
                .funcs()
                .any(|f| f.name.starts_with(program::SAFE_PREFIX)),
            "seed {seed}: no function built to stay defined"
        );
        for r in &p.runs {
            let safe = r.func.starts_with(&format!("@{}", program::SAFE_PREFIX))
                || r.func.starts_with(&format!("@\"{}", program::SAFE_PREFIX));
            assert_eq!(r.defined, safe, "seed {seed}: {}", r.func);
            if safe {
                assert_eq!(r.fuel, program::SAFE_FUEL, "seed {seed}: {}", r.func);
                assert_eq!(r.expect, None, "seed {seed}: {}", r.func);
            }
        }
    }
}

/// A function built to stay defined has no op that makes poison or UB on
/// defined operands: no `poison`, no flag, and each shift amount and
/// divisor comes from a mask. It calls only functions like itself.
#[test]
fn a_function_built_to_stay_defined_holds_only_ops_that_stay_defined() {
    let mut shifts = 0;
    let mut divisions = 0;
    for (seed, p) in programs() {
        for (caller, o) in ops(&p.module) {
            if !caller.starts_with(program::SAFE_PREFIX) {
                continue;
            }
            assert_ne!(o.name, "poison", "seed {seed}: {caller}");
            for a in &o.attrs {
                let flag = [Attr::word("nuw"), Attr::word("nsw"), Attr::word("exact")];
                assert!(!flag.contains(a), "seed {seed}: {caller}: {}", o.name);
                if o.name == "call" {
                    let Attr::Sym(callee) = a else { continue };
                    assert!(
                        callee.starts_with(program::SAFE_PREFIX),
                        "seed {seed}: {caller} calls {callee}"
                    );
                }
            }
            match o.name.as_str() {
                "shl" | "lshr" | "ashr" => shifts += 1,
                "sdiv" | "udiv" | "srem" | "urem" => divisions += 1,
                _ => {}
            }
        }
    }
    assert!(shifts >= 50, "{shifts} shifts");
    assert!(divisions >= 50, "{divisions} divisions");
}

/// Every kind of UB is planted, each beside a near miss with a known result.
#[test]
fn every_kind_of_ub_is_planted_beside_a_near_miss() {
    let (mut by_zero, mut by_poison, mut min_by_minus_one, mut poison_by_minus_one) = (0, 0, 0, 0);
    let (mut branch, mut near_misses, mut poison_results) = (0, 0, 0);
    for (_, p) in programs() {
        for f in p.module.funcs() {
            if !f.name.starts_with("planted.ub") {
                continue;
            }
            let mut names: Vec<&str> = f.body.blocks[0]
                .ops
                .iter()
                .map(|o| o.name.as_str())
                .collect();
            names.pop();
            match names.as_slice() {
                ["poison"] => branch += 1,
                ["const", d] if d.contains("div") || d.contains("rem") => by_zero += 1,
                ["poison", d] if d.contains("div") || d.contains("rem") => by_poison += 1,
                ["const", "const", _] => min_by_minus_one += 1,
                ["poison", "const", _] => poison_by_minus_one += 1,
                other => panic!("a planted UB of an unknown shape: {other:?}"),
            }
        }
        for r in &p.runs {
            if let Some(Expect::Values(v)) = &r.expect {
                near_misses += 1;
                if v.iter().any(|x| x == "poison") {
                    poison_results += 1;
                }
            }
        }
    }
    for (what, n) in [
        ("division by zero", by_zero),
        ("division by poison", by_poison),
        ("signed minimum by -1", min_by_minus_one),
        ("poison by -1", poison_by_minus_one),
        ("branch on poison", branch),
        ("near misses", near_misses),
        ("near misses that give poison", poison_results),
    ] {
        assert!(n >= 10, "{n} of {what}");
    }
}

#[test]
fn the_sidecar_writes_a_defined_run_and_a_near_miss() {
    let runs = [
        program::Run {
            func: "@f".into(),
            args: vec![],
            fuel: 7,
            expect: None,
            defined: true,
        },
        program::Run {
            func: "@g".into(),
            args: vec![],
            fuel: 7,
            expect: Some(Expect::Values(vec!["-5".into(), "poison".into()])),
            defined: false,
        },
    ];
    assert_eq!(
        program::sidecar_of(&runs),
        "tests = [\n  { func = \"@f\", args = [], fuel = 7, defined = true },\n  { func = \"@g\", args = [], fuel = 7, expect = [\"-5\", \"poison\"] },\n]\n"
    );
}

#[test]
fn the_sidecar_spells_a_quoted_symbol_with_escapes() {
    let run = program::Run {
        func: "@\"a\\\"b\n\"".into(),
        args: vec!["-1".into()],
        fuel: 7,
        expect: Some(Expect::Ub),
        defined: false,
    };
    assert_eq!(
        program::sidecar_of(&[run]),
        "tests = [\n  { func = \"@\\\"a\\\\\\\"b\\u000a\\\"\", args = [\"-1\"], fuel = 7, expect = \"ub\" },\n]\n"
    );
}
