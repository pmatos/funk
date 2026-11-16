//! Checks of the float functions of generated programs (#219).

use std::collections::HashSet;

use funk_ir::dialects::core::{float_format, read_float};
use funk_ir::generate::Rng;
use funk_ir::generate::program::{self, FLOAT_PREFIX, MAX_FLOAT_RESULTS, MAX_NAN_OPS, Program};
use funk_ir::text::print_symbol;
use funk_ir::{Func, Op};

const SEEDS: u64 = 400;

/// The ops of a float function that may make a NaN choice.
const NAN_OPS: [&str; 12] = [
    "fadd", "fsub", "fmul", "fdiv", "frem", "fmod", "sqrt", "fma", "fneg", "fabs", "fpext",
    "fptrunc",
];

fn programs() -> impl Iterator<Item = (u64, Program)> {
    (0..SEEDS).map(|seed| (seed, program::program(&mut Rng::new(seed))))
}

fn float_funcs(p: &Program) -> impl Iterator<Item = &Func> {
    p.module
        .funcs()
        .filter(|f| f.name.starts_with(FLOAT_PREFIX))
}

fn ops(f: &Func) -> impl Iterator<Item = &Op> {
    f.body.blocks.iter().flat_map(|b| &b.ops)
}

/// The budget of a generated run is 10 bits (`CHOICE_BITS` in
/// `scripts/harness/programs.py`). A NaN choice costs `bitsFor(1 + k)` bits
/// on the run that tries native code's `k` NaNs, one per float result.
#[test]
fn a_float_function_stays_within_the_budget_of_a_generated_run() {
    let bits_for = |n: usize| (2 * n - 1).ilog2() as usize;
    assert!(MAX_NAN_OPS * bits_for(1 + MAX_FLOAT_RESULTS) <= 10);
    for (seed, p) in programs() {
        for f in float_funcs(&p) {
            assert_eq!(f.body.blocks.len(), 1, "seed {seed}: {}", f.name);
            let nan_ops = ops(f).filter(|o| NAN_OPS.contains(&o.name.as_str()));
            assert!(nan_ops.count() <= MAX_NAN_OPS, "seed {seed}: {}", f.name);
            let floats = f.results.iter().filter(|t| float_format(t).is_some());
            assert!(
                floats.count() <= MAX_FLOAT_RESULTS,
                "seed {seed}: {}",
                f.name
            );
        }
    }
}

/// No integer op computes on a NaN's bits, no op carries a fast-math flag,
/// and every value an op defines reaches `ret`.
#[test]
fn a_float_function_holds_only_float_ops_and_uses_every_value() {
    let allowed = |n: &str| NAN_OPS.contains(&n) || ["const", "fcmp", "ret"].contains(&n);
    for (seed, p) in programs() {
        for f in float_funcs(&p) {
            let mut used = HashSet::new();
            for o in ops(f) {
                assert!(allowed(&o.name), "seed {seed}: {}: {}", f.name, o.name);
                for flag in ["nnan", "ninf", "nsz"] {
                    let word = funk_ir::Attr::word(flag);
                    assert!(!o.attrs.contains(&word), "seed {seed}: {}", f.name);
                }
                used.extend(o.operands.iter().cloned());
            }
            for o in ops(f) {
                for d in &o.results {
                    assert!(
                        used.contains(&d.name),
                        "seed {seed}: {}: %{}",
                        f.name,
                        d.name
                    );
                }
            }
        }
    }
}

#[test]
fn every_program_has_float_functions_at_both_formats_with_their_runs() {
    let mut formats = HashSet::new();
    let mut counts = std::collections::HashMap::new();
    for (seed, p) in programs() {
        assert!(float_funcs(&p).next().is_some(), "seed {seed}");
        for f in float_funcs(&p) {
            formats.extend(f.params.iter().filter_map(|d| float_format(&d.ty)));
            let symbol = print_symbol(&f.name);
            let runs: Vec<_> = p.runs.iter().filter(|r| r.func == symbol).collect();
            assert!(!runs.is_empty(), "seed {seed}: {} never runs", f.name);
            for r in runs {
                assert!(!r.defined && r.expect.is_none(), "seed {seed}: {}", f.name);
            }
            for o in ops(f) {
                *counts.entry(o.name.clone()).or_insert(0) += 1;
            }
        }
    }
    assert_eq!(formats, HashSet::from([(8, 23), (11, 52)]));
    for name in NAN_OPS.iter().chain(&["const", "fcmp"]) {
        let n = counts.get(*name).copied().unwrap_or(0);
        assert!(n >= 20, "{n} of {name}");
    }
}

/// The arguments often hold the values where floats go wrong.
#[test]
fn float_arguments_hold_nans_infinities_and_zeros() {
    let (mut quiet, mut signalling, mut infinities, mut zeros, mut negative) = (0, 0, 0, 0, 0);
    for (_, p) in programs() {
        for f in float_funcs(&p) {
            let symbol = print_symbol(&f.name);
            let (e, m) = float_format(&f.params[0].ty).expect("a float");
            for r in p.runs.iter().filter(|r| r.func == symbol) {
                for a in &r.args {
                    let b = read_float(e, m, a).expect("a float literal");
                    let exp = (b >> m) & ((1 << e) - 1);
                    let mantissa = b & ((1 << m) - 1);
                    let top = exp == (1 << e) - 1;
                    match (top, mantissa, mantissa >> (m - 1)) {
                        (true, 0, _) => infinities += 1,
                        (true, _, 1) => quiet += 1,
                        (true, _, _) => signalling += 1,
                        _ if exp == 0 && mantissa == 0 => zeros += 1,
                        _ => {}
                    }
                    negative += usize::from(b >> (e + m) == 1);
                }
            }
        }
    }
    for (what, n) in [
        ("quiet NaN", quiet),
        ("signalling NaN", signalling),
        ("infinity", infinities),
        ("zero", zeros),
        ("negative", negative),
    ] {
        assert!(n >= 50, "{n} of {what}");
    }
}
