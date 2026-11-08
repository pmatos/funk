//! Programs that the differential harness runs (#165).
//!
//! A program is a module of [`Widths::Backend`], so `funk build` accepts
//! it, with the runs to make of it: argument vectors for each of its
//! functions, often at the boundary values of their types. Its functions
//! come from the generator of random valid modules, so they loop, join,
//! call and recurse, and some of them hit UB or never end. Its bounded
//! functions (`bounded.rs`) loop and recurse for many steps and then end.
//!
//! Some bounded functions are built to stay defined, and their runs must
//! neither hit UB nor run out of fuel: the generator is a second opinion on
//! `fir-ref` there. `planted.rs` adds functions that must end one way.

use super::{Rng, Widths, bounded, module_of, planted};
use crate::dialects::core::int_width;
use crate::ir::{Func, LocRef, Module};
use crate::text::print_symbol;

pub use super::bounded::SAFE_PREFIX;

/// The fuel of a run that may return. Enough for every run that returns
/// to do so in the common case, and small enough that a loop that never
/// ends is cheap.
pub const FUEL: u64 = 20_000;

/// The fuel of a run built to stay defined: more than its loops and calls
/// can take.
pub const SAFE_FUEL: u64 = 1_000_000;

/// How a planted run must end.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expect {
    Ub,
    FuelExhausted,
    /// These values, each a constant or `poison`.
    Values(Vec<String>),
}

/// One run of a function of a program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Run {
    /// The function's symbol, as text writes it.
    pub func: String,
    /// One argument per parameter, spelled as a constant of its type.
    pub args: Vec<String>,
    pub fuel: u64,
    /// How the run must end, when it was planted to.
    pub expect: Option<Expect>,
    /// Built to stay defined: UB, poison or running out of fuel is a failure.
    pub defined: bool,
}

/// A module and the runs to make of it.
#[derive(Clone, Debug)]
pub struct Program {
    pub module: Module,
    pub runs: Vec<Run>,
}

impl Program {
    /// The runs, in the format of a test sidecar of the corpus.
    pub fn sidecar(&self) -> String {
        sidecar_of(&self.runs)
    }
}

/// `runs`, in the format of a test sidecar of the corpus.
pub fn sidecar_of(runs: &[Run]) -> String {
    let mut out = String::from("tests = [\n");
    for r in runs {
        let args: Vec<String> = r.args.iter().map(|a| toml_string(a)).collect();
        out.push_str(&format!(
            "  {{ func = {}, args = [{}], fuel = {}",
            toml_string(&r.func),
            args.join(", "),
            r.fuel
        ));
        match &r.expect {
            Some(Expect::Ub) => out.push_str(", expect = \"ub\""),
            Some(Expect::FuelExhausted) => out.push_str(", expect = \"fuel-exhausted\""),
            Some(Expect::Values(vs)) => {
                let vs: Vec<String> = vs.iter().map(|v| toml_string(v)).collect();
                out.push_str(&format!(", expect = [{}]", vs.join(", ")));
            }
            None => {}
        }
        if r.defined {
            out.push_str(", defined = true");
        }
        out.push_str(" },\n");
    }
    out.push_str("]\n");
    out
}

/// A TOML basic string that holds `s`.
fn toml_string(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            ' '..='~' => out.push(c),
            c if u32::from(c) <= 0xffff => out.push_str(&format!("\\u{:04x}", u32::from(c))),
            c => out.push_str(&format!("\\U{:08x}", u32::from(c))),
        }
    }
    out.push('"');
    out
}

/// A random program.
pub fn program(rng: &mut Rng) -> Program {
    let module = module_of(rng, Widths::Backend);
    let keys: Vec<LocRef> = module.locs.entries.iter().map(|(r, _)| *r).collect();
    let mut module = bounded::add(rng, module, &keys);
    let mut runs = Vec::new();
    for f in module.funcs() {
        let vectors = if f.params.is_empty() {
            1
        } else {
            1 + rng.below(4)
        };
        let safe = f.name.starts_with(SAFE_PREFIX);
        let mut seen: Vec<Vec<String>> = Vec::new();
        for _ in 0..vectors {
            let args = arguments(rng, f);
            if seen.contains(&args) {
                continue;
            }
            seen.push(args.clone());
            runs.push(Run {
                func: print_symbol(&f.name),
                args,
                fuel: if safe { SAFE_FUEL } else { FUEL },
                expect: None,
                defined: safe,
            });
        }
    }
    let loc = module.locs.entries[0].0;
    let mut planted_funcs = Vec::new();
    for k in 0..1 + rng.below(2) {
        planted_funcs.extend(planted::ub_and_near_miss(rng, k, loc));
    }
    planted_funcs.extend(planted::spin(rng, loc));
    for (f, run) in planted_funcs {
        runs.push(run);
        module = module.func(f);
    }
    Program { module, runs }
}

/// One argument for each parameter of `f`.
pub(super) fn arguments(rng: &mut Rng, f: &Func) -> Vec<String> {
    let widths = f.params.iter().map(|d| int_width(&d.ty));
    widths
        .map(|w| argument(rng, w.expect("an integer type")))
        .collect()
}

/// A value of `iN`, often at a boundary, spelled as a constant.
fn argument(rng: &mut Rng, w: u32) -> String {
    if w == 1 {
        return if rng.one_in(2) { "true" } else { "false" }.into();
    }
    let shift = 128 - w;
    let min = i128::MIN >> shift;
    let max = !min;
    let v = match rng.below(6) {
        0 => 0,
        1 => 1,
        2 => -1,
        3 => min,
        4 => max,
        _ => {
            let bits = (u128::from(rng.next_u64()) << 64) | u128::from(rng.next_u64());
            ((bits as i128) << shift) >> shift
        }
    };
    v.to_string()
}
