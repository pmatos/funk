//! Programs that the differential harness runs (#165).
//!
//! A program is a module of [`Widths::Backend`], so `funk build` accepts
//! it, with the runs to make of it: argument vectors for each of its
//! functions, often at the boundary values of their types. Its functions
//! come from the generator of random valid modules, so they loop, join,
//! call and recurse, and some of them hit UB or never end. Its bounded
//! functions (`bounded.rs`) loop and recurse for many steps and then end.
//!
//! Each program also holds functions planted to end one way: UB, by a
//! division by zero or a `cond_br` on poison, or a run out of fuel, by a
//! loop or a recursion that never ends. Their runs say what `fir-ref` must
//! report, and native code does not run them.

use super::{BACKEND_WIDTHS, Rng, Widths, bounded, module_of};
use crate::dialects::core::{int_type, int_width};
use crate::ir::{Attr, Block, Func, Int, LocRef, Module, Op, Type};
use crate::text::print_symbol;

/// The fuel of a run that may return. Enough for every run that returns
/// to do so in the common case, and small enough that a loop that never
/// ends is cheap.
pub const FUEL: u64 = 20_000;

/// The fuel of a run planted to run out of it.
const PLANTED_FUEL: u64 = 1_000;

/// How a planted run must end.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Expect {
    Ub,
    FuelExhausted,
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
        match r.expect {
            Some(Expect::Ub) => out.push_str(", expect = \"ub\""),
            Some(Expect::FuelExhausted) => out.push_str(", expect = \"fuel-exhausted\""),
            None => {}
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
        for _ in 0..vectors {
            runs.push(Run {
                func: print_symbol(&f.name),
                args: arguments(rng, f),
                fuel: FUEL,
                expect: None,
            });
        }
    }
    let loc = module.locs.entries[0].0;
    for k in 0..1 + rng.below(2) {
        let name = format!("planted.ub{k}");
        let f = planted_ub(rng, name, loc);
        runs.push(planted_run(rng, &f, PLANTED_FUEL, Expect::Ub));
        module = module.func(f);
    }
    for f in planted_spin(rng, loc) {
        runs.push(planted_run(rng, &f, PLANTED_FUEL, Expect::FuelExhausted));
        module = module.func(f);
    }
    Program { module, runs }
}

fn planted_run(rng: &mut Rng, f: &Func, fuel: u64, expect: Expect) -> Run {
    Run {
        func: print_symbol(&f.name),
        args: arguments(rng, f),
        fuel,
        expect: Some(expect),
    }
}

/// One argument for each parameter of `f`.
fn arguments(rng: &mut Rng, f: &Func) -> Vec<String> {
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

fn zero(w: u32) -> Attr {
    if w == 1 {
        Attr::word("false")
    } else {
        Attr::Int(Int::parse("0").expect("a canonical integer"))
    }
}

/// A function of one parameter whose every run hits UB: a division by
/// zero, or a `cond_br` on poison.
fn planted_ub(rng: &mut Rng, name: String, loc: LocRef) -> Func {
    let w = *rng.pick(&BACKEND_WIDTHS);
    let t = int_type(w);
    let f = Func::new(name).param("x", t.clone());
    if rng.one_in(2) {
        let cond = Op::new("poison", loc).result("c", int_type(1));
        let branch = Op::new("cond_br", loc)
            .operand("c")
            .succ("a", &[])
            .succ("b", &[]);
        let entry = Block::new("entry").op(cond).op(branch);
        let out = |label: &str| Block::new(label).op(Op::new("ret", loc));
        return f.block(entry).block(out("a")).block(out("b"));
    }
    let divide = *rng.pick(&["sdiv", "udiv", "srem", "urem"]);
    let zero = Op::new("const", loc).attr(zero(w)).result("z", t.clone());
    let q = Op::new(divide, loc)
        .operand("x")
        .operand("z")
        .result("q", t.clone());
    let ret = Op::new("ret", loc).operand("q");
    f.result(t)
        .block(Block::new("entry").op(zero).op(q).op(ret))
}

/// One function, or two that call each other, whose every run runs out of
/// fuel: a loop that passes a block argument round, or a recursion.
fn planted_spin(rng: &mut Rng, loc: LocRef) -> Vec<Func> {
    let t = int_type(*rng.pick(&BACKEND_WIDTHS));
    match rng.below(3) {
        0 => vec![spin_loop(t, loc)],
        1 => vec![recursive("planted.self", "planted.self", t, loc)],
        _ => vec![
            recursive("planted.ping", "planted.pong", t.clone(), loc),
            recursive("planted.pong", "planted.ping", t, loc),
        ],
    }
}

fn spin_loop(t: Type, loc: LocRef) -> Func {
    let enter = Op::new("br", loc).succ("loop", &["x"]);
    let step = Op::new("add", loc)
        .operand("a")
        .operand("a")
        .result("b", t.clone());
    let back = Op::new("br", loc).succ("loop", &["b"]);
    Func::new("planted.spin")
        .param("x", t.clone())
        .block(Block::new("entry").op(enter))
        .block(Block::new("loop").param("a", t).op(step).op(back))
}

fn recursive(name: &str, callee: &str, t: Type, loc: LocRef) -> Func {
    let call = Op::new("call", loc)
        .attr(Attr::Sym(callee.into()))
        .operand("x")
        .result("r", t.clone());
    let ret = Op::new("ret", loc).operand("r");
    Func::new(name)
        .param("x", t.clone())
        .result(t)
        .block(Block::new("entry").op(call).op(ret))
}
