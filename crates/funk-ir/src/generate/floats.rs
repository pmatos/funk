//! Float functions of a generated program (#219).
//!
//! Each function computes at `f32` or `f64`, the formats that the backend
//! lowers, on arguments that are often a zero, an infinity, a quiet or a
//! signalling NaN with a payload, or a boundary value. Its body is one
//! block: a chain of float ops, each of which takes the value before it as
//! its first operand, so every op's result reaches `ret`. The ops are the
//! arithmetic ops and `fpext` and `fptrunc` between the two formats, whose
//! other operands are parameters, earlier values or float constants. Each
//! may make a NaN choice (ADR-2026-11-09-1549), which the harness judges on
//! the NaNs that `fir-ref` tries (ADR-2026-11-16-1630). A function may also
//! return `fcmp` of the chain's last value and another.
//!
//! A run never computes on a NaN's bits with an integer op, has no
//! fast-math flag and no UB, and makes no choice but NaN choices: its
//! results are float values and `fcmp` results.
//!
//! Each NaN choice costs no bit on the harness's first run of `fir-ref`,
//! and `bitsFor(1 + k)` bits on its second, which tries the `k` NaNs that
//! native code returned. A function has at most [`MAX_FLOAT_RESULTS`] float
//! results, so `k <= 2` and a choice costs at most 2 bits, and at most
//! [`MAX_NAN_OPS`] ops that may choose a NaN, so a path charges at most 10
//! bits: the budget of a generated run (`CHOICE_BITS` in
//! `scripts/harness/programs.py`).

use super::Rng;
use super::program::{FUEL, Run};
use crate::dialects::core::{FLOAT_PREDICATES, float_format, float_type, int_type, spell_float};
use crate::ir::{Attr, Block, Func, LocRef, Op, Type};
use crate::text::print_symbol;

/// The most ops of a float function that may make a NaN choice.
pub const MAX_NAN_OPS: usize = 5;

/// The most float results of a float function.
pub const MAX_FLOAT_RESULTS: usize = 2;

/// The start of the name of a float function.
pub const FLOAT_PREFIX: &str = "float.";

/// The formats that the backend lowers, as `(e, m)`.
const FORMATS: [(u32, u32); 2] = [(8, 23), (11, 52)];

/// The arithmetic ops: each name, its number of operands, and whether it
/// rounds.
const ARITH: [(&str, usize, bool); 10] = [
    ("fadd", 2, true),
    ("fsub", 2, true),
    ("fmul", 2, true),
    ("fdiv", 2, true),
    ("frem", 2, false),
    ("fmod", 2, false),
    ("sqrt", 1, true),
    ("fma", 3, true),
    ("fneg", 1, false),
    ("fabs", 1, false),
];

fn round() -> Attr {
    Attr::App("round".into(), vec![Attr::word("rne")])
}

/// Bits of `float<e,m>`, often a special value: a zero, one, an infinity,
/// a quiet or signalling NaN, either with a payload, the smallest
/// subnormal, the smallest normal or the largest finite value, each of
/// either sign.
fn special_bits(rng: &mut Rng, e: u32, m: u32) -> u128 {
    let width = 1 + e + m;
    let sign = if rng.one_in(2) { 1u128 << (e + m) } else { 0 };
    let exp_ones = ((1u128 << e) - 1) << m;
    let quiet = 1u128 << (m - 1);
    let payload = u128::from(rng.next_u64()) & (quiet - 1);
    let magnitude = match rng.below(12) {
        0 => 0,
        1 => ((1u128 << (e - 1)) - 1) << m,
        2 => exp_ones,
        3 => exp_ones | quiet,
        4 => exp_ones | quiet | payload,
        5 => exp_ones | payload.max(1),
        6 => 1,
        7 => 1 << m,
        8 => exp_ones - 1,
        _ => {
            let bits = (u128::from(rng.next_u64()) << 64) | u128::from(rng.next_u64());
            return bits & ((1u128 << width) - 1);
        }
    };
    sign | magnitude
}

/// A float literal of `float<e,m>` from [`special_bits`].
fn literal(rng: &mut Rng, e: u32, m: u32) -> String {
    spell_float(e, m, special_bits(rng, e, m))
}

/// The ops of a float function so far, and its values in scope.
struct Chain {
    loc: LocRef,
    ops: Vec<Op>,
    values: Vec<(String, Type)>,
    next: usize,
}

impl Chain {
    fn fresh(&mut self) -> String {
        self.next += 1;
        format!("v{}", self.next)
    }

    fn push(&mut self, op: Op, t: &Type) -> String {
        let n = self.fresh();
        self.ops.push(op.result(n.clone(), t.clone()));
        self.values.push((n.clone(), t.clone()));
        n
    }

    /// A value of type `t`: one in scope, or a new constant.
    fn operand(&mut self, rng: &mut Rng, t: &Type) -> String {
        let same: Vec<String> = self
            .values
            .iter()
            .filter(|(_, u)| u == t)
            .map(|(v, _)| v.clone())
            .collect();
        if !same.is_empty() && !rng.one_in(3) {
            return rng.pick(&same).clone();
        }
        let (e, m) = float_format(t).expect("a float type");
        let c = Op::new("const", self.loc).attr(Attr::Float(literal(rng, e, m)));
        self.push(c, t)
    }

    /// `fcmp` of `last` and another value of its type.
    fn compare(&mut self, rng: &mut Rng, last: &str, t: &Type) -> String {
        let other = self.operand(rng, t);
        let op = Op::new("fcmp", self.loc)
            .attr(Attr::word(*rng.pick(&FLOAT_PREDICATES)))
            .operand(last)
            .operand(other);
        self.push(op, &int_type(1))
    }

    /// One op that takes `last` of type `t` first, and its result's type.
    fn step(&mut self, rng: &mut Rng, last: &str, t: &Type) -> (String, Type) {
        let fmt = float_format(t).expect("a float type");
        if rng.one_in(6) {
            let (e, m) = FORMATS[usize::from(fmt == FORMATS[0])];
            let u = float_type(e, m);
            let op = if fmt == FORMATS[0] {
                Op::new("fpext", self.loc)
            } else {
                Op::new("fptrunc", self.loc).attr(round())
            };
            return (self.push(op.operand(last), &u), u);
        }
        let (name, n, rounds) = *rng.pick(&ARITH);
        let mut op = Op::new(name, self.loc);
        if rounds {
            op = op.attr(round());
        }
        op = op.operand(last);
        for _ in 1..n {
            op = op.operand(self.operand(rng, t));
        }
        (self.push(op, t), t.clone())
    }
}

/// The float function `name` and its runs: one to three parameters of one
/// format, a chain of one to [`MAX_NAN_OPS`] ops, and as results the
/// chain's last value, and maybe an earlier float and an `fcmp` result.
pub(super) fn function(rng: &mut Rng, name: String, loc: LocRef) -> (Func, Vec<Run>) {
    let (e, m) = *rng.pick(&FORMATS);
    let t = float_type(e, m);
    let mut f = Func::new(name);
    let mut chain = Chain {
        loc,
        ops: Vec::new(),
        values: Vec::new(),
        next: 0,
    };
    for k in 0..1 + rng.below(3) {
        let p = format!("p{k}");
        chain.values.push((p.clone(), t.clone()));
        f = f.param(p, t.clone());
    }
    let mut last = rng.pick(&chain.values).0.clone();
    let mut ty = t.clone();
    let mut floats = Vec::new();
    for _ in 0..1 + rng.below(MAX_NAN_OPS as u64) {
        (last, ty) = chain.step(rng, &last, &ty);
        floats.push((last.clone(), ty.clone()));
    }
    let mut results = vec![(last.clone(), ty.clone())];
    if floats.len() > 1 && rng.one_in(3) {
        results.push(rng.pick(&floats[..floats.len() - 1]).clone());
    }
    if rng.one_in(3) {
        let c = chain.compare(rng, &last, &ty);
        results.push((c, int_type(1)));
    }
    let mut ret = Op::new("ret", loc);
    for (v, u) in &results {
        ret = ret.operand(v.as_str());
        f = f.result(u.clone());
    }
    let mut entry = Block::new("entry");
    for op in chain.ops {
        entry = entry.op(op);
    }
    let f = f.block(entry.op(ret));
    let runs = runs(rng, &f, e, m);
    (f, runs)
}

/// One to four distinct argument vectors for the float function `f`, whose
/// parameters are of `float<e,m>`.
fn runs(rng: &mut Rng, f: &Func, e: u32, m: u32) -> Vec<Run> {
    let mut seen: Vec<Vec<String>> = Vec::new();
    for _ in 0..1 + rng.below(4) {
        let args: Vec<String> = f.params.iter().map(|_| literal(rng, e, m)).collect();
        if !seen.contains(&args) {
            seen.push(args);
        }
    }
    seen.into_iter()
        .map(|args| Run {
            func: print_symbol(&f.name),
            args,
            fuel: FUEL,
            expect: None,
            defined: false,
        })
        .collect()
}
