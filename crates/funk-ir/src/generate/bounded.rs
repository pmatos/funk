//! Functions of a generated program that iterate and then end (#165).
//!
//! Random control flow mostly returns at once or never ends, so native code
//! would rarely run a loop to its end. These functions do. Each takes a
//! counter as its first parameter, of 8 bits or more, and masks it to a
//! small bound, so its arguments still choose how long it runs:
//!
//! - a loop counts up to the bound, passing accumulators round as block
//!   arguments, and may branch to a join inside its body;
//! - a recursion, of one function or of two that call each other, goes
//!   down from the bound to 0, so it is at most 15 deep.
//!
//! Most of their ops keep values defined and feed what they return
//! ([`Body::defined`]), so that a wrong result in native code shows as a
//! wrong value: random operands mostly make poison, which any value refines.
//! The rest are the generator's own ops, and they may call earlier bounded
//! functions. An op may still make poison, and a division or a branch on it
//! may hit UB: that makes a run interpreter-only, not invalid.
//!
//! A function named with [`SAFE_PREFIX`] holds only ops that stay defined,
//! calls only functions like itself, and makes at most one call on each
//! path through an iteration, which bounds its steps. Its runs must return
//! defined values.

use super::blocks::value;
use super::calls::{self, Callee};
use super::{BACKEND_WIDTHS, Body, Rng, Widths, constant};
use crate::dialects::core::{PREDICATES, int_type, int_width};
use crate::ir::{Attr, Block, Func, FuncType, Int, LocRef, Module, Op, Type};

/// The start of the name of a function built to stay defined.
pub const SAFE_PREFIX: &str = "safe.";

const COUNTER_WIDTHS: [u32; 5] = [8, 16, 32, 64, 128];
const MASKS: [&str; 3] = ["3", "7", "15"];
const LOOP_PREDICATES: [&str; 3] = ["slt", "ult", "ne"];

/// Adds one to three bounded functions, or pairs of them, to `module`. The
/// first is built to stay defined, and so is each later one half the time.
pub(super) fn add(rng: &mut Rng, mut module: Module, keys: &[LocRef]) -> Module {
    let (mut all, mut safe_ones): (Vec<Callee>, Vec<Callee>) = (Vec::new(), Vec::new());
    for k in 0..1 + rng.below(3) {
        let safe = k == 0 || rng.one_in(2);
        let prefix = if safe { SAFE_PREFIX } else { "bounded." };
        let done = if safe { &safe_ones } else { &all };
        let mut made = Vec::new();
        match rng.below(4) {
            0 | 1 => {
                let me = signature(rng, format!("{prefix}loop{k}"));
                module = module.func(counted_loop(rng, &me, done, keys, safe));
                made.push(me);
            }
            2 => {
                let me = signature(rng, format!("{prefix}self{k}"));
                module = module.func(recursion(rng, &me, &me.name, done, keys, safe));
                made.push(me);
            }
            _ => {
                let a = signature(rng, format!("{prefix}even{k}"));
                let b = Callee {
                    name: format!("{prefix}odd{k}"),
                    ty: a.ty.clone(),
                };
                module = module.func(recursion(rng, &a, &b.name, done, keys, safe));
                module = module.func(recursion(rng, &b, &a.name, done, keys, safe));
                made.extend([a, b]);
            }
        }
        if safe {
            safe_ones.extend(made.iter().cloned());
        }
        all.extend(made);
    }
    module
}

/// A signature whose first parameter is the counter.
fn signature(rng: &mut Rng, name: String) -> Callee {
    let mut me = calls::signature(rng, name, Widths::Backend);
    me.ty.params.insert(0, int_type(*rng.pick(&COUNTER_WIDTHS)));
    me
}

fn start<'k>(
    rng: &mut Rng,
    me: &Callee,
    done: &'k [Callee],
    keys: &'k [LocRef],
    safe: bool,
) -> (Func, Body<'k>) {
    let mut body = Body {
        widths: Widths::Backend,
        safe,
        calls_left: 0,
        keys,
        funcs: done,
        values: Vec::new(),
        ops: Vec::new(),
        taken: Vec::new(),
    };
    let mut f = Func::new(me.name.clone());
    for t in &me.ty.params {
        let n = body.fresh_name(rng);
        body.values.push((n.clone(), t.clone()));
        f = f.param(n, t.clone());
    }
    for t in &me.ty.results {
        f = f.result(t.clone());
    }
    (f, body)
}

impl Body<'_> {
    fn loc(&self, rng: &mut Rng) -> LocRef {
        *rng.pick(self.keys)
    }

    /// Adds `op`, with one new result of type `t`, and returns the result.
    fn result_of(&mut self, rng: &mut Rng, op: Op, t: &Type) -> String {
        let n = self.fresh_name(rng);
        self.ops.push(op.result(n.clone(), t.clone()));
        self.values.push((n.clone(), t.clone()));
        n
    }

    /// A constant of a small value, spelled for `t`: 0 or 1 at `i1`.
    fn int(&mut self, rng: &mut Rng, digits: &str, t: &Type) -> String {
        let v = match (int_width(t) == Some(1), digits) {
            (true, "0") => Attr::word("false"),
            (true, _) => Attr::word("true"),
            _ => Attr::Int(Int::parse(digits).expect("a canonical integer")),
        };
        let op = Op::new("const", self.loc(rng)).attr(v);
        self.result_of(rng, op, t)
    }

    fn binary(&mut self, rng: &mut Rng, name: &str, a: &str, b: &str, t: &Type) -> String {
        let op = Op::new(name, self.loc(rng)).operand(a).operand(b);
        self.result_of(rng, op, t)
    }

    fn compare(&mut self, rng: &mut Rng, predicate: &str, a: &str, b: &str) -> String {
        let op = Op::new("icmp", self.loc(rng))
            .attr(Attr::word(predicate))
            .operand(a)
            .operand(b);
        self.result_of(rng, op, &int_type(1))
    }

    /// The counter parameter, masked to a small bound.
    fn bound(&mut self, rng: &mut Rng, counter: &str, t: &Type) -> String {
        let digits = *rng.pick(&MASKS);
        let mask = self.int(rng, digits, t);
        self.binary(rng, "and", counter, &mask, t)
    }

    /// One to three ops: new values, or calls of earlier bounded functions.
    fn work(&mut self, rng: &mut Rng) {
        for _ in 0..1 + rng.below(3) {
            if !self.funcs.is_empty() && self.calls_left > 0 && rng.one_in(3) {
                self.calls_left -= 1;
                calls::call(rng, self);
            } else {
                let t = int_type(*rng.pick(&BACKEND_WIDTHS));
                let t = if rng.one_in(2) {
                    rng.pick(&self.values).1.clone()
                } else {
                    t
                };
                if rng.one_in(4) {
                    self.define(rng, t);
                } else {
                    self.defined(rng, &t);
                }
            }
        }
    }

    /// A recent value of type `t`, or sometimes a new constant.
    fn operand(&mut self, rng: &mut Rng, t: &Type) -> String {
        let have = self.of_type(t);
        if have.is_empty() || rng.one_in(6) {
            let w = int_width(t).expect("an integer type");
            let op = Op::new("const", self.loc(rng)).attr(constant(rng, w));
            return self.result_of(rng, op, t);
        }
        have[have.len().saturating_sub(4)..][rng.below(have.len().min(4) as u64) as usize].clone()
    }

    /// A new value of type `t` from recent values, by an op that gives no
    /// poison on defined operands: no flags, a shift amount below the
    /// width, and a divisor from 1 to 7.
    pub(super) fn defined(&mut self, rng: &mut Rng, t: &Type) -> String {
        let w = int_width(t).expect("an integer type");
        let a = self.operand(rng, t);
        let b = self.operand(rng, t);
        match rng.below(if w == 1 { 8 } else { 14 }) {
            k @ 0..=5 => {
                let name = ["add", "sub", "mul", "and", "or", "xor"][k as usize];
                self.binary(rng, name, &a, &b, t)
            }
            6 | 7 => {
                let predicate = *rng.pick(&PREDICATES);
                let c = self.compare(rng, predicate, &a, &b);
                let op = Op::new("select", self.loc(rng))
                    .operand(c)
                    .operand(a)
                    .operand(b);
                self.result_of(rng, op, t)
            }
            8 | 9 => {
                let top = self.int(rng, &(w - 1).to_string(), t);
                let amount = self.binary(rng, "and", &b, &top, t);
                let name = *rng.pick(&["shl", "lshr", "ashr"]);
                self.binary(rng, name, &a, &amount, t)
            }
            10 => {
                let seven = self.int(rng, "7", t);
                let low = self.binary(rng, "and", &b, &seven, t);
                let one = self.int(rng, "1", t);
                let divisor = self.binary(rng, "or", &low, &one, t);
                let name = *rng.pick(&["sdiv", "udiv", "srem", "urem"]);
                self.binary(rng, name, &a, &divisor, t)
            }
            13 => {
                let op = Op::new("freeze", self.loc(rng)).operand(a);
                self.result_of(rng, op, t)
            }
            _ => {
                let casts = self.casts_to(t);
                if casts.is_empty() {
                    return self.binary(rng, "xor", &a, &b, t);
                }
                let (name, x) = rng.pick(&casts).clone();
                let op = Op::new(name, self.loc(rng)).operand(x);
                self.result_of(rng, op, t)
            }
        }
    }

    /// Allows the calls of one path through an iteration.
    fn allow_calls(&mut self) {
        self.calls_left = if self.safe { 1 } else { 6 };
    }

    fn take_block(&mut self, label: &str, params: &[(String, Type)], term: Op) -> Block {
        let mut b = Block::new(label);
        for (x, t) in params {
            b = b.param(x.clone(), t.clone());
        }
        b.ops = std::mem::take(&mut self.ops);
        b.op(term)
    }

    fn ret(&mut self, rng: &mut Rng, me: &Callee) -> Op {
        let mut op = Op::new("ret", self.loc(rng));
        for t in &me.ty.results {
            let v = match self.of_type(t).last() {
                Some(v) => v.clone(),
                None => self.defined(rng, t),
            };
            op = op.operand(v);
        }
        op
    }
}

/// A loop that counts from 0 up to the bound, with accumulators as block
/// arguments of its header.
fn counted_loop(rng: &mut Rng, me: &Callee, done: &[Callee], keys: &[LocRef], safe: bool) -> Func {
    let (f, mut body) = start(rng, me, done, keys, safe);
    let (counter, t) = body.values[0].clone();
    let n = body.bound(rng, &counter, &t);
    let zero = body.int(rng, "0", &t);
    let mut types = me.ty.results.clone();
    if types.is_empty() || rng.one_in(2) {
        types.push(int_type(*rng.pick(&BACKEND_WIDTHS)));
    }
    let inits: Vec<String> = types.iter().map(|u| value(rng, &mut body, u)).collect();
    let mut args = vec![zero.as_str()];
    args.extend(inits.iter().map(String::as_str));
    let enter = Op::new("br", body.loc(rng)).succ("head", &args);
    let entry = body.take_block("entry", &[], enter);

    let i = body.fresh_name(rng);
    let mut params = vec![(i.clone(), t.clone())];
    for u in &types {
        params.push((body.fresh_name(rng), u.clone()));
    }
    body.values.extend(params.iter().cloned());
    let predicate = *rng.pick(&LOOP_PREDICATES);
    let go = body.compare(rng, predicate, &i, &n);
    let test = Op::new("cond_br", body.loc(rng))
        .operand(go)
        .succ("body", &[])
        .succ("exit", &[]);
    let head = body.take_block("head", &params, test);
    let after_head = body.values.clone();

    body.allow_calls();
    body.work(rng);
    let mut blocks = Vec::new();
    let latch_params = if rng.one_in(2) {
        diamond(rng, &mut body, &i, &t, &types, &mut blocks)
    } else {
        Vec::new()
    };
    body.work(rng);
    let nexts: Vec<String> = types.iter().map(|u| body.defined(rng, u)).collect();
    let one = body.int(rng, "1", &t);
    let next = body.binary(rng, "add", &i, &one, &t);
    let mut args = vec![next.as_str()];
    args.extend(nexts.iter().map(String::as_str));
    let back = Op::new("br", body.loc(rng)).succ("head", &args);
    let label = if blocks.is_empty() { "body" } else { "latch" };
    let last = body.take_block(label, &latch_params, back);

    body.values = after_head;
    let ret = body.ret(rng, me);
    let exit = body.take_block("exit", &[], ret);

    let mut f = f.block(entry).block(head);
    for b in blocks {
        f = f.block(b);
    }
    f.block(last).block(exit)
}

/// Ends the loop's body with a branch on the counter's low bit to two
/// blocks, which pass a value each to a join. `blocks` gets the body and
/// the two arms; the join's parameter is returned and is in scope.
fn diamond(
    rng: &mut Rng,
    body: &mut Body<'_>,
    i: &str,
    t: &Type,
    types: &[Type],
    blocks: &mut Vec<Block>,
) -> Vec<(String, Type)> {
    let one = body.int(rng, "1", t);
    let low = body.binary(rng, "and", i, &one, t);
    let zero = body.int(rng, "0", t);
    let even = body.compare(rng, "eq", &low, &zero);
    let branch = Op::new("cond_br", body.loc(rng))
        .operand(even)
        .succ("then", &[])
        .succ("else", &[]);
    blocks.push(body.take_block("body", &[], branch));
    let joined = rng.pick(types).clone();
    let scope = body.values.clone();
    for label in ["then", "else"] {
        body.values = scope.clone();
        let v = body.defined(rng, &joined);
        let to = Op::new("br", body.loc(rng)).succ("latch", &[v.as_str()]);
        blocks.push(body.take_block(label, &[], to));
    }
    body.values = scope;
    let v = body.fresh_name(rng);
    body.values.push((v.clone(), joined.clone()));
    vec![(v, joined)]
}

/// A recursion that goes down from the bound to 0, calling `callee`, which
/// has `me`'s type: `me` itself, or the function it alternates with.
fn recursion(
    rng: &mut Rng,
    me: &Callee,
    callee: &str,
    done: &[Callee],
    keys: &[LocRef],
    safe: bool,
) -> Func {
    let (f, mut body) = start(rng, me, done, keys, safe);
    let (counter, t) = body.values[0].clone();
    let d = body.bound(rng, &counter, &t);
    let zero = body.int(rng, "0", &t);
    let go = body.compare(rng, "sgt", &d, &zero);
    let test = Op::new("cond_br", body.loc(rng))
        .operand(go)
        .succ("rec", &[])
        .succ("base", &[]);
    let entry = body.take_block("entry", &[], test);
    let after_entry = body.values.clone();

    body.allow_calls();
    body.work(rng);
    let ret = body.ret(rng, me);
    let base = body.take_block("base", &[], ret);

    body.values = after_entry;
    let one = body.int(rng, "1", &t);
    let next = body.binary(rng, "sub", &d, &one, &t);
    let ty: FuncType = me.ty.clone();
    let mut call = Op::new("call", body.loc(rng))
        .attr(Attr::Sym(callee.to_string()))
        .operand(next);
    for u in &ty.params[1..] {
        call = call.operand(value(rng, &mut body, u));
    }
    for u in &ty.results {
        let n = body.fresh_name(rng);
        call = call.result(n.clone(), u.clone());
        body.values.push((n, u.clone()));
    }
    body.ops.push(call);
    body.allow_calls();
    body.work(rng);
    let ret = body.ret(rng, me);
    let rec = body.take_block("rec", &[], ret);

    f.block(entry).block(base).block(rec)
}
