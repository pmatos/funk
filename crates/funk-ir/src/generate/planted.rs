//! Functions of a generated program planted to end one way (#165).
//!
//! The generator says how these runs must end, so it is a second opinion on
//! `fir-ref`'s report. Each kind of UB comes with a near miss, one operand
//! away from it, whose result is known:
//!
//! | UB | near miss |
//! | --- | --- |
//! | `cond_br` on poison | `cond_br` on a constant |
//! | `unreachable` reached | the branch past it taken |
//! | a division by zero | a division by 1 |
//! | a division by poison | poison divided by 1, which is poison |
//! | the signed minimum by -1 | the signed minimum plus 1 by -1 |
//! | poison by -1 | 5 by -1 |
//!
//! Other functions never end, by a loop or a recursion, and must run out of
//! fuel. Native code runs none of these.

use super::program::{Expect, Run};
use super::{BACKEND_WIDTHS, Rng};
use crate::dialects::core::{DIVISION_OPS, int_type};
use crate::ir::{Attr, Block, Func, LocRef, Op, Type};
use crate::text::print_symbol;

/// The fuel of a planted run.
const FUEL: u64 = 1_000;

const SIGNED_DIVISIONS: [&str; 2] = ["sdiv", "srem"];

fn planted(f: &Func, args: Vec<String>, expect: Expect) -> Run {
    Run {
        func: print_symbol(&f.name),
        args,
        fuel: FUEL,
        expect: Some(expect),
        defined: false,
    }
}

/// The ops and the type of one planted function.
struct Builder {
    loc: LocRef,
    w: u32,
    t: Type,
}

impl Builder {
    fn constant(&self, name: &str, v: i128) -> Op {
        Op::new("const", self.loc)
            .attr(Attr::int(v))
            .result(name, self.t.clone())
    }

    /// `%c: i1 = const true` or `false`, as `taken` says.
    fn condition(&self, taken: bool) -> Op {
        Op::new("const", self.loc)
            .attr(Attr::word(if taken { "true" } else { "false" }))
            .result("c", int_type(1))
    }

    fn poison(&self, name: &str) -> Op {
        Op::new("poison", self.loc).result(name, self.t.clone())
    }

    /// The signed minimum of the type.
    fn min(&self) -> i128 {
        i128::MIN >> (128 - self.w)
    }

    /// `name`, which runs `ops` and returns `a op b`.
    fn division(&self, name: String, ops: Vec<Op>, op: &str, a: &str, b: &str) -> Func {
        let mut f = Func::new(name).result(self.t.clone());
        if a == "x" {
            f = f.param("x", self.t.clone());
        }
        let mut entry = Block::new("entry");
        for o in ops {
            entry = entry.op(o);
        }
        let q = Op::new(op, self.loc)
            .operand(a)
            .operand(b)
            .result("q", self.t.clone());
        f.block(entry.op(q).op(Op::new("ret", self.loc).operand("q")))
    }

    /// A branch on `cond`, whose two arms return 1 and 0.
    fn branch(&self, name: String, cond: Op) -> Func {
        let test = Op::new("cond_br", self.loc)
            .operand("c")
            .succ("a", &[])
            .succ("b", &[]);
        let arm = |label: &str, value: i128| {
            let r = format!("r{label}");
            Block::new(label)
                .op(self.constant(&r, value))
                .op(Op::new("ret", self.loc).operand(r))
        };
        Func::new(name)
            .result(self.t.clone())
            .block(Block::new("entry").op(cond).op(test))
            .block(arm("a", 1))
            .block(arm("b", 0))
    }

    /// A branch on the constant `taken`, whose first arm is `unreachable`
    /// and whose second returns 0.
    fn trap(&self, name: String, taken: bool) -> Func {
        let test = Op::new("cond_br", self.loc)
            .operand("c")
            .succ("dead", &[])
            .succ("ok", &[]);
        Func::new(name)
            .result(self.t.clone())
            .block(Block::new("entry").op(self.condition(taken)).op(test))
            .block(Block::new("dead").op(Op::new("unreachable", self.loc)))
            .block(
                Block::new("ok")
                    .op(self.constant("r", 0))
                    .op(Op::new("ret", self.loc).operand("r")),
            )
    }
}

/// A function whose every run hits UB, and its near miss, with their runs.
pub(super) fn ub_and_near_miss(rng: &mut Rng, k: u64, loc: LocRef) -> Vec<(Func, Run)> {
    let w = *rng.pick(&BACKEND_WIDTHS[1..]);
    let b = Builder {
        loc,
        w,
        t: int_type(w),
    };
    let ub = format!("planted.ub{k}");
    let near = format!("planted.near{k}");
    let x = (rng.next_u64() % 100).to_string();
    let zero_rem = |op: &str, kept: String| {
        vec![if op.ends_with("rem") {
            "0".into()
        } else {
            kept
        }]
    };
    let (bad, good, values) = match rng.below(6) {
        0 => {
            let taken = rng.one_in(2);
            let c = b.condition(taken);
            let p = Op::new("poison", loc).result("c", int_type(1));
            let value = if taken { "1" } else { "0" };
            (b.branch(ub, p), b.branch(near, c), vec![value.to_string()])
        }
        1 => {
            let op = rng.pick(&DIVISION_OPS).0;
            let bad = b.division(ub, vec![b.constant("d", 0)], op, "x", "d");
            let good = b.division(near, vec![b.constant("d", 1)], op, "x", "d");
            (bad, good, zero_rem(op, x.clone()))
        }
        2 => {
            let op = rng.pick(&DIVISION_OPS).0;
            let bad = b.division(ub, vec![b.poison("d")], op, "x", "d");
            let ops = vec![b.poison("p"), b.constant("d", 1)];
            let good = b.division(near, ops, op, "p", "d");
            (bad, good, vec!["poison".to_string()])
        }
        3 => {
            let op = *rng.pick(&SIGNED_DIVISIONS);
            let min = b.min();
            let ops = |a: i128| vec![b.constant("a", a), b.constant("d", -1)];
            let bad = b.division(ub, ops(min), op, "a", "d");
            let good = b.division(near, ops(min + 1), op, "a", "d");
            (bad, good, zero_rem(op, (!min).to_string()))
        }
        5 => (b.trap(ub, true), b.trap(near, false), vec!["0".to_string()]),
        _ => {
            let op = *rng.pick(&SIGNED_DIVISIONS);
            let ops = vec![b.poison("a"), b.constant("d", -1)];
            let bad = b.division(ub, ops, op, "a", "d");
            let ops = vec![b.constant("a", 5), b.constant("d", -1)];
            let good = b.division(near, ops, op, "a", "d");
            (bad, good, zero_rem(op, "-5".to_string()))
        }
    };
    let args = |f: &Func| f.params.iter().map(|_| x.clone()).collect();
    let bad_run = planted(&bad, args(&bad), Expect::Ub);
    let good_run = planted(&good, args(&good), Expect::Values(values));
    vec![(bad, bad_run), (good, good_run)]
}

/// One function, or two that call each other, whose every run runs out of
/// fuel: a loop that passes a block argument round, or a recursion.
pub(super) fn spin(rng: &mut Rng, loc: LocRef) -> Vec<(Func, Run)> {
    let t = int_type(*rng.pick(&BACKEND_WIDTHS));
    let funcs = match rng.below(3) {
        0 => vec![spin_loop(t, loc)],
        1 => vec![recursive("planted.self", "planted.self", t, loc)],
        _ => vec![
            recursive("planted.ping", "planted.pong", t.clone(), loc),
            recursive("planted.pong", "planted.ping", t, loc),
        ],
    };
    funcs
        .into_iter()
        .map(|f| {
            let args = super::program::arguments(rng, &f);
            let run = planted(&f, args, Expect::FuelExhausted);
            (f, run)
        })
        .collect()
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
