//! The blocks of a generated function and the branches between them
//! (`br` and `cond_br`, #19).
//!
//! A function has one block, or a chain of several: each block but the
//! last ends in a branch to the next, so the entry reaches every block, as
//! validation requires (ADR-2026-10-30-0817). A `cond_br` also goes to any
//! block but the entry: back to an earlier one or to itself, which makes a
//! loop, or forward, past the next, which makes a join. The last block
//! returns. Every block but the entry may take arguments, and each branch
//! passes values of their types: values in scope, often the block's own
//! arguments in another order, or new ones.
//!
//! A value is in scope in a block when its definition dominates it
//! (`Func.InScope`): the function's parameters, the definitions of every
//! block that dominates it, and those of the block itself before the use.
//! Dominance is decided as the spec defines it, by whether the entry
//! reaches a block once the other is removed (`Func.Dominates`). A block
//! dominates only blocks after it in the chain, so the blocks are filled in
//! order.

use super::{Body, Rng, name, width};
use crate::dialects::core::int_type;
use crate::ir::{Block, Func, Op, Type};

/// The blocks of `f`, whose parameters `body` holds, with their branches
/// and the `ret` that ends the last one, which also sets `f`'s results.
pub(super) fn build(rng: &mut Rng, body: &mut Body<'_>, mut f: Func) -> Func {
    let n = if rng.one_in(3) {
        1
    } else {
        2 + rng.below(4) as usize
    };
    let mut labels: Vec<String> = Vec::new();
    while labels.len() < n {
        let l = name(rng, false);
        if !labels.contains(&l) {
            labels.push(l);
        }
    }
    let params: Vec<Vec<(String, Type)>> = (0..n)
        .map(|k| {
            let count = if k == 0 { 0 } else { rng.below(4) };
            let mut ps: Vec<(String, Type)> = Vec::new();
            for _ in 0..count {
                let t = match ps.last() {
                    Some((_, t)) if rng.one_in(2) => t.clone(),
                    _ => arg_type(rng, body),
                };
                ps.push((body.fresh_name(rng), t));
            }
            ps
        })
        .collect();
    let exits: Vec<Vec<usize>> = (0..n - 1).map(|k| exit(rng, k, n)).collect();
    let fparams = body.values.clone();
    let mut defs: Vec<Vec<(String, Type)>> = Vec::with_capacity(n);
    for k in 0..n {
        body.values = fparams.clone();
        for (d, ds) in defs.iter().enumerate() {
            if dominates(&exits, d, k) {
                body.values.extend(ds.iter().cloned());
            }
        }
        body.values.extend(params[k].iter().cloned());
        body.ops = Vec::new();
        for _ in 0..rng.below(4) {
            let t = if !body.values.is_empty() && rng.one_in(2) {
                rng.pick(&body.values).1.clone()
            } else {
                int_type(width(rng))
            };
            body.define(rng, t);
        }
        let term = match exits.get(k) {
            Some(targets) => branch(rng, body, targets, &labels, &params),
            None => {
                let (g, ret) = ret(rng, body, f);
                f = g;
                ret
            }
        };
        let mut block = Block::new(labels[k].clone());
        for (x, t) in &params[k] {
            block = block.param(x.clone(), t.clone());
        }
        block.ops = std::mem::take(&mut body.ops);
        let mut ds = params[k].clone();
        for op in &block.ops {
            ds.extend(op.results.iter().map(|d| (d.name.clone(), d.ty.clone())));
        }
        defs.push(ds);
        f = f.block(block.op(term));
    }
    f
}

/// The type of a block argument: often one that a parameter of the
/// function has.
fn arg_type(rng: &mut Rng, body: &Body<'_>) -> Type {
    if !body.values.is_empty() && rng.one_in(2) {
        rng.pick(&body.values).1.clone()
    } else {
        int_type(width(rng))
    }
}

/// Where block `k` of `n` goes: to the next block, and for a `cond_br` to
/// any block but the entry too, in either order.
fn exit(rng: &mut Rng, k: usize, n: usize) -> Vec<usize> {
    if rng.one_in(3) {
        return vec![k + 1];
    }
    let other = 1 + rng.below(n as u64 - 1) as usize;
    if rng.one_in(2) {
        vec![k + 1, other]
    } else {
        vec![other, k + 1]
    }
}

/// Whether block `a` dominates block `b`: they are one block, or the entry
/// does not reach `b` once `a` is removed. `exits[k]` are the successors
/// of block `k`; the last block has none.
fn dominates(exits: &[Vec<usize>], a: usize, b: usize) -> bool {
    if a == b {
        return true;
    }
    let mut seen = vec![false; exits.len() + 1];
    let mut stack = Vec::new();
    if a != 0 {
        seen[0] = true;
        stack.push(0);
    }
    while let Some(x) = stack.pop() {
        for &y in exits.get(x).into_iter().flatten() {
            if y != a && !seen[y] {
                seen[y] = true;
                stack.push(y);
            }
        }
    }
    !seen[b]
}

/// A value of type `t` in scope: often one that is, otherwise a new one.
fn value(rng: &mut Rng, body: &mut Body<'_>, t: &Type) -> String {
    let have = body.of_type(t);
    if !have.is_empty() && !rng.one_in(4) {
        rng.pick(&have).clone()
    } else {
        body.define(rng, t.clone())
    }
}

/// `own`, the arguments of a block that a branch goes back to, passed to
/// it again: rotated among the arguments of each type, which permutes
/// them, or each one of its type, which may pass one to several.
fn shuffled(rng: &mut Rng, own: &[(String, Type)]) -> Vec<String> {
    let shift = rng.below(own.len() as u64) as usize;
    let rotate = rng.one_in(2);
    let mut args = Vec::with_capacity(own.len());
    for (i, (_, t)) in own.iter().enumerate() {
        let same: Vec<usize> = (0..own.len()).filter(|&j| own[j].1 == *t).collect();
        let j = if rotate {
            let at = same
                .iter()
                .position(|&j| j == i)
                .expect("i has its own type");
            same[(at + shift) % same.len()]
        } else {
            *rng.pick(&same)
        };
        args.push(own[j].0.clone());
    }
    args
}

/// The branch to `targets`: `br` to one, or `cond_br` on an `i1` to two,
/// each passing a value of the right type for each of its arguments.
fn branch(
    rng: &mut Rng,
    body: &mut Body<'_>,
    targets: &[usize],
    labels: &[String],
    params: &[Vec<(String, Type)>],
) -> Op {
    let loc = *rng.pick(body.keys);
    let mut op = match targets {
        [_] => Op::new("br", loc),
        _ => Op::new("cond_br", loc).operand(value(rng, body, &int_type(1))),
    };
    for &t in targets {
        let own = &params[t];
        let in_scope = own.iter().all(|p| body.values.contains(p));
        let args: Vec<String> = if !own.is_empty() && in_scope && rng.one_in(2) {
            shuffled(rng, own)
        } else {
            own.iter().map(|(_, ty)| value(rng, body, ty)).collect()
        };
        let args: Vec<&str> = args.iter().map(String::as_str).collect();
        op = op.succ(labels[t].clone(), &args);
    }
    op
}

/// The `ret` of the last block, of zero to three values, and `f` with
/// their types as its results.
fn ret(rng: &mut Rng, body: &mut Body<'_>, mut f: Func) -> (Func, Op) {
    let mut ret = Op::new("ret", *rng.pick(body.keys));
    for _ in 0..rng.below(4) {
        let t = int_type(width(rng));
        let have = body.of_type(&t);
        let v = if !have.is_empty() && rng.one_in(2) {
            rng.pick(&have).clone()
        } else {
            body.define(rng, t.clone())
        };
        ret = ret.operand(v);
        f = f.result(t);
    }
    (f, ret)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dominance_is_the_spec_s_on_a_chain_with_a_loop_and_a_join() {
        // 0 -> 1; 1 -> 2 or back to 1; 2 -> 3 or on to 4; 3 -> 4.
        let exits = vec![vec![1], vec![2, 1], vec![3, 4], vec![4]];
        let doms = |b: usize| {
            (0..5)
                .filter(|&a| dominates(&exits, a, b))
                .collect::<Vec<_>>()
        };
        assert_eq!(doms(0), [0]);
        assert_eq!(doms(1), [0, 1]);
        assert_eq!(doms(2), [0, 1, 2]);
        assert_eq!(doms(3), [0, 1, 2, 3]);
        assert_eq!(doms(4), [0, 1, 2, 4]);
    }
}
