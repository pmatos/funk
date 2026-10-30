//! The control-flow graph of a function, reachability and dominance
//! (`lean/Fir/Validation/Dominance.lean`).
//!
//! The nodes are the labels of the function's top-level blocks, and an edge
//! goes from a block to each successor of its ops. Block `a` dominates block
//! `b` when every path from the entry to `b` passes through `a`. Dominators
//! are computed with the algorithm of Cooper, Harvey and Kennedy, and the
//! dominator tree is numbered in depth-first order, so that `a` dominates `b`
//! when `b`'s interval lies inside `a`'s. A block that the entry does not
//! reach is dominated by every block, as the spec's definition
//! (`¬ ReachesAvoiding a b`) gives.

use std::collections::HashMap;

use crate::ir::Func;

/// The graph of a function, over its labels.
pub(super) struct Cfg<'f> {
    index: HashMap<&'f str, usize>,
    /// The position of each reachable node in a postorder, if reachable.
    post: Vec<Option<usize>>,
    /// When the walk of the dominator tree enters and leaves each reachable
    /// node.
    enter: Vec<usize>,
    leave: Vec<usize>,
}

impl<'f> Cfg<'f> {
    pub(super) fn new(f: &'f Func) -> Cfg<'f> {
        let mut index = HashMap::new();
        for b in &f.body.blocks {
            let next = index.len();
            index.entry(b.label.as_str()).or_insert(next);
        }
        let n = index.len();
        let mut succs = vec![Vec::new(); n];
        for b in &f.body.blocks {
            let from = index[b.label.as_str()];
            for s in b.ops.iter().flat_map(|o| &o.succs) {
                if let Some(&to) = index.get(s.label.as_str()) {
                    succs[from].push(to);
                }
            }
        }
        let (post, order) = postorder(&succs, n);
        let idom = dominators(&succs, &post, &order, n);
        let (enter, leave) = number_tree(&idom, &post);
        Cfg {
            index,
            post,
            enter,
            leave,
        }
    }

    /// Whether the entry reaches the block labelled `l`.
    pub(super) fn reachable(&self, l: &str) -> bool {
        self.index.get(l).is_some_and(|&i| self.post[i].is_some())
    }

    /// Whether the block labelled `a` dominates the block labelled `b`.
    pub(super) fn dominates(&self, a: &str, b: &str) -> bool {
        if a == b {
            return true;
        }
        let (Some(&a), Some(&b)) = (self.index.get(a), self.index.get(b)) else {
            return !self.reachable(b);
        };
        if self.post[b].is_none() {
            return true;
        }
        if self.post[a].is_none() {
            return false;
        }
        self.enter[a] <= self.enter[b] && self.leave[b] <= self.leave[a]
    }
}

/// Numbers the dominator tree of the reachable nodes in depth-first order:
/// when the walk enters each node, and when it leaves it.
fn number_tree(idom: &[usize], post: &[Option<usize>]) -> (Vec<usize>, Vec<usize>) {
    let n = idom.len();
    let mut children = vec![Vec::new(); n];
    for (x, &d) in idom.iter().enumerate() {
        if x != d && post[x].is_some() {
            children[d].push(x);
        }
    }
    let (mut enter, mut leave) = (vec![0; n], vec![0; n]);
    if n == 0 {
        return (enter, leave);
    }
    let mut clock = 0;
    let mut stack = vec![(0, 0)];
    enter[0] = clock;
    while let Some((node, next)) = stack.pop() {
        clock += 1;
        if let Some(&child) = children[node].get(next) {
            stack.push((node, next + 1));
            enter[child] = clock;
            stack.push((child, 0));
        } else {
            leave[node] = clock;
        }
    }
    (enter, leave)
}

/// The postorder position of each node the entry (node 0) reaches, and the
/// nodes in postorder.
fn postorder(succs: &[Vec<usize>], n: usize) -> (Vec<Option<usize>>, Vec<usize>) {
    let mut post = vec![None; n];
    let mut order = Vec::new();
    if n == 0 {
        return (post, order);
    }
    let mut seen = vec![false; n];
    let mut stack = vec![(0, 0)];
    seen[0] = true;
    while let Some((node, next)) = stack.pop() {
        if let Some(&s) = succs[node].get(next) {
            stack.push((node, next + 1));
            if !seen[s] {
                seen[s] = true;
                stack.push((s, 0));
            }
        } else {
            post[node] = Some(order.len());
            order.push(node);
        }
    }
    (post, order)
}

/// Immediate dominators by the iterative algorithm over reverse postorder.
fn dominators(
    succs: &[Vec<usize>],
    post: &[Option<usize>],
    order: &[usize],
    n: usize,
) -> Vec<usize> {
    let mut preds = vec![Vec::new(); n];
    for (from, tos) in succs.iter().enumerate() {
        for &to in tos {
            preds[to].push(from);
        }
    }
    let mut idom: Vec<Option<usize>> = vec![None; n];
    if n == 0 {
        return Vec::new();
    }
    idom[0] = Some(0);
    let mut changed = true;
    while changed {
        changed = false;
        for &b in order.iter().rev().filter(|&&b| b != 0) {
            let mut new = None;
            for &p in &preds[b] {
                if idom[p].is_none() {
                    continue;
                }
                new = Some(match new {
                    None => p,
                    Some(q) => intersect(&idom, post, p, q),
                });
            }
            if new.is_some() && idom[b] != new {
                idom[b] = new;
                changed = true;
            }
        }
    }
    idom.into_iter()
        .enumerate()
        .map(|(i, d)| d.unwrap_or(i))
        .collect()
}

fn intersect(idom: &[Option<usize>], post: &[Option<usize>], mut a: usize, mut b: usize) -> usize {
    let at = |x: usize| post[x].expect("a processed node is reachable");
    let up = |x: usize| idom[x].expect("a processed node has a dominator");
    while a != b {
        while at(a) < at(b) {
            a = up(a);
        }
        while at(b) < at(a) {
            b = up(b);
        }
    }
    a
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Block, LocRef, Op};

    /// A function whose block `i` branches to the blocks `edges[i]`.
    fn graph(edges: &[Vec<usize>]) -> Func {
        let mut f = Func::new("g");
        for (i, tos) in edges.iter().enumerate() {
            let mut op = Op::new("toy.br", LocRef(0));
            for t in tos {
                op = op.succ(format!("b{t}"), &[]);
            }
            f = f.block(Block::new(format!("b{i}")).op(op));
        }
        f
    }

    /// `ReachesAvoiding` as the spec defines it.
    fn reaches_avoiding(edges: &[Vec<usize>], a: usize, b: usize) -> bool {
        if a == 0 {
            return false;
        }
        let mut seen = vec![false; edges.len()];
        let mut stack = vec![0];
        seen[0] = true;
        while let Some(x) = stack.pop() {
            for &y in &edges[x] {
                if y != a && !seen[y] {
                    seen[y] = true;
                    stack.push(y);
                }
            }
        }
        seen[b]
    }

    #[test]
    fn dominance_matches_the_spec_on_random_graphs() {
        let mut seed = 0x9e37_79b9_7f4a_7c15_u64;
        let mut next = move |m: u64| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed % m
        };
        for _ in 0..500 {
            let n = 1 + next(9) as usize;
            let edges: Vec<Vec<usize>> = (0..n)
                .map(|_| (0..next(4)).map(|_| next(n as u64) as usize).collect())
                .collect();
            let f = graph(&edges);
            let cfg = Cfg::new(&f);
            for a in 0..n {
                assert_eq!(
                    cfg.reachable(&format!("b{a}")),
                    a == 0 || reaches_avoiding(&edges, n + 1, a)
                );
                for b in 0..n {
                    let spec = a == b || !reaches_avoiding(&edges, a, b);
                    assert_eq!(
                        cfg.dominates(&format!("b{a}"), &format!("b{b}")),
                        spec,
                        "{edges:?} {a} {b}"
                    );
                }
            }
        }
    }
}
