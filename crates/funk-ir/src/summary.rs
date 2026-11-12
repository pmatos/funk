//! Function summaries: the effects that a call of each function of a symbol
//! table may have (`lean/Fir/Execution/Summary.lean`, ADR-2026-11-10-2108).
//!
//! An op's [`Effects`] are those of its own rule; an op that calls a
//! function has its callee's too. A function's summary joins what a caller
//! sees of each op of each function that it reaches through calls: every
//! effect of those ops but control, since a terminator of a callee ends a
//! block of the callee. A call of a symbol that names no function of the
//! table has every effect but control. Calls resolve in the table that
//! holds the caller, so [`Summaries::of`] takes the items of one table: a
//! module's, or a nested module's.
//!
//! The spec defines each summary by a walk over the functions that one function
//! reaches, and proves it the least fixpoint of the calls and sound: a function
//! whose summary leaves out may-UB never ends in UB, and one whose summary
//! leaves out may produce poison returns no poison on arguments with none. Here
//! every summary comes from one pass over the call graph's strongly connected
//! components, callees first: the functions of a component reach each other, so
//! they share a summary. The pass keeps its path on the heap, so a long chain
//! of calls or a deep recursion takes no stack per call
//! (`docs/decisions/rust-ir-and-tools.md#nesting`). A summary is a set, so its
//! memories are kept in sorted order; the shared cases of
//! `tests/dialects/effect-summaries.cases` check that each one equals Lean's.

use std::collections::HashMap;

use crate::effects::Effects;
use crate::ir::{Func, Item, Op, Type};
use crate::registry::{OpTypes, Registry};
use crate::verify::all_blocks;

/// What a function's op says of itself: the effects of its own rule, and the
/// symbol it calls.
struct OpInfo {
    own: Effects,
    callee: Option<String>,
}

/// The type of each value of `f`: its first definition, at any depth.
fn value_types(f: &Func) -> HashMap<&str, &Type> {
    let mut types = HashMap::new();
    let defs = f.params.iter().chain(
        all_blocks(&f.body)
            .into_iter()
            .flat_map(|b| b.params.iter().chain(b.ops.iter().flat_map(|o| &o.results))),
    );
    for d in defs {
        types.entry(d.name.as_str()).or_insert(&d.ty);
    }
    types
}

/// What `op` says of itself, its operands typed by `types`. An op that the
/// registry cannot decode has every effect: nothing narrower is known of it.
fn op_info(reg: &Registry, types: &HashMap<&str, &Type>, op: &Op) -> OpInfo {
    let unknown = OpInfo {
        own: Effects::ALL,
        callee: None,
    };
    let operands: Option<Vec<Type>> = op
        .operands
        .iter()
        .map(|x| types.get(x.as_str()).map(|t| (*t).clone()))
        .collect();
    let (Some(spec), Some(operands)) = (reg.op(&op.name), operands) else {
        return unknown;
    };
    let results: Vec<Type> = op.results.iter().map(|d| d.ty.clone()).collect();
    let ty = OpTypes {
        attrs: &op.attrs,
        operands: &operands,
        results: &results,
    };
    let Ok(shape) = spec.decode(&ty) else {
        return unknown;
    };
    OpInfo {
        own: spec.effects(&ty),
        callee: if shape.terminator {
            None
        } else {
            spec.callee(&ty)
        },
    }
}

/// The ops of `f` at any depth, in the spec's order (`Func.allOps`): the ops
/// of each block, each block before the blocks of its ops' regions.
fn all_ops(f: &Func) -> impl Iterator<Item = &Op> {
    all_blocks(&f.body).into_iter().flat_map(|b| &b.ops)
}

/// The summaries of the functions of one symbol table.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Summaries {
    by_name: HashMap<String, Effects>,
}

impl Summaries {
    /// The summaries of the functions of the symbol table whose items are
    /// `items`: those of a [`Module`](crate::Module), or of a
    /// [`NestedModule`](crate::NestedModule). A symbol names its first
    /// function, as the interpreter finds a callee.
    pub fn of(items: &[Item], reg: &Registry) -> Summaries {
        let mut funcs: Vec<&Func> = Vec::new();
        let mut index: HashMap<&str, usize> = HashMap::new();
        for f in items.iter().filter_map(Item::as_func) {
            if !index.contains_key(f.name.as_str()) {
                index.insert(&f.name, funcs.len());
                funcs.push(f);
            }
        }
        let mut own = Vec::with_capacity(funcs.len());
        let mut edges = Vec::with_capacity(funcs.len());
        for f in &funcs {
            let types = value_types(f);
            let mut sees = Effects::PURE;
            let mut calls = Vec::new();
            for op in all_ops(f) {
                let info = op_info(reg, &types, op);
                let mut e = info.own;
                match info.callee.as_deref().map(|c| index.get(c)) {
                    Some(Some(&g)) => calls.push(g),
                    Some(None) => e = e.join(&Effects::ALL),
                    None => {}
                }
                sees = sees.join(&e.caller_view());
            }
            calls.sort_unstable();
            calls.dedup();
            own.push(sees);
            edges.push(calls);
        }
        let mut sums: Vec<Option<Effects>> = vec![None; funcs.len()];
        for comp in components(&edges) {
            let mut s = Effects::PURE;
            for &v in &comp {
                s = s.join(&own[v]);
                for &w in &edges[v] {
                    if let Some(sw) = &sums[w] {
                        s = s.join(sw);
                    }
                }
            }
            let s = s.sorted();
            for &v in &comp {
                sums[v] = Some(s.clone());
            }
        }
        let by_name = funcs
            .iter()
            .zip(sums)
            .map(|(f, s)| (f.name.clone(), s.expect("every function is in a component")))
            .collect();
        Summaries { by_name }
    }

    /// The summary of the function that `name` names (`SymbolTable.summary`),
    /// or `None` when it names no function of the table. Lean gives such a
    /// symbol the empty summary, but a call of it has every effect but
    /// control, so a caller that reads a summary here must not take `None`
    /// for pure: [`InFunc::op_effects`] gives a call its effects.
    pub fn summary(&self, name: &str) -> Option<&Effects> {
        self.by_name.get(name)
    }

    /// The effects of the ops of the function `f` of the table, in place:
    /// the types of `f`'s values are found once, for every op asked about.
    pub fn in_func<'a>(&'a self, reg: &'a Registry, f: &'a Func) -> InFunc<'a> {
        InFunc {
            summaries: self,
            reg,
            types: value_types(f),
        }
    }
}

/// The effects of the ops of one function of a table, in place.
pub struct InFunc<'a> {
    summaries: &'a Summaries,
    reg: &'a Registry,
    types: HashMap<&'a str, &'a Type>,
}

impl InFunc<'_> {
    /// The effects of `op` in place (`SymbolTable.opEffects`): those of its
    /// own rule and, when it calls a function, its callee's summary, or every
    /// effect but control when its callee names no function of the table. An
    /// op that the registry cannot decode has every effect, control
    /// included, since nothing narrower is known of it.
    pub fn op_effects(&self, op: &Op) -> Effects {
        let info = op_info(self.reg, &self.types, op);
        let e = match info.callee {
            Some(c) => match self.summaries.summary(&c) {
                Some(s) => info.own.join(s),
                None => info.own.join(&Effects::ALL.caller_view()),
            },
            None => info.own,
        };
        e.sorted()
    }
}

/// The state of Tarjan's walk: each node's index and low link, and the
/// nodes of the components not yet closed.
struct Tarjan {
    index: Vec<usize>,
    low: Vec<usize>,
    on_stack: Vec<bool>,
    stack: Vec<usize>,
    next: usize,
}

impl Tarjan {
    const UNSEEN: usize = usize::MAX;

    /// Gives `v` the next index and puts it on the stack and the path.
    fn enter(&mut self, v: usize, path: &mut Vec<(usize, usize)>) {
        self.index[v] = self.next;
        self.low[v] = self.next;
        self.next += 1;
        self.stack.push(v);
        self.on_stack[v] = true;
        path.push((v, 0));
    }

    /// The component that `v` closes: the nodes of the stack down to `v`.
    fn close(&mut self, v: usize) -> Vec<usize> {
        let mut comp = Vec::new();
        while let Some(w) = self.stack.pop() {
            self.on_stack[w] = false;
            comp.push(w);
            if w == v {
                break;
            }
        }
        comp
    }
}

/// The strongly connected components of the graph whose node `v` has the
/// edges `edges[v]`, each component after every component that it reaches
/// (Tarjan's algorithm). The walk keeps its path in a vector, not on the
/// stack.
fn components(edges: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let n = edges.len();
    let mut t = Tarjan {
        index: vec![Tarjan::UNSEEN; n],
        low: vec![0; n],
        on_stack: vec![false; n],
        stack: Vec::new(),
        next: 0,
    };
    let mut comps = Vec::new();
    let mut path: Vec<(usize, usize)> = Vec::new();
    for root in 0..n {
        if t.index[root] != Tarjan::UNSEEN {
            continue;
        }
        t.enter(root, &mut path);
        while let Some(&(v, i)) = path.last() {
            if let Some(&w) = edges[v].get(i) {
                let top = path.len() - 1;
                path[top].1 += 1;
                if t.index[w] == Tarjan::UNSEEN {
                    t.enter(w, &mut path);
                } else if t.on_stack[w] {
                    t.low[v] = t.low[v].min(t.index[w]);
                }
                continue;
            }
            path.pop();
            if let Some(&(u, _)) = path.last() {
                t.low[u] = t.low[u].min(t.low[v]);
            }
            if t.low[v] == t.index[v] {
                comps.push(t.close(v));
            }
        }
    }
    comps
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn components_come_callees_first() {
        // 0 -> 1 <-> 2 -> 3, and 4 alone.
        let edges = vec![vec![1], vec![2], vec![1, 3], vec![], vec![]];
        let comps: Vec<Vec<usize>> = components(&edges)
            .into_iter()
            .map(|mut c| {
                c.sort();
                c
            })
            .collect();
        assert_eq!(comps, vec![vec![3], vec![1, 2], vec![0], vec![4]]);
    }

    #[test]
    fn a_long_chain_takes_no_stack_per_call() {
        let n = 200_000;
        let edges: Vec<Vec<usize>> = (0..n)
            .map(|v| if v + 1 < n { vec![v + 1] } else { vec![0] })
            .collect();
        let comps = components(&edges);
        assert_eq!(comps.len(), 1);
        assert_eq!(comps[0].len(), n);
    }
}
