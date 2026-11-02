//! The stack that a run of each function needs, with its calls
//! (ADR-2026-11-02-1132).
//!
//! A function's need is the stack it uses below the return address that its
//! caller pushes: that address and its saved `%rbp`, its frame, and the
//! deepest of its calls, each with the arguments it pushes and the callee's
//! own need. A call between two functions of one cycle, such as a function
//! that calls itself or two that call each other, is left out: how deep a
//! cycle goes depends on the arguments, so no figure from the code bounds
//! it. Without those calls the call graph has no cycle, and each need is a
//! sum along its deepest path. A function from which a cycle is reachable is
//! marked recursive: its need is then the least that a run needs, and the
//! runtime gives it as much stack as memory allows.
//!
//! Nothing here recurses once per call: the cycles are found by Tarjan's
//! algorithm with the path on the heap, so a chain of any length is sized
//! on a small stack.

use std::collections::HashMap;

use funk_ir::{Func, Module};

use crate::lower::{callee, pushed_words};

/// The stack a run of one function needs.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Need {
    /// The bytes below the caller's return address: the most that any run
    /// uses when the function is not recursive, and otherwise the most that
    /// a run uses when it makes no call within a cycle.
    pub bytes: u64,
    /// Whether a cycle of calls is reachable from the function, so that a
    /// run may need more than `bytes`, as many more as its arguments say.
    pub recursive: bool,
}

/// One call of a function: the index of its callee, and the bytes of
/// arguments and padding that it pushes.
type Call = (usize, u64);

/// The need of each function of `m`, in order, where `frames` gives the size
/// of each one's frame. A call names its callee by symbol; the first
/// function with that symbol is the one called, as the verifier reads it.
pub fn needs(m: &Module, frames: &[i32]) -> Vec<Need> {
    let funcs: Vec<&Func> = m.funcs().collect();
    let mut index = HashMap::new();
    for (i, f) in funcs.iter().enumerate() {
        index.entry(f.name.as_str()).or_insert(i);
    }
    let calls: Vec<Vec<Call>> = funcs
        .iter()
        .map(|f| {
            let ops = f.body.blocks.iter().flat_map(|b| &b.ops);
            ops.filter_map(|op| {
                let i = *index.get(callee(op)?)?;
                let words = u64::try_from(pushed_words(op.operands.len())).unwrap_or(u64::MAX);
                Some((i, words.saturating_mul(8)))
            })
            .collect()
        })
        .collect();
    let own = |i: usize| {
        let frame = frames.get(i).map_or(0, |s| u64::from(s.unsigned_abs()));
        frame.saturating_add(16)
    };
    let mut out = vec![Need::default(); funcs.len()];
    let mut component = vec![0; funcs.len()];
    // Each component comes after every component that it calls, whose
    // needs are known by then; a call within the component does not count.
    for (c, members) in components(&calls).into_iter().enumerate() {
        for &f in &members {
            component[f] = c + 1;
        }
        let cycle = members.len() > 1 || calls[members[0]].iter().any(|&(g, _)| g == members[0]);
        for &f in &members {
            let mut need = Need {
                bytes: 0,
                recursive: cycle,
            };
            for &(g, pushed) in &calls[f] {
                if component[g] == c + 1 {
                    continue;
                }
                let below = out[g];
                need.bytes = need.bytes.max(pushed.saturating_add(below.bytes));
                need.recursive |= below.recursive;
            }
            need.bytes = need.bytes.saturating_add(own(f));
            out[f] = need;
        }
    }
    out
}

/// The strongly connected components of the call graph `calls`, by
/// Tarjan's algorithm, each after every component that it calls. A
/// component is one function, or the functions of a cycle of calls.
fn components(calls: &[Vec<Call>]) -> Vec<Vec<usize>> {
    const UNSEEN: usize = usize::MAX;
    let n = calls.len();
    let (mut order, mut low) = (vec![UNSEEN; n], vec![0; n]);
    let mut on_path = vec![false; n];
    let (mut path, mut out, mut next) = (Vec::new(), Vec::new(), 0);
    for root in 0..n {
        if order[root] != UNSEEN {
            continue;
        }
        // The functions being visited, each with its next call to follow.
        let mut work = vec![(root, 0)];
        (order[root], low[root], next) = (next, next, next + 1);
        path.push(root);
        on_path[root] = true;
        while let Some(top) = work.last_mut() {
            let (f, k) = *top;
            if let Some(&(g, _)) = calls[f].get(k) {
                top.1 += 1;
                if order[g] == UNSEEN {
                    (order[g], low[g], next) = (next, next, next + 1);
                    path.push(g);
                    on_path[g] = true;
                    work.push((g, 0));
                } else if on_path[g] {
                    low[f] = low[f].min(order[g]);
                }
                continue;
            }
            work.pop();
            if let Some(&(caller, _)) = work.last() {
                low[caller] = low[caller].min(low[f]);
            }
            if low[f] == order[f] {
                let mut members = Vec::new();
                while let Some(g) = path.pop() {
                    on_path[g] = false;
                    members.push(g);
                    if g == f {
                        break;
                    }
                }
                out.push(members);
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use funk_ir::{Attr, Block, Location, Op};

    use super::*;

    /// A module of the functions `funcs`, each a name and its calls in
    /// order, each call a callee and a number of arguments. Only the calls
    /// matter here, so the module need not be valid.
    fn module(funcs: &[(&str, &[(&str, usize)])]) -> Module {
        let mut m = Module::new();
        let here = m.locs.push(Location::Unknown);
        for (name, calls) in funcs {
            let mut b = Block::new("entry");
            for (callee, args) in *calls {
                let mut op = Op::new("call", here).attr(Attr::Sym(callee.to_string()));
                for _ in 0..*args {
                    op = op.operand("x");
                }
                b = b.op(op);
            }
            m = m.func(Func::new(*name).block(b.op(Op::new("ret", here))));
        }
        m
    }

    fn need(bytes: u64, recursive: bool) -> Need {
        Need { bytes, recursive }
    }

    #[test]
    fn a_function_that_calls_nothing_needs_its_frame() {
        let m = module(&[("f", &[]), ("g", &[])]);
        assert_eq!(needs(&m, &[0, 4096]), [need(16, false), need(4112, false)]);
    }

    #[test]
    fn a_chain_of_calls_needs_every_frame_on_it() {
        let m = module(&[("a", &[("b", 1)]), ("b", &[("c", 0)]), ("c", &[])]);
        let c = 16 + 48;
        let b = 16 + 4096 + c;
        let a = 16 + 32 + b;
        assert_eq!(
            needs(&m, &[32, 4096, 48]),
            [need(a, false), need(b, false), need(c, false)]
        );
    }

    /// The arguments past the sixth are pushed, padded to an even number,
    /// as `lower/call.rs` pushes them.
    #[test]
    fn a_call_needs_the_arguments_it_pushes() {
        for (args, pushed) in [(0, 0), (6, 0), (7, 16), (8, 16), (9, 32), (12, 48)] {
            let m = module(&[("f", &[("g", args)]), ("g", &[])]);
            assert_eq!(needs(&m, &[16, 16])[0], need(32 + pushed + 32, false));
        }
    }

    /// Calls one after another reuse the same stack: the need is the
    /// deepest of them, not their sum.
    #[test]
    fn a_function_needs_its_deepest_call_only() {
        let m = module(&[
            ("a", &[("b", 0), ("c", 8), ("b", 0)]),
            ("b", &[("d", 0)]),
            ("c", &[("d", 0)]),
            ("d", &[]),
        ]);
        let d = 16 + 64;
        let (b, c) = (16 + 1024 + d, 16 + 16 + d);
        let a = 16 + (b).max(16 + c);
        let got = needs(&m, &[0, 1024, 16, 64]);
        assert_eq!(
            got,
            [
                need(a, false),
                need(b, false),
                need(c, false),
                need(d, false)
            ]
        );
    }

    /// A callee may come before or after its caller, and a call is to the
    /// first function of its symbol.
    #[test]
    fn a_callee_is_the_first_function_of_its_symbol_wherever_it_is() {
        let m = module(&[("main", &[("leaf", 0)]), ("leaf", &[]), ("leaf", &[])]);
        assert_eq!(needs(&m, &[0, 32, 4096])[0], need(16 + 16 + 32, false));
        let m = module(&[("leaf", &[]), ("main", &[("leaf", 0)])]);
        assert_eq!(needs(&m, &[32, 0])[1], need(16 + 16 + 32, false));
    }

    /// A call to itself is left out of the need, and makes the function
    /// recursive; its other calls still count.
    #[test]
    fn a_function_that_calls_itself_is_recursive() {
        let m = module(&[("f", &[("f", 0), ("g", 0), ("f", 7)]), ("g", &[])]);
        let g = 16 + 256;
        assert_eq!(
            needs(&m, &[32, 256]),
            [need(16 + 32 + g, true), need(g, false)]
        );
    }

    #[test]
    fn functions_that_call_each_other_are_recursive() {
        let m = module(&[
            ("even", &[("odd", 0)]),
            ("odd", &[("even", 0), ("leaf", 7)]),
            ("leaf", &[]),
        ]);
        let leaf = 16 + 16;
        assert_eq!(
            needs(&m, &[32, 48, 16]),
            [
                need(16 + 32, true),
                need(16 + 48 + 16 + leaf, true),
                need(leaf, false)
            ]
        );
    }

    /// A function that reaches a cycle through a call is recursive, and
    /// needs at least what the cycle's function needs without its cycle.
    /// A cycle elsewhere in the module changes nothing.
    #[test]
    fn a_function_that_reaches_a_cycle_is_recursive() {
        let m = module(&[
            ("main", &[("helper", 0), ("fact", 0)]),
            ("fact", &[("fact", 0)]),
            ("helper", &[]),
            ("plain", &[("helper", 0)]),
        ]);
        let got = needs(&m, &[16, 4096, 0, 0]);
        assert_eq!(got[0], need(16 + 16 + 16 + 4096, true));
        assert_eq!(got[1], need(16 + 4096, true));
        assert_eq!(got[2], need(16, false));
        assert_eq!(got[3], need(32, false));
    }

    /// A chain or a cycle of 100,000 functions is sized without
    /// recursing once per call, on a test thread's small stack.
    #[test]
    fn a_long_chain_and_a_long_cycle_are_sized_on_a_small_stack() {
        let n = 100_000;
        let names: Vec<String> = (0..=n).map(|i| format!("f{i}")).collect();
        let calls: Vec<[(&str, usize); 1]> = names[1..].iter().map(|g| [(g.as_str(), 0)]).collect();
        let mut funcs: Vec<(&str, &[(&str, usize)])> = names[..n]
            .iter()
            .zip(&calls)
            .map(|(f, c)| (f.as_str(), c.as_slice()))
            .collect();
        funcs.push((names[n].as_str(), &[]));
        let frames = vec![16; n + 1];
        let chain = needs(&module(&funcs), &frames);
        let total = 32 * (n as u64 + 1);
        assert_eq!(chain[0], need(total, false));
        assert_eq!(chain[n], need(32, false));
        let back = [("f0", 0)];
        funcs[n] = (names[n].as_str(), &back);
        let cycle = needs(&module(&funcs), &frames);
        assert!(cycle.iter().all(|&x| x == need(32, true)));
    }
}
