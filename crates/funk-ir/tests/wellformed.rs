//! The round trips over well-formed modules that are not all valid (#146):
//! `parse(print(m)) == m` and `print(parse(t)) == t` hold for every
//! well-formed module (ADR-2026-10-30-0815), not only for the valid ones
//! that `property.rs` checks. The modules come from
//! `generate::wellformed`, and the tests check that they hold every shape
//! that validation rejects and the round trip must still cover.

use std::collections::HashSet;

use funk_ir::generate::Rng;
use funk_ir::generate::wellformed::{self, Dialects, TOY_OP, WELL_FORMED_MODULES};
use funk_ir::{Attr, Block, Func, LocTable, Location, Module, Op, Registry, parse, print, verify};

/// The core dialect and the toy dialect of the generator.
fn registry() -> Registry {
    let mut reg = Registry::core();
    reg.register(wellformed::toy_dialect())
        .expect("the toy dialect registers");
    reg
}

fn generated(dialects: Dialects) -> impl Iterator<Item = (u64, Module)> {
    (0..WELL_FORMED_MODULES).map(move |seed| {
        let m = wellformed::module(&mut Rng::new(seed), dialects);
        (seed, m)
    })
}

/// Checks both round trips on `m`, with the registry `reg`.
fn round_trips(seed: u64, m: &Module, reg: &Registry) {
    let text = print(m);
    let back = parse(&text, reg).unwrap_or_else(|e| panic!("seed {seed}: {e}\n{text}"));
    assert_eq!(&back, m, "seed {seed}\n{text}");
    assert_eq!(print(&back), text, "seed {seed}");
}

#[test]
fn well_formed_modules_round_trip() {
    let (core, both) = (Registry::core(), registry());
    for (seed, m) in generated(Dialects::Core) {
        round_trips(seed, &m, &core);
        round_trips(seed, &m, &both);
    }
    for (seed, m) in generated(Dialects::CoreAndToy) {
        round_trips(seed, &m, &both);
    }
}

#[test]
fn the_generator_is_deterministic_and_keeps_core_modules_core() {
    for (seed, m) in generated(Dialects::Core).take(100) {
        let again = wellformed::module(&mut Rng::new(seed), Dialects::Core);
        assert_eq!(m, again, "seed {seed}");
        assert!(ops(&m).iter().all(|op| op.name != TOY_OP), "seed {seed}");
    }
}

/// Every block of `f`, at any depth.
fn blocks(f: &Func) -> Vec<&Block> {
    let mut out = Vec::new();
    let mut stack: Vec<&Block> = f.body.blocks.iter().rev().collect();
    while let Some(b) = stack.pop() {
        out.push(b);
        for op in b.ops.iter().rev() {
            for r in op.regions.iter().rev() {
                stack.extend(r.blocks.iter().rev());
            }
        }
    }
    out
}

/// Every op of the module, at any depth.
fn ops(m: &Module) -> Vec<&Op> {
    m.funcs()
        .flat_map(|f| blocks(f).into_iter().flat_map(|b| &b.ops))
        .collect()
}

/// Every attribute of the op, at any depth.
fn attrs(op: &Op) -> Vec<&Attr> {
    let mut out = Vec::new();
    let mut stack: Vec<&Attr> = op.attrs.iter().collect();
    while let Some(a) = stack.pop() {
        out.push(a);
        if let Attr::App(_, args) = a {
            stack.extend(args);
        }
    }
    out
}

/// Whether some top-level block of `f` is not reached from its entry by
/// the successors of the top-level blocks' ops.
fn has_unreachable_block(f: &Func) -> bool {
    let bs = &f.body.blocks;
    let mut seen = vec![false; bs.len()];
    let mut stack = vec![0];
    while let Some(k) = stack.pop() {
        if bs.is_empty() || seen[k] {
            continue;
        }
        seen[k] = true;
        for s in bs[k].ops.iter().flat_map(|op| &op.succs) {
            stack.extend(bs.iter().position(|b| b.label == s.label));
        }
    }
    seen.contains(&false)
}

/// Whether the table is valid (`LocTable.Valid`): references in increasing
/// order, each location built from entries before it, ranges well formed
/// and fused locations of two or more references.
fn table_is_valid(t: &LocTable) -> bool {
    let keys: Vec<u32> = t.entries.iter().map(|(r, _)| r.0).collect();
    keys.windows(2).all(|w| w[0] < w[1])
        && t.entries.iter().all(|(r, l)| {
            let ok = match l {
                Location::Range {
                    start_line: l1,
                    start_col: c1,
                    end_line: l2,
                    end_col: c2,
                    ..
                } => *l1 >= 1 && (l1 < l2 || (l1 == l2 && (*c1 == 0 || *c2 == 0 || c1 <= c2))),
                Location::Fused(refs) => refs.len() >= 2,
                _ => true,
            };
            ok && l.refs().iter().all(|x| x < r && keys.contains(&x.0))
        })
}

/// How many modules hold each shape that the round trip must cover and
/// validation rejects, and how many are rejected.
#[derive(Debug, Default)]
struct Shapes {
    core_regions: usize,
    toy_regions: usize,
    nested_regions: usize,
    strings: usize,
    applied: usize,
    applied_to_none: usize,
    fused_none: usize,
    fused_one: usize,
    unreachable: usize,
    undefined_labels: usize,
    undefined_args: usize,
    undefined_callees: usize,
    broken_tables: usize,
    missing_locs: usize,
    rejected: usize,
}

fn shapes(dialects: Dialects) -> Shapes {
    let reg = registry();
    let mut n = Shapes::default();
    for (_, m) in generated(dialects) {
        let symbols: HashSet<&str> = m.funcs().map(|f| f.name.as_str()).collect();
        let keys: HashSet<u32> = m.locs.entries.iter().map(|(r, _)| r.0).collect();
        let all = ops(&m);
        let has = |count: &mut usize, yes: bool| *count += usize::from(yes);
        let owners = all.iter().filter(|op| !op.regions.is_empty());
        has(
            &mut n.core_regions,
            owners.clone().any(|op| op.name != TOY_OP),
        );
        has(
            &mut n.toy_regions,
            owners.clone().any(|op| op.name == TOY_OP),
        );
        let nested = owners
            .flat_map(|op| &op.regions)
            .flat_map(|r| &r.blocks)
            .flat_map(|b| &b.ops)
            .any(|op| !op.regions.is_empty());
        has(&mut n.nested_regions, nested);
        let attrs: Vec<&Attr> = all.iter().flat_map(|op| attrs(op)).collect();
        has(
            &mut n.strings,
            attrs.iter().any(|a| matches!(a, Attr::Str(_))),
        );
        let applied =
            |a: &&Attr, none: bool| matches!(a, Attr::App(_, xs) if xs.is_empty() == none);
        has(&mut n.applied, attrs.iter().any(|a| applied(a, false)));
        has(
            &mut n.applied_to_none,
            attrs.iter().any(|a| applied(a, true)),
        );
        let fused = |k: usize| {
            m.locs
                .entries
                .iter()
                .any(|(_, l)| matches!(l, Location::Fused(r) if r.len() == k))
        };
        has(&mut n.fused_none, fused(0));
        has(&mut n.fused_one, fused(1));
        has(&mut n.unreachable, m.funcs().any(has_unreachable_block));
        let (mut labels, mut args) = (false, false);
        for f in m.funcs() {
            let bs = blocks(f);
            let defined: HashSet<&str> = f
                .params
                .iter()
                .chain(bs.iter().flat_map(|b| &b.params))
                .chain(bs.iter().flat_map(|b| &b.ops).flat_map(|op| &op.results))
                .map(|d| d.name.as_str())
                .collect();
            for s in bs.iter().flat_map(|b| &b.ops).flat_map(|op| &op.succs) {
                labels |= bs.iter().all(|b| b.label != s.label);
                args |= s.args.iter().any(|a| !defined.contains(a.as_str()));
            }
        }
        has(&mut n.undefined_labels, labels);
        has(&mut n.undefined_args, args);
        let callee = |op: &&&Op| match op.attrs.as_slice() {
            [Attr::Sym(s)] => op.name == "call" && !symbols.contains(s.as_str()),
            _ => false,
        };
        has(&mut n.undefined_callees, all.iter().any(|op| callee(&op)));
        has(&mut n.broken_tables, !table_is_valid(&m.locs));
        has(
            &mut n.missing_locs,
            all.iter().any(|op| !keys.contains(&op.loc.0)),
        );
        has(&mut n.rejected, !verify(&m, &reg).is_empty());
    }
    n
}

/// Each shape is in at least a tenth of the modules, and nearly every module
/// is one that validation rejects. Toy ops, and so string and applied
/// attributes, are only in the modules that may hold them.
#[test]
fn the_generator_covers_what_validation_rejects() {
    let tenth = WELL_FORMED_MODULES as usize / 10;
    for dialects in [Dialects::Core, Dialects::CoreAndToy] {
        let n = shapes(dialects);
        let toy = dialects == Dialects::CoreAndToy;
        let common = [
            n.core_regions,
            n.nested_regions,
            n.fused_none,
            n.fused_one,
            n.unreachable,
            n.undefined_labels,
            n.undefined_args,
            n.undefined_callees,
            n.broken_tables,
            n.missing_locs,
        ];
        assert!(common.iter().all(|&k| k >= tenth), "{dialects:?}: {n:?}");
        let toy_only = [n.toy_regions, n.strings, n.applied, n.applied_to_none];
        if toy {
            assert!(toy_only.iter().all(|&k| k >= tenth), "{dialects:?}: {n:?}");
        } else {
            assert!(toy_only.iter().all(|&k| k == 0), "{dialects:?}: {n:?}");
        }
        assert!(n.rejected >= tenth * 9, "{dialects:?}: {n:?}");
    }
}
