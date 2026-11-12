//! The effect summaries of functions (ADR-2026-11-09-1541), on the shared
//! cases of `tests/dialects/effect-summaries.cases`, which
//! `lean/FirTest/SummaryCases.lean` reads too, so each summary here is
//! `SymbolTable.summary`. Each case gives the summary of every function of
//! every symbol table of its module, by the path of symbols that leads to
//! it.

use funk_ir::{Effects, Func, Item, MemSet, Module, Registry, Summaries, parse, verify};

const CASES: &str = include_str!("../../../tests/dialects/effect-summaries.cases");

struct Case {
    name: &'static str,
    sums: Vec<(Vec<&'static str>, &'static str)>,
    text: String,
}

fn cases() -> Vec<Case> {
    CASES
        .split("=== ")
        .skip(1)
        .map(|piece| {
            let mut lines = piece.lines();
            let name = lines.next().expect("a case has a name");
            let mut sums = Vec::new();
            let mut text = String::new();
            for line in lines {
                if text.is_empty() && line.starts_with('@') {
                    let mut words: Vec<&str> = line.split(' ').collect();
                    let set = words.pop().expect("a summary line names a set");
                    let path = words
                        .iter()
                        .map(|w| w.strip_prefix('@').expect("a path is of symbols"))
                        .collect();
                    sums.push((path, set));
                } else {
                    text.push_str(line);
                    text.push('\n');
                }
            }
            Case { name, sums, text }
        })
        .collect()
}

/// The items of the symbol table that `path` leads to, through nested
/// modules.
fn table<'m>(m: &'m Module, path: &[&str]) -> &'m [Item] {
    let mut items = m.items.as_slice();
    for name in path {
        items = items
            .iter()
            .find_map(|i| match i {
                Item::Module(n) if n.name == *name => Some(n.items.as_slice()),
                _ => None,
            })
            .unwrap_or_else(|| panic!("no module @{name}"));
    }
    items
}

/// The path of every function of every table under `items`, behind `pre`.
fn func_paths(pre: &[String], items: &[Item], out: &mut Vec<Vec<String>>) {
    for i in items {
        let mut path = pre.to_vec();
        path.push(i.name().to_string());
        match i {
            Item::Func(_) => out.push(path),
            Item::Module(n) => func_paths(&path, &n.items, out),
            _ => {}
        }
    }
}

#[test]
fn each_summary_is_the_one_lean_gives() {
    let reg = Registry::core();
    let cs = cases();
    assert_eq!(cs.len(), 11);
    for c in &cs {
        let m = parse(&c.text, &reg).unwrap_or_else(|e| panic!("{}: {e}", c.name));
        if c.name != "unknown-callee" {
            assert_eq!(verify(&m, &reg), vec![], "{}", c.name);
        }
        let mut paths = Vec::new();
        func_paths(&[], &m.items, &mut paths);
        let named: Vec<Vec<String>> = c
            .sums
            .iter()
            .map(|(p, _)| p.iter().map(|s| s.to_string()).collect())
            .collect();
        assert_eq!(named, paths, "{}: the case names every function", c.name);
        for (path, set) in &c.sums {
            let (func, outer) = path.split_last().expect("a path names a function");
            let s = Summaries::of(table(&m, outer), &reg);
            let sum = s
                .summary(func)
                .unwrap_or_else(|| panic!("{}: @{func}", c.name));
            assert_eq!(sum.to_string(), *set, "{}: {path:?}", c.name);
        }
    }
}

/// A call in place has its own effects and its callee's summary; a call of
/// no function has every effect but control.
#[test]
fn a_call_in_place_carries_its_callees_summary() {
    let reg = Registry::core();
    let chain = cases()
        .into_iter()
        .find(|c| c.name == "chain-of-three")
        .expect("the case exists");
    let m = parse(&chain.text, &reg).expect("the case parses");
    let s = Summaries::of(&m.items, &reg);
    let f: &Func = m.funcs().find(|f| f.name == "h").expect("@h");
    let ops = &f.body.blocks[0].ops;
    let in_h = s.in_func(&reg, f);
    assert_eq!(in_h.op_effects(&ops[0]).to_string(), "may-ub");
    assert_eq!(in_h.op_effects(&ops[1]).to_string(), "may-poison");
    assert_eq!(in_h.op_effects(&ops[2]).to_string(), "control");
    assert_eq!(s.summary("nowhere"), None);
    let lost = cases()
        .into_iter()
        .find(|c| c.name == "unknown-callee")
        .expect("the case exists");
    let m = parse(&lost.text, &reg).expect("the case parses");
    let f = m.funcs().next().expect("@f");
    let s = Summaries::of(&m.items, &reg);
    let e = s.in_func(&reg, f).op_effects(&f.body.blocks[0].ops[0]);
    assert_eq!(e, Effects::ALL.caller_view());
    assert_eq!(e.reads, MemSet::Every);
}

/// A chain of calls as long as a deep recursion would overflow takes no
/// stack per call.
#[test]
fn a_long_chain_of_calls_has_its_last_callees_effects() {
    let reg = Registry::core();
    let n = 20_000;
    let mut text = String::new();
    for i in 0..n {
        text.push_str(&format!(
            "func @f{i}(%a: i8) -> i8 {{\n^entry:\n  %r: i8 = call @f{} %a @0\n  ret %r @0\n}}\n\n",
            i + 1
        ));
    }
    text.push_str(&format!(
        "func @f{n}(%a: i8) -> i8 {{\n^entry:\n  %r: i8 = sdiv %a, %a @0\n  ret %r @0\n}}\n\nlocs {{\n  @0 = unknown\n}}\n"
    ));
    let m = parse(&text, &reg).expect("the chain parses");
    let s = Summaries::of(&m.items, &reg);
    assert_eq!(
        s.summary("f0").map(Effects::to_string),
        Some("may-ub".into())
    );
    let mid = format!("f{}", n / 2);
    assert_eq!(
        s.summary(&mid).map(Effects::to_string),
        Some("may-ub".into())
    );
}
