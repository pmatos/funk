//! The second dialect in tree, `gpu` (ADR-2026-11-09-1545), on the shared
//! cases of `tests/dialects/gpu.cases`. `lean/FirTest/Gpu.lean` reads them
//! too, so the two sides agree on each of them. Each case is read with the
//! core and `gpu` registered, as `funk` reads it: an accepted case parses,
//! prints as itself and verifies; an invalid one parses, prints as itself and
//! does not verify; a malformed one does not parse.

use funk_ir::dialects::in_tree;
use funk_ir::{Registry, parse, print, verify};

const CASES: &str = include_str!("../../../tests/dialects/gpu.cases");

struct Case {
    verdict: &'static str,
    name: &'static str,
    text: &'static str,
}

fn cases() -> Vec<Case> {
    CASES
        .split("=== ")
        .skip(1)
        .map(|piece| {
            let (head, text) = piece.split_once('\n').expect("a case has a first line");
            let (verdict, name) = head.split_once(' ').expect("a verdict and a name");
            Case {
                verdict,
                name,
                text,
            }
        })
        .collect()
}

#[test]
fn the_shared_cases_are_all_read() {
    let cases = cases();
    assert_eq!(cases.len(), 8);
    assert_eq!(cases.iter().filter(|c| c.verdict == "accept").count(), 2);
    assert_eq!(cases.iter().filter(|c| c.verdict == "malformed").count(), 3);
}

#[test]
fn each_case_gets_its_verdict() {
    let reg = in_tree();
    for c in cases() {
        match (parse(c.text, &reg), c.verdict) {
            (Ok(m), "accept" | "invalid") => {
                assert_eq!(print(&m), c.text, "{}", c.name);
                let ds = verify(&m, &reg);
                assert_eq!(ds.is_empty(), c.verdict == "accept", "{}: {ds:#?}", c.name);
            }
            (Err(_), "malformed") => {}
            (r, v) => panic!("{}: {v}, but {:?}", c.name, r.map(|_| ())),
        }
    }
}

#[test]
fn each_rejection_names_its_rule() {
    let reg = in_tree();
    for (name, needle) in [
        ("an-i64-id", "gives an i32"),
        ("device-module-without-gpu", "the dialect gpu"),
        ("device-memory-not-declared", "memory 3"),
    ] {
        let c = cases().into_iter().find(|c| c.name == name).unwrap();
        let ds = verify(&parse(c.text, &reg).unwrap(), &reg);
        assert_eq!(ds.len(), 1, "{name}: {ds:#?}");
        assert!(ds[0].message.contains(needle), "{name}: {}", ds[0]);
    }
}

#[test]
fn the_core_alone_reads_no_word_of_gpu() {
    let core = Registry::core();
    for c in cases().into_iter().filter(|c| c.verdict == "accept") {
        assert!(parse(c.text, &core).is_err(), "{}", c.name);
    }
}
