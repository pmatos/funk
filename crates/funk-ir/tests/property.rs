//! Property tests over random modules and random texts.
//!
//! `parse(print(m)) == m` on valid modules from the generator, layout that
//! is not canonical parses to the same module, and the parser never panics:
//! whatever text it accepts round-trips, and whatever it rejects, it rejects
//! with an error.

use funk_ir::dialects::core::{BITWISE_OPS, SHIFT_OPS};
use funk_ir::generate::{self, Rng};
use funk_ir::text::quote;
use funk_ir::{Attr, Location, Module, Registry, parse, print, verify};

fn generated() -> impl Iterator<Item = (u64, Module)> {
    (0..generate::ROUND_TRIP_MODULES).map(|seed| (seed, generate::module(&mut Rng::new(seed))))
}

#[test]
fn generated_modules_are_valid_and_round_trip() {
    let reg = Registry::core();
    for (seed, m) in generated() {
        let ds = verify(&m, &reg);
        assert!(ds.is_empty(), "seed {seed}: {ds:#?}");
        let text = print(&m);
        let back = parse(&text, &reg).unwrap_or_else(|e| panic!("seed {seed}: {e}\n{text}"));
        assert_eq!(back, m, "seed {seed}");
        assert_eq!(print(&back), text, "seed {seed}");
    }
}

#[test]
fn the_generator_covers_what_the_round_trip_must_cover() {
    let (mut quoted, mut booleans, mut kinds, mut results) =
        (0, [false; 2], [false; 6], [false; 3]);
    for (_, m) in generated() {
        for f in m.funcs() {
            quoted += usize::from(!funk_ir::ir::names::is_word(&f.name));
            results[f.results.len().min(2)] = true;
            for op in f.body.blocks.iter().flat_map(|b| &b.ops) {
                for a in &op.attrs {
                    if let Attr::Word(w) = a {
                        booleans[usize::from(w == "true")] = true;
                    }
                }
            }
        }
        for (_, l) in &m.locs.entries {
            kinds[match l {
                Location::Unknown => 0,
                Location::Range { .. } => 1,
                Location::Name(_) => 2,
                Location::CallSite { .. } => 3,
                Location::Fused(_) => 4,
                Location::Derived(_) => 5,
            }] = true;
        }
    }
    assert!(quoted > 10 && booleans == [true; 2] && kinds == [true; 6] && results == [true; 3]);
}

#[test]
fn the_generator_makes_every_op_with_every_set_of_flags() {
    let mut seen = std::collections::BTreeSet::new();
    for (_, m) in generated() {
        for op in m.funcs().flat_map(|f| &f.body.blocks).flat_map(|b| &b.ops) {
            if op.name != "const" {
                let attrs = op.attrs.iter().map(|a| format!(" {a}"));
                seen.insert(
                    std::iter::once(op.name.clone())
                        .chain(attrs)
                        .collect::<String>(),
                );
            }
        }
    }
    let mut want = std::collections::BTreeSet::new();
    for op in ["add", "sub", "mul"] {
        for flags in funk_ir::dialects::core::WRAP_FLAG_SETS {
            want.insert(
                std::iter::once(op)
                    .chain(flags.iter().copied())
                    .collect::<Vec<_>>()
                    .join(" "),
            );
        }
    }
    want.extend(["freeze".to_string(), "ret".to_string()]);
    want.extend(
        BITWISE_OPS
            .iter()
            .chain(&SHIFT_OPS)
            .map(|op| op.to_string()),
    );
    want.extend(funk_ir::dialects::core::WIDTH_CHANGES.map(String::from));
    for (op, exact) in funk_ir::dialects::core::DIVISION_OPS {
        want.insert(op.to_string());
        if exact {
            want.insert(format!("{op} exact"));
        }
    }
    assert_eq!(seen, want);
}

/// The width changes that the generator makes, as `(op, M, N)`, from `iM`
/// to `iN`.
fn generated_width_changes() -> Vec<(String, u32, u32)> {
    let int_width = funk_ir::dialects::core::int_width;
    let mut out = Vec::new();
    for (_, m) in generated() {
        for f in m.funcs() {
            let defs = f.params.iter().chain(
                f.body
                    .blocks
                    .iter()
                    .flat_map(|b| b.ops.iter().flat_map(|o| &o.results)),
            );
            let types: std::collections::HashMap<&str, u32> = defs
                .map(|d| (d.name.as_str(), int_width(&d.ty).expect("an integer")))
                .collect();
            for op in f.body.blocks.iter().flat_map(|b| &b.ops) {
                if funk_ir::dialects::core::WIDTH_CHANGES.contains(&op.name.as_str()) {
                    let n = int_width(&op.results[0].ty).expect("an integer");
                    out.push((op.name.clone(), types[op.operands[0].as_str()], n));
                }
            }
        }
    }
    out
}

#[test]
fn the_generator_changes_widths_only_where_validation_allows() {
    let changes = generated_width_changes();
    for (op, m, n) in &changes {
        let valid = if op == "trunc" { n < m } else { m < n };
        assert!(valid, "{op} from i{m} to i{n}");
    }
    for op in funk_ir::dialects::core::WIDTH_CHANGES {
        let to_i1 = changes.iter().any(|(o, _, n)| o == op && *n == 1);
        let from_i1 = changes.iter().any(|(o, m, _)| o == op && *m == 1);
        assert!(if op == "trunc" { to_i1 } else { from_i1 }, "{op}");
        assert!(
            changes.iter().filter(|(o, ..)| o == op).count() > 20,
            "{op}"
        );
    }
}

/// Rewrites the layout of a text outside its strings: each space or line
/// feed becomes other whitespace or a comment, and the final line feed may
/// go.
fn relayout(text: &str, rng: &mut Rng) -> String {
    const SPACES: [&str; 5] = [" ", "  ", "\t", " // c \"x\" \\\n", "\n\n"];
    const LINES: [&str; 4] = ["\n", "\n\n", " // é\n", "\t\n "];
    let mut out = String::new();
    let mut in_string = false;
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '"' => in_string = !in_string,
            '\\' if in_string => {
                out.push(c);
                out.extend(chars.next());
                continue;
            }
            ' ' if !in_string => {
                out.push_str(rng.pick(&SPACES));
                continue;
            }
            '\n' if chars.peek().is_none() && rng.one_in(2) => continue,
            '\n' => {
                out.push_str(rng.pick(&LINES));
                continue;
            }
            _ => {}
        }
        out.push(c);
    }
    out
}

#[test]
fn layout_that_is_not_canonical_parses_to_the_same_module() {
    let reg = Registry::core();
    let mut rng = Rng::new(7);
    for (seed, m) in generated().take(200) {
        let text = relayout(&print(&m), &mut rng);
        let back = parse(&text, &reg).unwrap_or_else(|e| panic!("seed {seed}: {e}\n{text}"));
        assert_eq!(back, m, "seed {seed}\n{text}");
    }
}

/// Parses `text`; if it parses, checks that its module round-trips and that
/// verifying it does not panic.
fn parse_never_panics(text: &str, reg: &Registry) {
    if let Ok(m) = parse(text, reg) {
        let printed = print(&m);
        assert_eq!(parse(&printed, reg).as_ref(), Ok(&m), "{text:?}");
        let _ = verify(&m, reg);
    }
}

#[test]
fn the_parser_never_panics_on_mutated_texts() {
    let reg = Registry::core();
    let mut rng = Rng::new(42);
    const PIECES: [&str; 24] = [
        "%", "^", "@", "\"", "\\", "(", ")", "{", "}", ",", ":", "=", "->", "-", "0", "9", "i8",
        "const", "add", "ret", "locs", "\n", "\r", "\u{202e}",
    ];
    for (_, m) in generated().take(300) {
        let text = print(&m);
        for _ in 0..20 {
            let mut chars: Vec<char> = text.chars().collect();
            for _ in 0..1 + rng.below(3) {
                let at = rng.below(chars.len() as u64 + 1) as usize;
                match rng.below(3) {
                    0 if at < chars.len() => {
                        chars.remove(at);
                    }
                    1 => chars
                        .splice(at..at, rng.pick(&PIECES).chars())
                        .for_each(drop),
                    _ if at < chars.len() => {
                        chars[at] = rng.pick(&PIECES).chars().next().unwrap_or(' ')
                    }
                    _ => {}
                }
            }
            parse_never_panics(&chars.into_iter().collect::<String>(), &reg);
        }
    }
}

#[test]
fn the_parser_never_panics_on_random_token_soup() {
    let reg = Registry::core();
    let mut rng = Rng::new(1);
    const TOKENS: [&str; 50] = [
        "func",
        "@f",
        "@\"x y\"",
        "@1",
        "@4294967296",
        "(",
        ")",
        "{",
        "}",
        "%a",
        "%b",
        ": i32",
        ": i1",
        "=",
        "const",
        "add",
        "sub",
        "mul",
        "nuw",
        "nsw",
        "freeze",
        "and",
        "or",
        "xor",
        "shl",
        "lshr",
        "ashr",
        "zext",
        "sext",
        "trunc",
        ": i64",
        "sdiv",
        "udiv",
        "srem",
        "urem",
        "exact",
        "ret",
        "true",
        "-1",
        "1",
        "^entry",
        ":",
        ",",
        "->",
        "locs",
        "unknown",
        "\"s\"",
        "fused(",
        "// c\n",
        "\n",
    ];
    for _ in 0..20_000 {
        let n = rng.below(40);
        let text: Vec<&str> = (0..n).map(|_| *rng.pick(&TOKENS)).collect();
        parse_never_panics(&text.join(" "), &reg);
    }
    for _ in 0..5_000 {
        let bytes: Vec<u8> = (0..rng.below(64)).map(|_| rng.next_u64() as u8).collect();
        let _ = funk_ir::text::parse_bytes(&bytes, &reg);
    }
}

#[test]
fn strings_round_trip_through_every_escape() {
    let reg = Registry::core();
    let mut rng = Rng::new(3);
    for _ in 0..2_000 {
        let s: String = (0..rng.below(8))
            .filter_map(|_| char::from_u32(rng.below(0x2_0000) as u32))
            .collect();
        let text = format!("locs {{\n  @0 = name({})\n}}\n", quote(&s));
        let m = parse(&text, &reg).unwrap_or_else(|e| panic!("{e}: {s:?}"));
        assert_eq!(m.locs.entries[0].1, Location::Name(s));
        assert_eq!(print(&m), text);
    }
}
