//! A generator of random valid modules, for property tests and for the
//! cross-checks with the Lean side (#10, #13).
//!
//! The modules are valid, so they are well formed (ADR-2026-10-30-0815), and
//! every number in them is within its limit. They cover quoted symbols,
//! `true` and `false`, constants at the bounds of their widths, every kind
//! of location, and functions with zero, one and several results. The ops
//! are those of the core dialect that the registry has: `const`, `add` and
//! `ret`. The generator is deterministic: one seed gives one module.

use crate::dialects::core::{MAX_WIDTH, int_type};
use crate::ir::{Attr, Block, Func, Int, LocRef, LocTable, Location, Module, Nat, Op, Type};

/// A small, fast pseudo-random generator (SplitMix64).
#[derive(Clone, Debug)]
pub struct Rng(u64);

impl Rng {
    /// A generator from a seed.
    pub fn new(seed: u64) -> Rng {
        Rng(seed)
    }

    /// The next 64 random bits.
    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    /// A number below `n`, which must not be 0.
    pub fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }

    /// True once in `n` times.
    pub fn one_in(&mut self, n: u64) -> bool {
        self.below(n) == 0
    }

    /// One of the items, which must not be empty.
    pub fn pick<'a, T>(&mut self, items: &'a [T]) -> &'a T {
        &items[self.below(items.len() as u64) as usize]
    }
}

/// A random valid module.
pub fn module(rng: &mut Rng) -> Module {
    let locs = loc_table(rng);
    let keys: Vec<LocRef> = locs.entries.iter().map(|(r, _)| *r).collect();
    let mut m = Module {
        items: Vec::new(),
        locs,
    };
    let mut symbols: Vec<String> = Vec::new();
    for _ in 0..rng.below(4) {
        let name = fresh(rng, &symbols, symbol);
        symbols.push(name.clone());
        m = m.func(func(rng, name, &keys));
    }
    m
}

/// A table of one to eight entries in increasing order of reference, each
/// built only from entries before it.
fn loc_table(rng: &mut Rng) -> LocTable {
    let mut t = LocTable::new();
    let mut next = if rng.one_in(8) {
        u32::MAX - 20
    } else {
        rng.below(3) as u32
    };
    for _ in 0..1 + rng.below(8) {
        let earlier: Vec<LocRef> = t.entries.iter().map(|(r, _)| *r).collect();
        let loc = match (rng.below(6), earlier.is_empty()) {
            (0, _) | (3..=5, true) => Location::Unknown,
            (1, _) => range(rng),
            (2, _) => Location::Name(string(rng)),
            (3, false) => Location::CallSite {
                callee: *rng.pick(&earlier),
                caller: *rng.pick(&earlier),
            },
            (4, false) => {
                Location::Fused((0..2 + rng.below(3)).map(|_| *rng.pick(&earlier)).collect())
            }
            _ => Location::Derived(*rng.pick(&earlier)),
        };
        t.insert(LocRef(next), loc);
        match next.checked_add(1 + rng.below(3) as u32) {
            Some(n) => next = n,
            None => break,
        }
    }
    t
}

fn number(rng: &mut Rng) -> u32 {
    match rng.below(4) {
        0 => rng.below(3) as u32,
        1 => u32::MAX - rng.below(3) as u32,
        _ => rng.below(200) as u32,
    }
}

/// A well-formed source range.
fn range(rng: &mut Rng) -> Location {
    let start_line = number(rng).max(1);
    let start_col = number(rng);
    let end_line = start_line.saturating_add(if rng.one_in(2) { 0 } else { number(rng) });
    let end_col = if end_line > start_line || start_col == 0 {
        number(rng)
    } else if rng.one_in(4) {
        0
    } else {
        start_col.saturating_add(rng.below(40) as u32)
    };
    Location::Range {
        file: string(rng),
        start_line,
        start_col,
        end_line,
        end_col,
    }
}

/// Any string, often with characters that the text escapes.
fn string(rng: &mut Rng) -> String {
    const PARTS: [&str; 14] = [
        "a",
        "sum.c",
        "_",
        "1",
        " ",
        "\"",
        "\\",
        "\n",
        "\t",
        "é",
        "\u{1}",
        "\u{202e}",
        "\u{85}",
        "\u{e007f}",
    ];
    (0..rng.below(5)).map(|_| *rng.pick(&PARTS)).collect()
}

/// A symbol: a word, or a name that the text must quote.
fn symbol(rng: &mut Rng) -> String {
    if rng.one_in(3) {
        string(rng)
    } else {
        name(rng, true)
    }
}

/// A name of one or more name characters; a word when `word` is set.
fn name(rng: &mut Rng, word: bool) -> String {
    const FIRST: [&str; 5] = ["a", "x", "_", "acc", "Z"];
    const REST: [&str; 6] = ["0", "1", ".", "_", "b", "9"];
    let mut s = if word || rng.one_in(2) {
        rng.pick(&FIRST).to_string()
    } else {
        "0".into()
    };
    for _ in 0..rng.below(4) {
        s.push_str(rng.pick(&REST));
    }
    s
}

/// A value that `taken` does not hold.
fn fresh(rng: &mut Rng, taken: &[String], make: fn(&mut Rng) -> String) -> String {
    loop {
        let s = make(rng);
        if !taken.contains(&s) {
            return s;
        }
    }
}

fn width(rng: &mut Rng) -> u32 {
    match rng.below(10) {
        0 | 1 => 1,
        2 => *rng.pick(&[8, 16, 32, 64]),
        3 => 128,
        4 => 127 + rng.below(4) as u32,
        5 => 1 + rng.below(1024) as u32,
        6 => MAX_WIDTH - rng.below(2) as u32,
        _ => 1 + rng.below(70) as u32,
    }
}

/// A constant that fits `iN`, often at a bound.
fn constant(rng: &mut Rng, w: u32) -> Attr {
    if w == 1 {
        return Attr::word(if rng.one_in(2) { "true" } else { "false" });
    }
    if w > 1024 || (w > 4 && rng.one_in(3)) {
        let digits = 1 + rng.below(u64::from((w - 1) / 4).clamp(1, 30));
        let mut s: String = (0..digits)
            .map(|_| char::from(b'0' + rng.below(10) as u8))
            .collect();
        s = s.trim_start_matches('0').to_string();
        let s = if s.is_empty() {
            "0".into()
        } else if rng.one_in(2) {
            format!("-{s}")
        } else {
            s
        };
        return Attr::Int(Int::parse(&s).expect("a canonical integer"));
    }
    let k = u64::from(w - 1);
    match rng.below(4) {
        0 => Attr::Int(Int::from_nat(true, &Nat::pow2(k))),
        1 => Attr::Int(Int::from_nat(false, &Nat::ones(k))),
        _ => {
            let bits = (u128::from(rng.next_u64()) << 64) | u128::from(rng.next_u64());
            let low = if w >= 128 {
                bits
            } else {
                bits & ((1u128 << w) - 1)
            };
            let negative = rng.one_in(2);
            let magnitude = Nat::from_u128(low >> 1);
            Attr::Int(Int::from_nat(negative, &magnitude))
        }
    }
}

fn func(rng: &mut Rng, sym: String, keys: &[LocRef]) -> Func {
    let mut f = Func::new(sym);
    let mut values: Vec<(String, Type)> = Vec::new();
    let mut names: Vec<String> = Vec::new();
    for _ in 0..rng.below(4) {
        let n = fresh(rng, &names, |r| name(r, false));
        let t = int_type(width(rng));
        names.push(n.clone());
        values.push((n.clone(), t.clone()));
        f = f.param(n, t);
    }
    let results: Vec<Type> = (0..rng.below(4)).map(|_| int_type(width(rng))).collect();
    let mut block = Block::new(name(rng, false));
    let mut define = |rng: &mut Rng, block: Block, values: &mut Vec<(String, Type)>, t: Type| {
        let w = crate::dialects::core::int_width(&t).expect("an integer type");
        let n = fresh(rng, &names, |r| name(r, false));
        names.push(n.clone());
        values.push((n.clone(), t.clone()));
        let same: Vec<&String> = values
            .iter()
            .filter(|(_, u)| *u == t)
            .map(|(v, _)| v)
            .collect();
        let op = if same.len() > 1 && rng.one_in(2) {
            let (a, b) = (
                rng.pick(&same[..same.len() - 1]),
                rng.pick(&same[..same.len() - 1]),
            );
            Op::new("add", *rng.pick(keys))
                .operand(a.as_str())
                .operand(b.as_str())
        } else {
            Op::new("const", *rng.pick(keys)).attr(constant(rng, w))
        };
        (block.op(op.result(n.clone(), t)), n)
    };
    for _ in 0..rng.below(5) {
        let t = if !values.is_empty() && rng.one_in(2) {
            rng.pick(&values).1.clone()
        } else {
            int_type(width(rng))
        };
        block = define(rng, block, &mut values, t).0;
    }
    let mut ret = Op::new("ret", *rng.pick(keys));
    for t in &results {
        let have: Vec<&String> = values
            .iter()
            .filter(|(_, u)| u == t)
            .map(|(v, _)| v)
            .collect();
        let v = if !have.is_empty() && rng.one_in(2) {
            rng.pick(&have).to_string()
        } else {
            let (b, v) = define(rng, block, &mut values, t.clone());
            block = b;
            v
        };
        ret = ret.operand(v);
    }
    for t in results {
        f = f.result(t);
    }
    f.block(block.op(ret))
}
