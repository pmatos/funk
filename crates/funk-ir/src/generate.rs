//! A generator of random valid modules, for property tests and for the
//! cross-checks with the Lean side (#10, #13).
//!
//! The modules are valid, so they are well formed (ADR-2026-10-30-0815), and
//! every number in them is within its limit. They cover quoted symbols,
//! `true` and `false`, constants at the bounds of their widths, every kind
//! of location, and functions with zero, one and several results. The ops
//! are those of the core dialect that the registry has: `const`, `add`,
//! `sub` and `mul` with each combination of their flags, `freeze`, `sdiv`
//! and `udiv` with and without `exact`, `srem`, `urem` and `ret`. A division
//! may be by zero: that is UB when it runs, not invalid, and no check runs
//! these modules.
//! The generator is deterministic: one seed gives one module.

use crate::dialects::core::{DIVISION_OPS, MAX_WIDTH, WRAP_FLAG_SETS, int_type};
use crate::ir::{Attr, Block, Func, Int, LocRef, LocTable, Location, Module, Nat, Op, Type};

/// How many modules, from seed 0, the round-trip checks generate: the Rust
/// property tests and the cross-language round trip with Lean.
pub const ROUND_TRIP_MODULES: u64 = 600;

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
        let name = loop {
            let s = symbol(rng);
            if !symbols.contains(&s) {
                break s;
            }
        };
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

/// The values of a function so far, and the ops of its block that define
/// them.
struct Body<'k> {
    keys: &'k [LocRef],
    values: Vec<(String, Type)>,
    ops: Vec<Op>,
}

impl Body<'_> {
    /// The names of the values of type `t`.
    fn of_type(&self, t: &Type) -> Vec<String> {
        let same = self.values.iter().filter(|(_, u)| u == t);
        same.map(|(v, _)| v.clone()).collect()
    }

    /// A value name that the function does not define yet.
    fn fresh_name(&self, rng: &mut Rng) -> String {
        loop {
            let n = name(rng, false);
            if self.values.iter().all(|(v, _)| *v != n) {
                return n;
            }
        }
    }

    /// Defines a new value of type `t` and returns its name: `add`, `sub`
    /// or `mul` of two earlier values of that type, with any of their flags,
    /// a division or remainder of two, `freeze` of one, or a constant.
    fn define(&mut self, rng: &mut Rng, t: Type) -> String {
        let same = self.of_type(&t);
        let loc = *rng.pick(self.keys);
        let op = if !same.is_empty() && rng.one_in(5) {
            let (name, exact) = *rng.pick(&DIVISION_OPS);
            let op = Op::new(name, loc);
            let op = if exact && rng.one_in(2) {
                op.attr(Attr::word("exact"))
            } else {
                op
            };
            op.operand(rng.pick(&same).as_str())
                .operand(rng.pick(&same).as_str())
        } else if !same.is_empty() && rng.one_in(2) {
            match rng.below(4) {
                0 => Op::new("freeze", loc).operand(rng.pick(&same).as_str()),
                k => {
                    let name = ["add", "sub", "mul"][k as usize - 1];
                    let flags = rng.pick(&WRAP_FLAG_SETS);
                    let op = flags
                        .iter()
                        .fold(Op::new(name, loc), |op, f| op.attr(Attr::word(*f)));
                    op.operand(rng.pick(&same).as_str())
                        .operand(rng.pick(&same).as_str())
                }
            }
        } else {
            let w = crate::dialects::core::int_width(&t).expect("an integer type");
            Op::new("const", loc).attr(constant(rng, w))
        };
        let n = self.fresh_name(rng);
        self.ops.push(op.result(n.clone(), t.clone()));
        self.values.push((n.clone(), t));
        n
    }
}

fn func(rng: &mut Rng, sym: String, keys: &[LocRef]) -> Func {
    let mut f = Func::new(sym);
    let mut body = Body {
        keys,
        values: Vec::new(),
        ops: Vec::new(),
    };
    for _ in 0..rng.below(4) {
        let (n, t) = (body.fresh_name(rng), int_type(width(rng)));
        body.values.push((n.clone(), t.clone()));
        f = f.param(n, t);
    }
    for _ in 0..rng.below(5) {
        let t = if !body.values.is_empty() && rng.one_in(2) {
            rng.pick(&body.values).1.clone()
        } else {
            int_type(width(rng))
        };
        body.define(rng, t);
    }
    let mut ret = Op::new("ret", *rng.pick(keys));
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
    let mut block = Block::new(name(rng, false));
    block.ops = body.ops;
    f.block(block.op(ret))
}
