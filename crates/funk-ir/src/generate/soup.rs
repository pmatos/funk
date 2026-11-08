//! Random texts for the parsers: tokens of fir in any order, and random
//! bytes. The Rust property tests parse them, and `fir-ref fmt` reads them
//! through the `fir_programs` example (#165).

use super::Rng;

const TOKENS: [&str; 60] = [
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
    "poison",
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
    "icmp",
    "slt",
    "uge",
    "select",
    "icmp.slt",
    "ret",
    "br",
    "cond_br",
    "^loop(",
    "^loop",
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

/// Up to 39 tokens of fir, in any order.
pub fn token_soup(rng: &mut Rng) -> String {
    let n = rng.below(40);
    let text: Vec<&str> = (0..n).map(|_| *rng.pick(&TOKENS)).collect();
    text.join(" ")
}

/// Up to 63 random bytes.
pub fn random_bytes(rng: &mut Rng) -> Vec<u8> {
    (0..rng.below(64)).map(|_| rng.next_u64() as u8).collect()
}
