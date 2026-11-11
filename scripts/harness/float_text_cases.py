"""Writes the shared cases of the text of float constants (#229).

Usage: python scripts/harness/float_text_cases.py > tests/dialects/float-text.cases

`lean/FirTest/FloatText.lean` and `crates/funk-ir/tests/float_text.rs`
read the file, so the spec's reader and printer and Rust's are checked
against `float_text.py`, which is written apart from both
(ADR-2026-11-11-1438). `test_float_text.py` checks that the committed file
is what this prints.
"""

import random
from fractions import Fraction

import float_text as ft
from float_ref import Format

HEADER = """\
Cases of the text of float constants (ADR-2026-11-11-1438), shared by
`lean/FirTest/FloatText.lean` and `crates/funk-ir/tests/float_text.rs`.
`scripts/harness/float_text_cases.py` writes this file from the
exact-rational reference `scripts/harness/float_text.py`; do not edit it.
Each line below the line `---` is one case, its words separated by spaces.
A format is written `e,m`, and bits in hexadecimal:

- `spell E,M BITS TEXT`: TEXT is the one spelling of BITS, and reads back
  as them.
- `read E,M TEXT BITS`: TEXT reads as BITS, rounded to nearest even, but is
  not their spelling, so it does not decode.
- `reject E,M TEXT`: TEXT reads as no bits of the format.
---
"""

# The formats of the spelling cases: every value of the two smallest, and
# the hard values and seeded random ones of the others.
EVERY = [(2, 1), (3, 2)]
SOME = [(5, 10), (8, 7), (8, 23), (11, 52), (15, 112), (5, 2), (2, 30), (15, 3)]
# Formats with no decimals: every value is hexadecimal bits.
NO_DECIMALS = [(16, 3), (1, 1), (3, 120)]
# The formats of the reading cases.
READ = [(5, 10), (8, 7), (8, 23), (11, 52), (15, 112), (2, 30)]
RANDOM = 6


def hard_bits(f: Format) -> list[int]:
    """Zeros, the smallest and largest subnormals, the smallest normal, one,
    the largest finite value, infinities and NaNs, of both signs."""
    top = f.top << f.m
    one = f.bias << f.m
    pos = [
        0,
        1,
        (1 << f.m) - 1,
        1 << f.m,
        one,
        one + 1,
        top - 1,
        top,
        top | 1,
        top | (1 << (f.m - 1)),
        top | ((1 << f.m) - 1),
    ]
    return pos + [b | f.sign_bit for b in pos]


def spell_lines(rng: random.Random) -> list[str]:
    out = []
    for e, m in EVERY:
        for b in range(1 << (1 + e + m)):
            out.append(f"spell {e},{m} {b:#x} {ft.spell(e, m, b)}")
    for e, m in SOME + NO_DECIMALS:
        w = 1 + e + m
        bits = (
            hard_bits(Format(e, m)) if ft.has_decimals(e, m) else [0, 1, (1 << w) - 1]
        )
        bits += [rng.getrandbits(w) for _ in range(RANDOM)]
        for b in dict.fromkeys(bits):
            out.append(f"spell {e},{m} {b:#x} {ft.spell(e, m, b)}")
    return out


def sci(x: Fraction) -> str | None:
    """`x`, a nonzero rational with a finite decimal, written with one digit
    before the point and an exponent, if it fits the reader's bounds."""
    neg = x < 0
    a = -x if neg else x
    # Too many digits for the reader's bounds, so not worth writing out.
    if a.numerator.bit_length() > 400 or a.denominator.bit_length() > 400:
        return None
    k = 0
    while a.denominator != 1:
        a *= 10
        k -= 1
    ds = str(int(a))
    exp = len(ds) - 1 + k
    frac = ds[1:].rstrip("0") or "0"
    if len(frac) > ft.MAX_DIGITS:
        return None
    return f"{'-' if neg else ''}{ds[0]}.{frac}e{exp}"


def read_lines(rng: random.Random) -> list[str]:
    """Decimals between two neighbouring floats, at their midpoint and just
    off it, and at the ends of the range: a midpoint rounds to the even
    neighbour, and the largest finite value plus half an ulp to infinity."""
    out = []
    for e, m in READ:
        f = Format(e, m)
        top = f.top << f.m
        pairs = [
            (1 << f.m, (1 << f.m) + 1),
            ((1 << f.m) + 1, (1 << f.m) + 2),
            (0, 1),
            (f.bias << f.m, (f.bias << f.m) + 1),
            (top - 2, top - 1),
        ]
        pairs += [(b, b + 1) for b in (rng.randrange(1, top - 1) for _ in range(3))]
        cands = []
        for lo, hi in pairs:
            a, b = f.decode(lo), f.decode(hi)
            x = Fraction(0) if a[0] == "zero" else a[1]
            y = b[1]
            mid = (x + y) / 2
            tiny = (y - x) / 10**6
            cands += [mid, mid + tiny, mid - tiny, -mid]
        big = f.decode(top - 1)[1]
        ulp = big - f.decode(top - 2)[1]
        cands += [big + ulp / 2, big + ulp / 2 - ulp / 10**6]
        for x in cands:
            s = sci(x)
            if s is None:
                continue
            b = ft.decode_lit(e, m, s)
            if ft.decode(e, m, s) is None:
                out.append(f"read {e},{m} {s} {b:#x}")
    return out


def reject_lines() -> list[str]:
    texts = [
        (8, 23, "1.0e10000"),
        (8, 23, "1." + "0" * 65),
        (8, 23, "1" * 65 + ".0"),
        (8, 23, "0x7fc0000"),
        (8, 23, "0x07fc00000"),
        (8, 23, "0x1ffffffff"),
        (16, 3, "1.0"),
        (1, 1, "0.0"),
        (2, 1, "0x10"),
    ]
    return [f"reject {e},{m} {s}" for e, m, s in texts]


def main() -> str:
    rng = random.Random(1438)
    lines = spell_lines(rng) + read_lines(rng) + reject_lines()
    return HEADER + "\n".join(lines) + "\n"


if __name__ == "__main__":
    print(main(), end="")
