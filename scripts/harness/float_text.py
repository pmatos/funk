"""The text of a float constant, exact on bits (ADR-2026-11-11-1438).

A value of `float<e,m>` has one spelling. A finite value of a format no
wider than `f128` in each field, `2 <= e <= 15` and `1 <= m <= 112`, is a
decimal: the shortest one that reads back to its bits, rounding to nearest
even at the format; of two such, the nearer to the value, and of two
equally near, the one whose last digit is even. Its digits are laid out
plainly when its decimal exponent `E` (the value is `d.ddd * 10^E`) lies in
`-4 <= E < 16`, as `1.5` or `0.0001`, and otherwise as `1.5e-7`. Zeros are
`0.0` and `-0.0`. Every other value, NaNs and infinities among them, and
every value of a wider format, is `0x` and its bits in exactly
`ceil((1 + e + m) / 4)` lowercase hexadecimal digits.

A text reads back only when it is that spelling: `decode` reads the text,
then checks that the value it gives is spelled so. Before reading a
decimal, it rejects one whose whole part or fraction has more than 64
digits, or whose exponent is 10,000 or more in magnitude, which no
spelling has, so reading never computes a huge power of ten. This module is written apart from the Lean and Rust
code, and their tests are checked against it.
"""

import re
from fractions import Fraction

from float_ref import Format, floor_log2

# The widest fields that have decimal spellings, those of `f128`.
MAX_E, MAX_M = 15, 112
# The bounds checked before reading a decimal: the digits of its whole
# part, and of its fraction, and the magnitude of its exponent.
MAX_DIGITS = 64
MAX_EXP = 9999

DECIMAL = re.compile(r"(-?)(0|[1-9][0-9]*)\.([0-9]+)(?:e(0|-?[1-9][0-9]*))?")
HEX = re.compile(r"0x([0-9a-f]+)")


def has_decimals(e: int, m: int) -> bool:
    """Whether the finite values of `float<e,m>` are spelled in decimal."""
    return 2 <= e <= MAX_E and 1 <= m <= MAX_M


def hex_digits(e: int, m: int) -> int:
    return (1 + e + m + 3) // 4


def hex_text(e: int, m: int, b: int) -> str:
    return "0x" + format(b, "x").zfill(hex_digits(e, m))


def read_decimal(f: Format, neg: bool, d: int, k: int) -> int:
    """The bits of `-1^neg * d * 10^k`, rounded to nearest even."""
    if d == 0:
        return f.zero(neg)
    x = Fraction(d) * Fraction(10) ** k
    return f.round(-x if neg else x)


def decode_lit(e: int, m: int, s: str) -> int | None:
    """The bits that the text `s` reads to at `float<e,m>`, before the
    check that `s` is their spelling."""
    h = HEX.fullmatch(s)
    if h is not None:
        v = int(h.group(1), 16)
        if len(h.group(1)) != hex_digits(e, m) or v >= 1 << (1 + e + m):
            return None
        return v
    dm = DECIMAL.fullmatch(s)
    if dm is None or not has_decimals(e, m):
        return None
    sign, whole, frac, exp = dm.groups()
    exp = int(exp or "0")
    if len(whole) > MAX_DIGITS or len(frac) > MAX_DIGITS or abs(exp) > MAX_EXP:
        return None
    return read_decimal(Format(e, m), sign == "-", int(whole + frac), exp - len(frac))


def floor_log10(a: Fraction) -> int:
    """`floor(log10 a)` for a positive `a`."""
    k = (floor_log2(a) * 30103) // 100000
    while Fraction(10) ** k > a:
        k -= 1
    while Fraction(10) ** (k + 1) <= a:
        k += 1
    return k


def shortest(f: Format, b: int, neg: bool, a: Fraction) -> tuple[int, int] | None:
    """`(d, j)` with `d * 10^j` the shortest decimal that reads back to
    `b`, whose magnitude is `a`; of two, the nearer to `a`, then the one
    with an even `d`. It tries `n = 1, 2, ...` significant digits, up to
    `m + 4`, and at each the two multiples of `10^j` around `a`."""
    top = floor_log10(a)
    for n in range(1, f.m + 5):
        j = top - n + 1
        t = a / Fraction(10) ** j
        lo = t.numerator // t.denominator
        cands = [lo] if lo == t else [lo, lo + 1]
        ok = [c for c in cands if read_decimal(f, neg, c, j) == b]
        if len(ok) == 2:
            dl, dh = t - ok[0], ok[1] - t
            ok = [ok[0]] if dl < dh or (dl == dh and ok[0] % 2 == 0) else [ok[1]]
        if ok:
            return ok[0], j
    return None


def layout(neg: bool, d: int, j: int) -> str:
    """The text of `-1^neg * d * 10^j` with `d > 0`."""
    while d % 10 == 0:
        d //= 10
        j += 1
    ds = str(d)
    exp = j + len(ds) - 1
    sign = "-" if neg else ""
    if exp < -4 or exp >= 16:
        return f"{sign}{ds[0]}.{ds[1:] or '0'}e{exp}"
    if exp < 0:
        return f"{sign}0.{'0' * (-exp - 1)}{ds}"
    whole = ds[: exp + 1].ljust(exp + 1, "0")
    return f"{sign}{whole}.{ds[exp + 1 :] or '0'}"


def decimal(e: int, m: int, b: int) -> str | None:
    """The decimal that spells `b`, if it has one."""
    if not has_decimals(e, m):
        return None
    f = Format(e, m)
    v = f.decode(b)
    if v[0] == "zero":
        return "-0.0" if v[1] else "0.0"
    if v[0] != "fin":
        return None
    x = v[1]
    found = shortest(f, b, x < 0, abs(x))
    return None if found is None else layout(x < 0, *found)


def spell(e: int, m: int, b: int) -> str:
    """The one spelling of the bits `b` of `float<e,m>`."""
    s = decimal(e, m, b)
    if s is not None and decode_lit(e, m, s) == b:
        return s
    return hex_text(e, m, b)


def decode(e: int, m: int, s: str) -> int | None:
    """The bits that `s` spells at `float<e,m>`, or None when `s` is not
    the spelling of any value of it."""
    b = decode_lit(e, m, s)
    if b is None or spell(e, m, b) != s:
        return None
    return b
