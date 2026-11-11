"""An exact-rational reference for IEEE 754 arithmetic at any format
`float<e,m>`, rounding to nearest even (#229).

It is the reference that computed the expected bit patterns of Lean's float
model in `lean/FirTest/FloatModel*.lean`, written apart from Lean's code. A
finite operand is the rational number it encodes, as a `Fraction`. A finite
nonzero result `x` is rounded at the quantum `q = 2^(k - m)`, where `k` is
the larger of `floor(log2 |x|)` and the smallest normal exponent: `x/q` goes
to the nearest integer, a tie to the even one, and a result whose magnitude
reaches `2^(emax + 1)` is an infinity. A square root takes the integer
square root of `x/q^2` and compares `x/q^2` with the square of the
midpoint. The special cases (zeros and their signs, infinities, NaNs)
follow IEEE 754 sections 6 and 7. Every NaN result is the canonical NaN of
Lean's model: the positive quiet NaN whose mantissa has only its top bit
set.

Bit patterns are Python integers. `float_cases.py` writes the Lean cases
from this module, and `test_float_ref.py` checks it against the host's
binary16, binary32 and binary64 arithmetic.
"""

from fractions import Fraction

TWO = Fraction(2)

# The kinds of two factors whose product is NaN: an infinity and a zero.
INF_TIMES_ZERO = (("inf", "zero"), ("zero", "inf"))


class Format:
    """The format `float<e,m>`: `e` exponent bits and `m` explicit mantissa
    bits, with at least 2 of the first and 1 of the second, as Lean's model
    requires."""

    def __init__(self, e: int, m: int):
        if e < 2 or m < 1:
            raise ValueError(f"float<{e},{m}> needs e >= 2 and m >= 1")
        self.e, self.m = e, m
        self.bias = 2 ** (e - 1) - 1
        self.emin = 1 - self.bias
        self.emax = self.bias
        self.nbits = 1 + e + m
        self.digits = (self.nbits + 3) // 4
        self.sign_bit = 1 << (self.nbits - 1)
        self.top = 2**e - 1

    def nan(self) -> int:
        """The canonical NaN."""
        return (self.top << self.m) | (1 << (self.m - 1))

    def inf(self, neg: bool = False) -> int:
        return (self.sign_bit if neg else 0) | (self.top << self.m)

    def zero(self, neg: bool = False) -> int:
        return self.sign_bit if neg else 0

    def decode(self, b: int):
        """What the bit pattern `b` encodes: `('nan',)`, `('inf', neg)`,
        `('zero', neg)` or `('fin', x)` with `x` a nonzero `Fraction`."""
        neg = bool(b & self.sign_bit)
        ex = (b >> self.m) & self.top
        man = b & (2**self.m - 1)
        if ex == self.top:
            return ("nan",) if man else ("inf", neg)
        if ex == 0:
            if man == 0:
                return ("zero", neg)
            v = man * TWO ** (self.emin - self.m)
        else:
            v = (2**self.m + man) * TWO ** (ex - self.bias - self.m)
        return ("fin", -v if neg else v)

    def round(self, x: Fraction) -> int:
        """The bits of the nonzero `x`, rounded to nearest even."""
        neg = x < 0
        a = -x if neg else x
        q = TWO ** (max(floor_log2(a), self.emin) - self.m)
        return self.finish(nearest_even(a / q) * q, neg)

    def finish(self, v: Fraction, neg: bool) -> int:
        """The bits of the rounded magnitude `v`: an infinity once it
        reaches `2^(emax + 1)`."""
        if v >= TWO ** (self.emax + 1):
            return self.inf(neg)
        return self.encode(v, neg)

    def encode(self, v: Fraction, neg: bool) -> int:
        """The bits of the magnitude `v`, which the format holds exactly."""
        s = self.zero(neg)
        if v == 0:
            return s
        if v < TWO**self.emin:
            man = v / TWO ** (self.emin - self.m)
            assert man.denominator == 1, v
            return s | int(man)
        k = floor_log2(v)
        man = v / TWO ** (k - self.m)
        assert man.denominator == 1 and 2**self.m <= man < 2 ** (self.m + 1), v
        return s | ((k + self.bias) << self.m) | (int(man) - 2**self.m)

    def exact(self, v: Fraction) -> int:
        """The bits of a value that the format holds exactly."""
        b = self.round(v)
        assert self.decode(b) == ("fin", v), v
        return b


def floor_log2(a: Fraction) -> int:
    """`floor(log2 a)` for a positive `a`."""
    k = a.numerator.bit_length() - a.denominator.bit_length()
    while TWO**k > a:
        k -= 1
    while TWO ** (k + 1) <= a:
        k += 1
    return k


def nearest_even(t: Fraction) -> int:
    """The integer nearest `t >= 0`, a tie to the even one."""
    n = t.numerator // t.denominator
    r = t - n
    if r > Fraction(1, 2) or (r == Fraction(1, 2) and n % 2 == 1):
        n += 1
    return n


def isqrt(n: int) -> int:
    """`floor(sqrt n)` for `n >= 0`."""
    if n == 0:
        return 0
    x = 1 << ((n.bit_length() + 1) // 2)
    while True:
        y = (x + n // x) // 2
        if y >= x:
            return x
        x = y


def negated(d):
    """The decoded value `d` with its sign flipped."""
    if d[0] in ("inf", "zero"):
        return (d[0], not d[1])
    if d[0] == "fin":
        return ("fin", -d[1])
    return d


def sign_of(d) -> bool:
    return d[1] if d[0] in ("inf", "zero") else d[1] < 0


def value_of(d) -> Fraction:
    """The rational value of a decoded zero or finite number."""
    return d[1] if d[0] == "fin" else Fraction(0)


def add(f: Format, a: int, b: int, negate_b: bool = False) -> int:
    """`a + b`, or `a - b` with `negate_b`."""
    da, db = f.decode(a), f.decode(b)
    if negate_b:
        db = negated(db)
    if da[0] == "nan" or db[0] == "nan":
        return f.nan()
    if da[0] == "inf" and db[0] == "inf":
        return f.inf(da[1]) if da[1] == db[1] else f.nan()
    if da[0] == "inf":
        return f.inf(da[1])
    if db[0] == "inf":
        return f.inf(db[1])
    if da[0] == "zero" and db[0] == "zero":
        return f.zero(da[1] and db[1])
    s = value_of(da) + value_of(db)
    return f.zero() if s == 0 else f.round(s)


def sub(f: Format, a: int, b: int) -> int:
    return add(f, a, b, negate_b=True)


def mul(f: Format, a: int, b: int) -> int:
    da, db = f.decode(a), f.decode(b)
    if da[0] == "nan" or db[0] == "nan":
        return f.nan()
    s = sign_of(da) != sign_of(db)
    if (da[0], db[0]) in INF_TIMES_ZERO:
        return f.nan()
    if "inf" in (da[0], db[0]):
        return f.inf(s)
    if "zero" in (da[0], db[0]):
        return f.zero(s)
    return f.round(da[1] * db[1])


def div(f: Format, a: int, b: int) -> int:
    da, db = f.decode(a), f.decode(b)
    if da[0] == "nan" or db[0] == "nan":
        return f.nan()
    s = sign_of(da) != sign_of(db)
    if da[0] == db[0] and da[0] in ("inf", "zero"):
        return f.nan()
    if da[0] == "inf" or db[0] == "zero":
        return f.inf(s)
    if da[0] == "zero" or db[0] == "inf":
        return f.zero(s)
    return f.round(da[1] / db[1])


def fma(f: Format, a: int, b: int, c: int) -> int:
    """`a * b + c`, with one rounding."""
    da, db, dc = f.decode(a), f.decode(b), f.decode(c)
    if "nan" in (da[0], db[0], dc[0]):
        return f.nan()
    if (da[0], db[0]) in INF_TIMES_ZERO:
        return f.nan()
    ps = sign_of(da) != sign_of(db)
    if "inf" in (da[0], db[0]):
        if dc[0] == "inf" and dc[1] != ps:
            return f.nan()
        return f.inf(ps)
    if dc[0] == "inf":
        return f.inf(dc[1])
    p = value_of(da) * value_of(db)
    if p == 0 and dc[0] == "zero":
        return f.zero(ps and dc[1])
    s = p + value_of(dc)
    return f.zero() if s == 0 else f.round(s)


def sqrt(f: Format, a: int) -> int:
    d = f.decode(a)
    if d[0] == "nan":
        return f.nan()
    if d[0] == "zero":
        return f.zero(d[1])
    if d[0] == "inf":
        return f.nan() if d[1] else f.inf()
    x = d[1]
    if x < 0:
        return f.nan()
    q = TWO ** (max(floor_log2(x) // 2, f.emin) - f.m)
    t = x / (q * q)
    n = isqrt(t.numerator // t.denominator)
    half = (n + Fraction(1, 2)) ** 2
    if t > half or (t == half and n % 2 == 1):
        n += 1
    return f.finish(n * q, False)


def negate(f: Format, a: int) -> int:
    """`-a`; a NaN gives the canonical NaN, as in Lean's model."""
    return f.nan() if f.decode(a)[0] == "nan" else a ^ f.sign_bit


def fabs(f: Format, a: int) -> int:
    """`|a|`; a NaN gives the canonical NaN, as in Lean's model."""
    return f.nan() if f.decode(a)[0] == "nan" else a & ~f.sign_bit


def roundtrip(f: Format, a: int) -> int:
    """`a` unpacked and packed again: its bits, unless it is a NaN."""
    return f.nan() if f.decode(a)[0] == "nan" else a


def compare(f: Format, a: int, b: int):
    """`'lt'`, `'eq'` or `'gt'`, or `None` when `a` and `b` are
    unordered."""
    da, db = f.decode(a), f.decode(b)
    if da[0] == "nan" or db[0] == "nan":
        return None

    def key(d):
        if d[0] == "inf":
            return (-1 if d[1] else 1, 0)
        return (0, value_of(d))

    ka, kb = key(da), key(db)
    if ka < kb:
        return "lt"
    if ka > kb:
        return "gt"
    return "eq"
