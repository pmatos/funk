"""Writes the known-answer cases of Lean's float model (#229).

Usage: python scripts/harness/float_cases.py FORMAT
       python scripts/harness/float_cases.py tiny

With FORMAT one of f16, bf16 and f128, it prints the module
`lean/FirTest/FloatModelF16.lean`, `FloatModelBf16.lean` or
`FloatModelF128.lean`: the hard inputs at that format, each with the bit
pattern that `float_ref.py` computes for it. With `tiny`, it prints the
tables of every input at `float<2,1>` that `lean/FirTest/FloatModel.lean`
and `lean/FirTest/FloatModelFma.lean` hold. `test_float_ref.py` checks
that the committed modules hold exactly what this prints.
"""

import sys
from fractions import Fraction

import float_ref as ref
from float_ref import Format, floor_log2

FORMATS = {
    "f16": (5, 10, "`f16`, `float<5,10>`"),
    "bf16": (8, 7, "`bf16`, `float<8,7>`"),
    "f128": (15, 112, "`f128`, `float<15,112>`"),
}

NAN_OPERAND = "a NaN operand gives the canonical NaN"

SECTIONS = {
    "fadd": "Addition",
    "fsub": "Subtraction",
    "fmul": "Multiplication",
    "fdiv": "Division",
    "ffma": "Fused multiply-add",
    "fsqrt": "Square root",
    "fneg": "Negation and absolute value",
    "fabs": None,
    "fbits": "Unpacking and packing",
}

HEAD = """import FirTest.FloatModel

/-!
Known answers for Lean's float model at {title}, on the hard
inputs: ties, subnormals, `-0`, overflow to infinity and NaN operands
(#229). Each expected bit pattern was computed apart from Lean's code,
with exact rational arithmetic, and each case's comment says what the
result is. The symbols: `u` is an ulp of 1, `2^-{m}`, and `h` is `u/2`;
`s` is the smallest subnormal, `S` the largest subnormal, `n` the
smallest normal number, `M` the largest finite number, and `H` half an
ulp of `M`. A NaN result is the model's one canonical NaN. The NaN
operand "with a payload and a sign" has every bit set, and the
signalling NaN has only the lowest bit of its mantissa set.
-/

namespace FirTest.FloatModel

/-- The format these cases run at. -/
private abbrev q : Float.Model.Format := {name}
"""


def operations(f: Format) -> dict:
    """The operations of the cases, by the name the Lean module gives
    them."""
    return {
        "fadd": lambda a, b: ref.add(f, a, b),
        "fsub": lambda a, b: ref.sub(f, a, b),
        "fmul": lambda a, b: ref.mul(f, a, b),
        "fdiv": lambda a, b: ref.div(f, a, b),
        "ffma": lambda a, b, c: ref.fma(f, a, b, c),
        "fsqrt": lambda a: ref.sqrt(f, a),
        "fneg": lambda a: ref.negate(f, a),
        "fabs": lambda a: ref.fabs(f, a),
        "fbits": lambda a: ref.roundtrip(f, a),
    }


def hard_cases(f: Format) -> tuple[list, list]:
    """The hard inputs at `f`: each case is an operation, its operands and
    the result, each a value or a named special, and a label. A result
    `('r', x)` is `x` rounded to nearest, and `('s', x)` the square root of
    `x`, rounded. The second list holds the comparisons."""
    one, two = Fraction(1), Fraction(2)
    m = f.m
    u = two**-m
    h = u / 2
    s = two ** (f.emin - m)
    S = (2**m - 1) * s
    n = two**f.emin
    M = (2 ** (m + 1) - 1) * two ** (f.emax - m)
    H = two ** (f.emax - m - 1)
    cases = []

    def c(op, args, expect, label):
        cases.append((op, args, expect, label))

    c("fadd", [one, one], two, "1 + 1 = 2")
    c("fadd", [one, h], one, "1 + h is a tie: to the even 1")
    c("fadd", [one + u, h], one + 2 * u, "(1 + u) + h is a tie: to the even 1 + 2u")
    c("fadd", [one, 3 * h / 2], one + u, "1 + 3h/2 is past the tie: up to 1 + u")
    c("fadd", [one, h / 2], one, "1 + h/2 is short of the tie: down to 1")
    c("fadd", [M, M], "inf", "M + M overflows to inf")
    c("fadd", [M, H], "inf", "M + H is a tie at the top: to inf")
    c("fadd", [M, H / 2], M, "M + H/2 is short of the tie: M")
    c("fadd", [M, s], M, "M + s = M: s is far below half an ulp of M")
    c("fadd", [s, s], 2 * s, "s + s = 2s, subnormal and exact")
    c("fadd", [S, s], n, "S + s = n, from subnormal to normal")
    c("fadd", [one, -one], "0", "1 + -1 = +0")
    c("fadd", ["-0", "-0"], "-0", "-0 + -0 = -0")
    c("fadd", ["0", "-0"], "0", "+0 + -0 = +0")
    c("fadd", [-s, s], "0", "-s + s = +0")
    c("fadd", ["inf", "-inf"], "nan", "inf + -inf is NaN")
    c("fadd", ["-inf", M], "-inf", "-inf + M = -inf")
    c(
        "fadd",
        ["nanp", one],
        "nan",
        "a NaN with a payload and a sign gives the canonical NaN",
    )
    c("fadd", [one, "snan"], "nan", "a signalling NaN gives the canonical NaN")
    c("fsub", [one, one], "0", "1 - 1 = +0")
    c("fsub", ["-0", "0"], "-0", "-0 - +0 = -0")
    c("fsub", ["0", "0"], "0", "+0 - +0 = +0")
    c("fsub", [n, s], S, "n - s = S, from normal to subnormal")
    c("fsub", [one, h / 2], one, "1 - h/2 is a tie below 1: to the even 1")
    c("fsub", [-M, M], "-inf", "-M - M overflows to -inf")
    c("fsub", ["inf", "inf"], "nan", "inf - inf is NaN")
    c("fsub", ["0", "inf"], "-inf", "+0 - inf = -inf")
    c("fsub", [one, "nanp"], "nan", NAN_OPERAND)
    c("fmul", [Fraction(3, 2), Fraction(3, 2)], Fraction(9, 4), "1.5 * 1.5 = 2.25")
    c(
        "fmul",
        [one + u, one + u],
        one + 2 * u,
        "(1 + u)^2 is short of the tie: down to 1 + 2u",
    )
    c("fmul", [n, Fraction(1, 2)], n / 2, "n * 0.5 = n/2, subnormal and exact")
    c("fmul", [s, Fraction(1, 2)], "0", "s * 0.5 is a tie: to the even +0")
    c("fmul", [3 * s, Fraction(1, 2)], 2 * s, "3s * 0.5 is a tie: to the even 2s")
    c("fmul", [s, Fraction(3, 4)], s, "s * 0.75 is past the tie: up to s")
    c("fmul", [-s, Fraction(1, 4)], "-0", "-s * 0.25 underflows to -0")
    c("fmul", [M, two], "inf", "M * 2 overflows to inf")
    c("fmul", [-M, M], "-inf", "-M * M overflows to -inf")
    c("fmul", [s, s], "0", "s * s underflows far below s: to +0")
    c("fmul", [-s, S], "-0", "-s * S underflows far below s: to -0")
    c("fmul", ["-0", one], "-0", "-0 * 1 = -0")
    c("fmul", ["0", "inf"], "nan", "+0 * inf is NaN")
    c("fmul", [-one, "inf"], "-inf", "-1 * inf = -inf")
    c("fmul", ["nanp", "0"], "nan", NAN_OPERAND)
    c("fdiv", [one, Fraction(3)], ("r", Fraction(1, 3)), "1 / 3, rounded to nearest")
    c("fdiv", [one, one + u], ("r", 1 / (one + u)), "1 / (1 + u), rounded to nearest")
    c("fdiv", [one, "0"], "inf", "1 / +0 = inf")
    c("fdiv", [-one, "0"], "-inf", "-1 / +0 = -inf")
    c("fdiv", [one, "-0"], "-inf", "1 / -0 = -inf")
    c("fdiv", ["0", "0"], "nan", "0 / 0 is NaN")
    c("fdiv", ["inf", "inf"], "nan", "inf / inf is NaN")
    c("fdiv", [one, "inf"], "0", "1 / inf = +0")
    c("fdiv", [-one, "inf"], "-0", "-1 / inf = -0")
    c("fdiv", [n, two**m], s, "n / 2^m = s, exact")
    c("fdiv", [s, two], "0", "s / 2 is a tie: to the even +0")
    c("fdiv", [3 * s, two], 2 * s, "3s / 2 is a tie: to the even 2s")
    c("fdiv", [M, Fraction(1, 2)], "inf", "M / 0.5 overflows to inf")
    c("fdiv", [s, M], "0", "s / M underflows far below s: to +0")
    c("fdiv", [M, s], "inf", "M / s overflows to inf")
    c("fdiv", ["-0", one], "-0", "-0 / 1 = -0")
    c("fdiv", [one, "nanp"], "nan", NAN_OPERAND)
    c("ffma", [one, one, one], two, "1 * 1 + 1 = 2")
    c(
        "ffma",
        [one + u, one - u, -one],
        -(u * u),
        "(1 + u)(1 - u) - 1 = -u^2: one rounding, not two",
    )
    c(
        "ffma",
        [one + u, one + u, -(one + 2 * u)],
        u * u,
        "(1 + u)^2 - (1 + 2u) = u^2, exact",
    )
    c("ffma", [M, two, -M], M, "M * 2 - M = M: the product does not overflow")
    c("ffma", [one, h, one], one, "1 * h + 1 is a tie: to the even 1")
    c("ffma", [s, Fraction(1, 2), "0"], "0", "s * 0.5 + 0 is a tie: to the even +0")
    c("ffma", ["0", one, "-0"], "0", "+0 * 1 + -0 = +0")
    c("ffma", ["-0", one, "-0"], "-0", "-0 * 1 + -0 = -0")
    c("ffma", [-one, one, one], "0", "-1 * 1 + 1 = +0")
    c("ffma", ["inf", "0", "nanp"], "nan", "inf * 0 + NaN is NaN")
    c("ffma", ["inf", one, "-inf"], "nan", "inf * 1 - inf is NaN")
    c("ffma", [one, one, "inf"], "inf", "1 * 1 + inf = inf")
    c(
        "ffma",
        [s, s, -s],
        -s,
        "s * s - s = -s: the product is far below half an ulp of s",
    )
    c("ffma", [M, M, "-inf"], "-inf", "M * M - inf = -inf")
    c("fsqrt", [Fraction(4)], two, "sqrt 4 = 2")
    c("fsqrt", [Fraction(9, 4)], Fraction(3, 2), "sqrt 2.25 = 1.5")
    c("fsqrt", [two], ("s", two), "sqrt 2, rounded to nearest")
    for x, name in [(s, "s"), (2 * s, "2s")]:
        r = f.decode(ref.sqrt(f, f.exact(x)))[1]
        if r * r == x:
            c("fsqrt", [x], r, f"sqrt {name} = 2^{floor_log2(r)}, exact")
        else:
            c("fsqrt", [x], ("s", x), f"sqrt {name}, rounded to nearest")
    c("fsqrt", [M], ("s", M), "sqrt M, rounded to nearest")
    c("fsqrt", ["0"], "0", "sqrt +0 = +0")
    c("fsqrt", ["-0"], "-0", "sqrt -0 = -0")
    c("fsqrt", [-one], "nan", "sqrt -1 is NaN")
    c("fsqrt", ["inf"], "inf", "sqrt inf = inf")
    c("fsqrt", ["-inf"], "nan", "sqrt -inf is NaN")
    c("fsqrt", ["nanp"], "nan", NAN_OPERAND)
    c("fneg", ["0"], "-0", "neg +0 = -0")
    c("fneg", ["-inf"], "inf", "neg -inf = inf")
    c("fneg", [s], -s, "neg s = -s")
    c(
        "fneg",
        ["nanp"],
        "nan",
        "neg of a NaN is the canonical NaN, not the NaN with its sign flipped",
    )
    c("fabs", ["-0"], "0", "abs -0 = +0")
    c("fabs", [-M], M, "abs -M = M")
    c("fabs", ["nanp"], "nan", "abs of a NaN is the canonical NaN")
    for t, name in [
        (s, "s"),
        (S, "S"),
        (n, "n"),
        (M, "M"),
        ("-0", "-0"),
        ("-inf", "-inf"),
        (-one, "-1"),
    ]:
        c("fbits", [t], t, f"unpacking and packing {name} gives its bits back")
    c("fbits", ["nanp"], "nan", "unpacking and packing a NaN gives the canonical NaN")
    c(
        "fbits",
        ["snan"],
        "nan",
        "unpacking and packing a signalling NaN gives the canonical NaN",
    )
    comparisons = [
        ("0", "-0", "eq", "+0 and -0 are equal"),
        ("nan", "nan", None, "NaN is unordered with itself"),
        ("nanp", one, None, "NaN is unordered with 1"),
        ("-inf", s, "lt", "-inf < s"),
        (M, "inf", "lt", "M < inf"),
        (one, one + u, "lt", "1 < 1 + u"),
        (-one, -two, "gt", "-1 > -2"),
        (s, S, "lt", "s < S"),
        (-s, "0", "lt", "-s < +0"),
        ("-0", s, "lt", "-0 < s"),
        ("inf", "inf", "eq", "inf = inf"),
    ]
    return cases, comparisons


def bits_of(f: Format, t) -> int:
    """The bits of a case's value: a named special or an exact value."""
    specials = {
        "0": f.zero(),
        "-0": f.zero(True),
        "inf": f.inf(),
        "-inf": f.inf(True),
        "nan": f.nan(),
        "nanp": (1 << f.nbits) - 1,
        "snan": f.inf() | 1,
    }
    return specials[t] if isinstance(t, str) else f.exact(t)


def expected(f: Format, expect) -> int:
    """The bits that a case states as its result."""
    if isinstance(expect, tuple):
        kind, x = expect
        return f.round(x) if kind == "r" else ref.sqrt(f, f.exact(x))
    return bits_of(f, expect)


def known_answers(name: str) -> str:
    """The text of the known-answer module at the format `name`. Each
    result is computed and checked against the value its case states."""
    e, m, title = FORMATS[name]
    f = Format(e, m)
    ops = operations(f)

    def hx(b: int) -> str:
        return "0x" + format(b, f"0{f.digits}X")

    cases, comparisons = hard_cases(f)
    lines = []
    section = None
    for op, args, expect, label in cases:
        if op != section:
            section = op
            if SECTIONS[op]:
                lines += ["", f"/-! # {SECTIONS[op]} -/", ""]
        bits = [bits_of(f, a) for a in args]
        got = ops[op](*bits)
        if got != expected(f, expect):
            raise AssertionError(f"{name}: {label}: {hx(got)}")
        lines.append(f"-- {label}")
        lines.append(f"#guard {op} q {' '.join(hx(b) for b in bits)} == {hx(got)}")
    lines += ["", "/-! # Comparison -/", ""]
    for a, b, expect, label in comparisons:
        got = ref.compare(f, bits_of(f, a), bits_of(f, b))
        if got != expect:
            raise AssertionError(f"{name}: {label}: {got}")
        lines.append(f"-- {label}")
        result = "none" if got is None else f"some .{got}"
        lines.append(
            f"#guard fcmp q {hx(bits_of(f, a))} {hx(bits_of(f, b))} == {result}"
        )
    head = HEAD.format(title=title, m=m, name=name)
    return head + "\n".join(lines) + "\n\nend FirTest.FloatModel\n"


def nested(rows: list[str], tail: list[str] | None = None) -> str:
    """Rows of a Lean list of lists, one per line, closed on the last."""
    tail = tail or [""] * len(rows)
    out = []
    for i, (row, note) in enumerate(zip(rows, tail, strict=True)):
        end = "]" if i == len(rows) - 1 else ","
        out.append(f"  {row}{end}{note}")
    return "\n".join(out)


def row_text(xs) -> str:
    return "[" + ", ".join(str(x) for x in xs) + "]"


def tiny_tables() -> list[str]:
    """The tables of every input at `float<2,1>`, each as
    `lean/FirTest/FloatModel.lean` and `FloatModelFma.lean` write it."""
    f = Format(2, 1)
    ops = operations(f)
    r = range(16)
    out = []
    for op in ("fadd", "fsub", "fmul", "fdiv"):
        rows = [row_text(ops[op](a, b) for b in r) for a in r]
        out.append(f"#guard table ({op} tiny) == [\n{nested(rows)}")
    for op in ("fsqrt", "fneg", "fabs", "fbits"):
        out.append(f"#guard row ({op} tiny) == {row_text(ops[op](a) for a in r)}")
    char = {None: "u", "lt": "<", "eq": "=", "gt": ">"}
    rows = ['"' + "".join(char[ref.compare(f, a, b)] for b in r) + '"' for a in r]
    out.append(nested(rows))
    pairs = [(a, b) for a in r for b in r]
    rows = [row_text(ops["ffma"](a, b, c) for c in r) for a, b in pairs]
    notes = [f"  -- a = {a}" if b == 0 else "" for a, b in pairs]
    out.append(f"table (ffma tiny a)) == [\n{nested(rows, notes)}")
    return out


def main(argv: list[str]) -> int:
    if len(argv) != 1 or argv[0] not in [*FORMATS, "tiny"]:
        print(__doc__.split("\n\n")[1], file=sys.stderr)
        return 2
    if argv[0] == "tiny":
        print("\n\n".join(tiny_tables()))
    else:
        sys.stdout.write(known_answers(argv[0]))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
