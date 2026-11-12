"""The hard inputs of `frem` and `fmod` (#310), and the known answers of
fir's remainder in Lean.

Usage: python scripts/harness/float_rem_cases.py

It prints the module `lean/FirTest/FloatRem.lean`: fir's remainder,
`Fir.Core.remainder` in `lean/Fir/Core/FloatRem.lean`, on the hard inputs
below at `f16`, `bf16`, `f64` and `f128`, and on every input at
`float<2,1>`, each with the bit pattern that `float_ref.py` computes for
it. `test_float_rem_cases.py` checks that the committed module holds
exactly what this prints. `float_arith_cases.py` writes the corpus of the two ops
from the same hard inputs.

`frem` is IEEE 754's remainder: `x - n * y` with `n` the quotient `x / y`
rounded to the nearest integer, a tie to the even one. `fmod` is C's
`fmod`, with `n` truncated toward zero. Each result is exact.
"""

import sys
from fractions import Fraction

import float_ref as ref
from float_cases import NAN_OPERAND, bits_of, expected, nested, row_text
from float_ref import Format

FORMATS = {
    "f16": (5, 10, "f16"),
    "bf16": (8, 7, "bf16"),
    "f64": (11, 52, ".binary64"),
    "f128": (15, 112, "f128"),
}

OPS = {"frem": ref.remainder, "fmod": ref.fmod}


def hard_cases(f: Format) -> list:
    """The hard inputs of `frem` and `fmod` at `f`, as
    `float_cases.hard_cases` gives its own: an op, its operands, its
    result and a label. `s` is the smallest subnormal, `S` the largest,
    `n` the smallest normal number, `M` the largest finite number and
    `P` the largest power of two."""
    one, two = Fraction(1), Fraction(2)
    m = f.m
    s = two ** (f.emin - m)
    S = (2**m - 1) * s
    n = two**f.emin
    M = (2 ** (m + 1) - 1) * two ** (f.emax - m)
    P = two**f.emax
    # The quotient P / 3s is 2^k, and 2^k mod 3 is 1 or 2.
    k = f.emax - f.emin + m
    cases = []

    def c(op, args, expect, label):
        cases.append((op, args, expect, label))

    x, y = Fraction(11, 2), two
    c("frem", [x, y], Fraction(-1, 2), "5.5 frem 2 = -0.5: the quotient 2.75 goes to 3")
    c("frem", [-x, y], Fraction(1, 2), "-5.5 frem 2 = 0.5")
    c("frem", [x, -y], Fraction(-1, 2), "5.5 frem -2 = -0.5: y's sign does not matter")
    c("frem", [Fraction(3), y], -one, "3 frem 2 = -1: the tie 1.5 goes to the even 2")
    c("frem", [Fraction(5), y], one, "5 frem 2 = 1: the tie 2.5 goes to the even 2")
    c("frem", [one, Fraction(3)], one, "1 frem 3 = 1: the quotient goes to 0")
    c("frem", [two, Fraction(3)], -one, "2 frem 3 = -1: the quotient goes to 1")
    c("frem", [Fraction(4), y], "0", "4 frem 2 = +0")
    c("frem", [Fraction(-4), y], "-0", "-4 frem 2 = -0: a zero has x's sign")
    c("frem", [M, s], "0", "M frem s = +0: M is a multiple of s")
    c("frem", [P, 3 * s], s if 2**k % 3 == 1 else -s, "P frem 3s: x and y far apart")
    c("frem", [S, 2 * s], -s, "S frem 2s = -s: a tie to the even quotient")
    c("frem", [n, 3 * s], s if 2**m % 3 == 1 else -s, "n frem 3s, subnormal")
    c("frem", [one, "inf"], one, "1 frem inf = 1")
    c("frem", ["-0", "inf"], "-0", "-0 frem inf = -0")
    c("frem", ["-0", one], "-0", "-0 frem 1 = -0")
    c("frem", [one, "0"], "nan", "1 frem +0 is NaN")
    c("frem", ["inf", one], "nan", "inf frem 1 is NaN")
    c("frem", ["inf", "inf"], "nan", "inf frem inf is NaN")
    c("frem", ["0", "0"], "nan", "+0 frem +0 is NaN")
    c("frem", ["nanp", one], "nan", NAN_OPERAND)
    c("frem", [one, "snan"], "nan", "a signalling NaN gives the canonical NaN")
    c("fmod", [x, y], Fraction(3, 2), "5.5 fmod 2 = 1.5: the quotient 2.75 goes to 2")
    c("fmod", [-x, y], Fraction(-3, 2), "-5.5 fmod 2 = -1.5")
    c("fmod", [x, -y], Fraction(3, 2), "5.5 fmod -2 = 1.5: y's sign does not matter")
    c("fmod", [Fraction(3), y], one, "3 fmod 2 = 1")
    c("fmod", [Fraction(-4), y], "-0", "-4 fmod 2 = -0: a zero has x's sign")
    c("fmod", [one, Fraction(3)], one, "1 fmod 3 = 1")
    c("fmod", [-M, s], "-0", "-M fmod s = -0")
    c("fmod", [P, 3 * s], (2**k % 3) * s, "P fmod 3s: x and y far apart")
    c(
        "fmod",
        [M, M - two ** (f.emax - m)],
        two ** (f.emax - m),
        "M fmod (M - ulp M) = ulp M",
    )
    c("fmod", [n, 3 * s], (2**m % 3) * s, "n fmod 3s, subnormal")
    c("fmod", [M, "-inf"], M, "M fmod -inf = M")
    c("fmod", ["0", one], "0", "+0 fmod 1 = +0")
    c("fmod", [one, "-0"], "nan", "1 fmod -0 is NaN")
    c("fmod", ["-inf", one], "nan", "-inf fmod 1 is NaN")
    c("fmod", ["nanp", "inf"], "nan", NAN_OPERAND)
    return cases


HEAD = """import FirTest.FloatModel
import Fir.Core.FloatRem

/-!
Known answers for fir's remainder (#310), `Fir.Core.remainder`, which
`frem` and `fmod` compute on Lean's float model: on the hard inputs at
`f16`, `bf16`, `f64` and `f128`, and on every input at `float<2,1>`.
Each expected bit pattern was computed apart from Lean's code, with exact
rational arithmetic, by `scripts/harness/float_ref.py`, and
`scripts/harness/float_rem_cases.py` writes this module. The symbols:
`s` is the smallest subnormal, `S` the largest subnormal, `n` the
smallest normal number, `M` the largest finite number and `P` the
largest power of two. A NaN result is the model's one canonical NaN.
-/

namespace FirTest.FloatModel

open Float.Model

/-- `a frem b` in format `f`: IEEE 754's remainder. -/
def frem (f : Format) (a b : Nat) : Nat := pk f (Fir.Core.remainder true f (un f a) (un f b))

/-- `a fmod b` in format `f`: C's `fmod`. -/
def fmod (f : Format) (a b : Nat) : Nat := pk f (Fir.Core.remainder false f (un f a) (un f b))
"""


def known_answers() -> str:
    """The text of `lean/FirTest/FloatRem.lean`. Each result is computed
    and checked against the value its case states."""
    lines = []
    for name, (e, m, lean) in FORMATS.items():
        f = Format(e, m)

        def hx(b: int, f: Format = f) -> str:
            return "0x" + format(b, f"0{f.digits}X")

        lines += ["", f"/-! # At `{name}` -/", ""]
        for op, args, expect, label in hard_cases(f):
            bits = [bits_of(f, a) for a in args]
            got = OPS[op](f, *bits)
            if got != expected(f, expect):
                raise AssertionError(f"{name}: {label}: {hx(got)}")
            lines.append(f"-- {label}")
            lines.append(
                f"#guard {op} {lean} {' '.join(hx(b) for b in bits)} == {hx(got)}"
            )
    lines += ["", "/-! # Every input at `float<2,1>` -/", ""]
    tiny = Format(2, 1)
    for op, fn in OPS.items():
        rows = [row_text(fn(tiny, a, b) for b in range(16)) for a in range(16)]
        lines.append(f"#guard table ({op} tiny) == [\n{nested(rows)}")
    return HEAD + "\n".join(lines) + "\n\nend FirTest.FloatModel\n"


def main(argv: list[str]) -> int:
    if argv:
        print(__doc__.split("\n\n")[1], file=sys.stderr)
        return 2
    sys.stdout.write(known_answers())
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
