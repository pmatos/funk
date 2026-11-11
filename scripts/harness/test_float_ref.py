"""Tests of the exact-rational float reference and of the Lean cases that it
writes (#229): the committed modules of `lean/FirTest/` hold exactly what
`float_cases.py` prints, and the reference agrees with the host's binary16,
binary32 and binary64 arithmetic on special values and seeded random
inputs."""

import math
import os
import random
import struct
import unittest
from fractions import Fraction

import float_cases
import float_ref as ref
from float_ref import Format

ROOT = os.path.normpath(os.path.join(os.path.dirname(__file__), "..", ".."))
LEAN = os.path.join(ROOT, "lean", "FirTest")
MODULES = {
    "f16": "FloatModelF16.lean",
    "bf16": "FloatModelBf16.lean",
    "f128": "FloatModelF128.lean",
}

# The host's formats: the struct code of each and its float<e,m>.
HOST = {"e": Format(5, 10), "f": Format(8, 23), "d": Format(11, 52)}
UINT = {"e": "<H", "f": "<I", "d": "<Q"}


def read(name: str) -> str:
    with open(os.path.join(LEAN, name), encoding="utf-8") as f:
        return f.read()


def to_host(code: str, b: int) -> float:
    return struct.unpack("<" + code, struct.pack(UINT[code], b))[0]


def from_host(code: str, x: float) -> int:
    """The bits of `x` rounded to the format `code`, with any NaN read as
    the canonical NaN. Rounding a binary64 result once more is exact for
    `+`, `-`, `*`, `/` and the square root at binary32 and binary16, since
    binary64 has more than twice their precision plus two bits."""
    f = HOST[code]
    if math.isnan(x):
        return f.nan()
    try:
        packed = struct.pack("<" + code, x)
    except OverflowError:
        return f.inf(x < 0)
    return struct.unpack(UINT[code], packed)[0]


def host_op(code: str, op: str, *bits: int):
    """The host's result of `op`, or `None` where Python raises instead of
    giving the IEEE 754 result, as for a division by zero."""
    xs = [to_host(code, b) for b in bits]
    try:
        x = {
            "add": lambda: xs[0] + xs[1],
            "sub": lambda: xs[0] - xs[1],
            "mul": lambda: xs[0] * xs[1],
            "div": lambda: xs[0] / xs[1],
            "sqrt": lambda: math.sqrt(xs[0]),
            "fma": lambda: math.fma(*xs),
        }[op]()
    except (ZeroDivisionError, ValueError, OverflowError):
        return None
    return from_host(code, x)


def canonical(f: Format, b: int) -> int:
    return ref.roundtrip(f, b)


def inputs(f: Format, count: int, seed: int) -> list[int]:
    """Special values of `f` and `count` random bit patterns."""
    rng = random.Random(seed)
    one = f.exact(Fraction(1))
    special = [
        f.zero(),
        f.zero(True),
        1,
        (1 << f.m) - 1,
        1 << f.m,
        (1 << f.m) | 1,
        one,
        one | 1,
        one | f.sign_bit,
        f.exact(Fraction(3)),
        f.inf() - 1,
        f.inf(),
        f.inf(True),
        f.nan(),
        (1 << f.nbits) - 1,
    ]
    return special + [rng.getrandbits(f.nbits) for _ in range(count)]


class GeneratedCases(unittest.TestCase):
    def test_the_known_answer_modules_are_what_the_generator_prints(self):
        for name, module in MODULES.items():
            with self.subTest(name):
                self.assertEqual(float_cases.known_answers(name), read(module))

    def test_the_tiny_tables_are_what_the_generator_prints(self):
        src = read("FloatModel.lean") + read("FloatModelFma.lean")
        for table in float_cases.tiny_tables():
            with self.subTest(table.splitlines()[0]):
                self.assertIn(table, src)

    def test_a_case_whose_result_disagrees_with_its_statement_fails(self):
        f = Format(5, 10)
        self.assertEqual(float_cases.expected(f, ("r", Fraction(1, 3))), 0x3555)
        self.assertNotEqual(
            float_cases.expected(f, Fraction(1)), ref.add(f, 0x3C00, 0x3C00)
        )


class Reference(unittest.TestCase):
    def test_formats_below_the_model_s_bounds_are_refused(self):
        Format(2, 1)
        for e, m in [(1, 1), (2, 0), (0, 5)]:
            with self.assertRaises(ValueError):
                Format(e, m)

    def test_the_smallest_format_reads_as_documented(self):
        f = Format(2, 1)
        values = [f.decode(b) for b in range(8)]
        self.assertEqual(
            values,
            [
                ("zero", False),
                ("fin", Fraction(1, 2)),
                ("fin", Fraction(1)),
                ("fin", Fraction(3, 2)),
                ("fin", Fraction(2)),
                ("fin", Fraction(3)),
                ("inf", False),
                ("nan",),
            ],
        )
        self.assertEqual(f.nan(), 7)

    def test_the_canonical_nan_is_the_positive_quiet_nan(self):
        self.assertEqual(Format(8, 23).nan(), 0x7FC00000)
        self.assertEqual(Format(11, 52).nan(), 0x7FF8000000000000)

    def test_a_tie_goes_to_the_even_neighbour(self):
        f = Format(8, 23)
        one = f.exact(Fraction(1))
        half_ulp = f.exact(Fraction(1, 2**24))
        self.assertEqual(ref.add(f, one, half_ulp), one)
        self.assertEqual(ref.add(f, one + 1, half_ulp), one + 2)


class AgainstTheHost(unittest.TestCase):
    def check(self, code: str, count: int, seed: int):
        f = HOST[code]
        xs = inputs(f, count, seed)
        for a in xs:
            self.compare(code, "sqrt", ref.sqrt(f, a), a)
            for b in xs[:40]:
                self.compare(code, "add", ref.add(f, a, b), a, b)
                self.compare(code, "sub", ref.sub(f, a, b), a, b)
                self.compare(code, "mul", ref.mul(f, a, b), a, b)
                self.compare(code, "div", ref.div(f, a, b), a, b)

    def compare(self, code: str, op: str, got: int, *bits: int):
        want = host_op(code, op, *bits)
        if want is not None:
            self.assertEqual(
                got, canonical(HOST[code], want), (code, op, [hex(b) for b in bits])
            )

    def test_binary16(self):
        self.check("e", 200, 1)

    def test_binary32(self):
        self.check("f", 200, 2)

    def test_binary64(self):
        self.check("d", 120, 3)

    @unittest.skipUnless(hasattr(math, "fma"), "math.fma needs Python 3.13")
    def test_binary64_fma(self):
        f = HOST["d"]
        xs = inputs(f, 25, 4)
        for a in xs:
            for b in xs:
                for c in xs[:20]:
                    self.compare("d", "fma", ref.fma(f, a, b, c), a, b, c)


if __name__ == "__main__":
    unittest.main()
