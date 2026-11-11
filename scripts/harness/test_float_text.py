"""Tests of the text of float constants (ADR-2026-11-11-1438): the
exact-rational reference of `float_text.py` against the host's binary64,
which Python reads and writes exactly, the shortest spellings of small
formats against every decimal of fewer digits, the cases that
`float_text_cases.py` commits for the Lean and Rust tests, and the
conversion of floats at the boundary with native code."""

import math
import os
import random
import struct
import unittest
from fractions import Fraction

import float_text as ft
import float_text_cases
import native_floats
from float_ref import Format

ROOT = os.path.normpath(os.path.join(os.path.dirname(__file__), "..", ".."))
CASES = os.path.join(ROOT, "tests", "dialects", "float-text.cases")


def bits64(x: float) -> int:
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def python_spelling(x: float) -> str:
    """Python's shortest decimal of `x`, laid out as a float constant."""
    r = repr(x)
    if "e" not in r:
        return r
    mantissa, exp = r.split("e")
    if "." not in mantissa:
        mantissa += ".0"
    return f"{mantissa}e{int(exp)}"


class HostBinary64(unittest.TestCase):
    def test_spellings_are_pythons_shortest_decimals(self):
        rng = random.Random(1438)
        specials = [0, 1 << 63, 1, 0x000F_FFFF_FFFF_FFFF, 0x3FF0_0000_0000_0000]
        for b in specials + [rng.getrandbits(64) for _ in range(400)]:
            x = struct.unpack("<d", struct.pack("<Q", b))[0]
            s = ft.spell(11, 52, b)
            if math.isnan(x) or math.isinf(x):
                self.assertEqual(s, f"0x{b:016x}")
            else:
                self.assertEqual(s, python_spelling(x), hex(b))
            self.assertEqual(ft.decode(11, 52, s), b, s)

    def test_reading_is_exact_as_pythons(self):
        rng = random.Random(229)
        for _ in range(400):
            digits = "".join(
                rng.choice("0123456789") for _ in range(rng.randint(1, 30))
            )
            whole = digits.lstrip("0") or "0"
            exp = rng.randint(-340, 320)
            text = f"{whole}.0e{exp}"
            want = bits64(float(text))
            self.assertEqual(ft.decode_lit(11, 52, text), want, text)

    def test_a_midpoint_rounds_to_the_even_neighbour(self):
        # 1 + 2^-53 lies halfway between 1.0 and its successor.
        mid = Fraction(1) + Fraction(1, 2**53)
        text = float_text_cases.sci(mid)
        self.assertEqual(ft.decode_lit(11, 52, text), 0x3FF0_0000_0000_0000)
        self.assertIsNone(ft.decode(11, 52, text))


class SmallFormats(unittest.TestCase):
    def test_no_decimal_with_fewer_digits_reads_back(self):
        for e, m in ((2, 1), (3, 2)):
            f = Format(e, m)
            for b in range(1 << (1 + e + m)):
                s = ft.spell(e, m, b)
                self.assertEqual(ft.decode(e, m, s), b, s)
                if s.startswith("0x") or s.endswith("0.0"):
                    continue
                n = len(s.split("e")[0].replace("-", "").replace(".", "").strip("0"))
                neg = s.startswith("-")
                for k in range(1, n):
                    for j in range(-6, 4):
                        for d in range(10 ** (k - 1), 10**k):
                            self.assertNotEqual(
                                ft.read_decimal(f, neg, d, j), b, (s, d, j)
                            )


class SharedCases(unittest.TestCase):
    def test_the_committed_cases_are_what_the_generator_writes(self):
        with open(CASES, encoding="utf-8") as fh:
            self.assertEqual(fh.read(), float_text_cases.main())

    def test_only_spellings_decode(self):
        self.assertEqual(ft.decode(8, 23, "1.0"), 0x3F80_0000)
        self.assertEqual(ft.decode(8, 23, "0x7fc00000"), 0x7FC0_0000)
        for bad in ("1.00", "1.0e0", "0x3f800000", "0x7fc0000", "1.0e39", "1065353216"):
            self.assertIsNone(ft.decode(8, 23, bad), bad)
        self.assertEqual(ft.spell(16, 3, 0), "0x00000")
        self.assertIsNone(ft.decode(16, 3, "0.0"))


class NativeBoundary(unittest.TestCase):
    def test_floats_pass_as_their_bits_and_come_back_spelled(self):
        args = ("1.0", "-0.0", "poison", "7", "0x7fc00001")
        params = ("f32", "f64", "f32", "i8", "f32")
        native = native_floats.to_native(args, params)
        self.assertEqual(
            native, ("1065353216", "-9223372036854775808", "poison", "7", "2143289345")
        )
        back = native_floats.from_native(
            native[:2] + native[3:], params[:2] + params[3:]
        )
        self.assertEqual(back, ("1.0", "-0.0", "7", "0x7fc00001"))

    def test_anything_else_passes_as_it_is(self):
        self.assertEqual(native_floats.to_native(("1.0",), None), ("1.0",))
        self.assertEqual(native_floats.to_native(("1.00",), ("f32",)), ("1.00",))
        self.assertEqual(native_floats.from_native("failed", ("f32",)), "failed")
        self.assertEqual(native_floats.from_native(("1", "2"), ("f32",)), ("1", "2"))


if __name__ == "__main__":
    unittest.main()
