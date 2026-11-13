"""Tests of the corpus of #241's conversions from floats to integers: the
committed files of `tests/fir/canonical/` hold exactly what
`float_fptoi_cases.py` writes, and each expected result is what
`float_ref.py` decodes, truncated; and the host truncates each case as the
reference does at `f16`, `f32` and `f64`."""

import math
import struct
import tomllib
import unittest
from fractions import Fraction

import float_fptoi_cases as cases
from float_arith_cases import CANONICAL, FORMATS, stale_files, wrong_corpus
from float_itofp_cases import ODD_WIDTHS, WIDTHS, int_text, span
from float_ref import Format
from float_text import decode

# The host's reading of each format's bits, through `struct`.
HOST = {"f16": ("<H", "<e"), "f32": ("<I", "<f"), "f64": ("<Q", "<d")}


def wrong_expectations(module: str, text: str) -> list[str]:
    """The tests of a committed test file whose expected result is not the
    reference's."""
    funcs = {f"@{n}": (t, w, s) for n, _, t, w, s in cases.functions(module)}
    wrong = []
    for test in tomllib.loads(text)["tests"]:
        if "expect" not in test:
            continue
        [arg], [want] = test["args"], test["expect"]
        if arg == "poison":
            if want != "poison":
                wrong.append(f"{test}: a poison operand gives poison")
            continue
        t, w, signed = funcs[test["func"]]
        e, m = FORMATS[t]
        b = decode(e, m, arg)
        if b is None or cases.expected(Format(e, m), w, signed, b) != want:
            wrong.append(str(test))
    return wrong


def host(t: str, w: int, signed: bool, b: int) -> str:
    """What the host's `math.trunc` gives for the bits `b` of `t` at `iW`:
    the integer when `iW` holds it, and poison otherwise."""
    ifmt, ffmt = HOST[t]
    x = struct.unpack(ffmt, struct.pack(ifmt, b))[0]
    lo, hi = span(w, signed)
    if not math.isfinite(x) or not lo <= math.trunc(x) <= hi:
        return "poison"
    return int_text(w, math.trunc(x))


class Tests(unittest.TestCase):
    def test_the_committed_corpus_is_what_the_generator_writes(self):
        self.assertEqual(stale_files(cases.files()), [])

    def test_each_expected_result_is_the_reference_s(self):
        self.assertEqual(wrong_corpus(cases.FILES, wrong_expectations), {})

    def test_a_wrong_expected_result_is_found(self):
        text = (CANONICAL / "float-fptosi-f32.toml").read_text(encoding="utf-8")
        old = '{ func = "@s_i8", args = ["-2.7"], expect = ["-2"] }'
        self.assertEqual(text.count(old), 1)
        planted = text.replace(old, old.replace('"-2"', '"-3"'))
        self.assertEqual(len(wrong_expectations("float-fptosi-f32", planted)), 1)

    def test_the_host_truncates_each_case_as_the_reference_does(self):
        for t in HOST:
            f = Format(*FORMATS[t])
            for w in (*WIDTHS, *ODD_WIDTHS):
                for signed in (True, False):
                    for b in cases.floats(f, w, signed):
                        with self.subTest(t=t, w=w, signed=signed, b=hex(b)):
                            want = cases.expected(f, w, signed, b)
                            self.assertEqual(host(t, w, signed, b), want)

    def test_the_cases_reach_each_end_of_each_range(self):
        f32 = Format(8, 23)
        s32 = cases.floats(f32, 32, True)
        # 2^31 - 128, the largest f32 in range, and 2^31, the first out.
        self.assertIn(0x4EFFFFFF, s32)
        self.assertIn(0x4F000000, s32)
        # -2^31 in range, and the next f32 below it out.
        self.assertIn(0xCF000000, s32)
        self.assertIn(0xCF000001, s32)
        self.assertEqual(cases.expected(f32, 32, True, 0xCF000000), "-2147483648")
        self.assertEqual(cases.expected(f32, 32, True, 0xCF000001), "poison")
        u8 = cases.floats(f32, 8, False)
        # -0.99999994 truncates to 0, and -1.0 is out.
        self.assertEqual(cases.expected(f32, 8, False, 0xBF7FFFFF), "0")
        self.assertEqual(cases.expected(f32, 8, False, 0xBF800000), "poison")
        self.assertIn(0xBF7FFFFF, u8)
        self.assertIn(0xBF800000, u8)
        # 2.7 truncates to 2, and -2.7 to -2.
        self.assertEqual(cases.expected(f32, 8, True, f32.round(Fraction(27, 10))), "2")
        self.assertEqual(
            cases.expected(f32, 8, True, f32.round(Fraction(-27, 10))), "-2"
        )
        # f16's largest finite value, 65504, fits i32 but not i16.
        f16 = Format(5, 10)
        self.assertEqual(cases.expected(f16, 32, True, 0x7BFF), "65504")
        self.assertEqual(cases.expected(f16, 16, True, 0x7BFF), "poison")
        # At i128, f32's largest finite value fits unsigned, not signed.
        self.assertEqual(cases.expected(f32, 128, True, 0x7F7FFFFF), "poison")
        self.assertNotEqual(cases.expected(f32, 128, False, 0x7F7FFFFF), "poison")

    def test_every_function_has_its_cases_and_poison(self):
        for module in cases.FILES:
            text = (CANONICAL / f"{module}.toml").read_text(encoding="utf-8")
            tests = tomllib.loads(text)["tests"]
            native = module.split("-")[-1] in cases.DIFFERENTIAL
            for name, _, t, w, signed in cases.functions(module):
                n = len(cases.floats(Format(*FORMATS[t]), w, signed)) + 1
                with self.subTest(module=module, func=name):
                    mine = [x for x in tests if x["func"] == f"@{name}"]
                    self.assertEqual(len([x for x in mine if "expect" in x]), n)
                    plain = len([x for x in mine if "expect" not in x])
                    self.assertEqual(plain, n if native else 0)


if __name__ == "__main__":
    unittest.main()
