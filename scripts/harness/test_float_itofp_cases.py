"""Tests of the corpus of #241's conversions from integers to floats: the
committed files of `tests/fir/canonical/` hold exactly what
`float_itofp_cases.py` writes, and each expected result is what
`float_ref.py` computes; and the reference rounds as the host does at
`f16`, `f32` and `f64`."""

import struct
import tomllib
import unittest
from fractions import Fraction

import float_itofp_cases as cases
from float_itofp_cases import CANONICAL, FORMATS
from float_ref import Format
from float_text import decode

# The host's conversion of an integer to each format, through `struct`,
# which packs a Python float, a double; and the format's bits.
HOST = {"f16": ("<e", "<H"), "f32": ("<f", "<I"), "f64": ("<d", "<Q")}


def int_value(w: int, signed: bool, text: str) -> int:
    """The integer that the argument `text` of `iW` holds, read as signed
    or as unsigned."""
    if text in ("true", "false"):
        b = 1 if text == "true" else 0
    else:
        v = int(text)
        assert -(2 ** (w - 1)) <= v < 2 ** (w - 1), text
        b = v % 2**w
    return b - 2**w if signed and b >= 2 ** (w - 1) else b


def wrong_expectations(module: str, text: str) -> list[str]:
    """The tests of a committed test file whose expected result is not the
    reference's."""
    funcs = {f"@{n}": (w, t, s) for n, _, w, t, s in cases.functions(module)}
    wrong = []
    for test in tomllib.loads(text)["tests"]:
        if "expect" not in test:
            continue
        [arg], [want] = test["args"], test["expect"]
        if arg == "poison":
            if want != "poison":
                wrong.append(f"{test}: a poison operand gives poison")
            continue
        w, t, signed = funcs[test["func"]]
        e, m = FORMATS[t]
        f = Format(e, m)
        x = int_value(w, signed, arg)
        got = f.zero() if x == 0 else f.round(Fraction(x))
        if decode(e, m, want) != got:
            wrong.append(str(test))
    return wrong


class Tests(unittest.TestCase):
    def test_the_committed_corpus_is_what_the_generator_writes(self):
        for path, text in cases.files().items():
            with self.subTest(path=path):
                committed = (CANONICAL / path).read_text(encoding="utf-8")
                self.assertEqual(committed, text)

    def test_each_expected_result_is_the_reference_s(self):
        for module in cases.FILES:
            with self.subTest(module=module):
                text = (CANONICAL / f"{module}.toml").read_text(encoding="utf-8")
                self.assertEqual(wrong_expectations(module, text), [])

    def test_a_wrong_expected_result_is_found(self):
        text = (CANONICAL / "float-sitofp-f32.toml").read_text(encoding="utf-8")
        old = '{ func = "@si_i32", args = ["16777217"], expect = ["16777216.0"] }'
        self.assertEqual(text.count(old), 1)
        planted = text.replace(old, old.replace("16777216.0", "16777218.0"))
        self.assertEqual(len(wrong_expectations("float-sitofp-f32", planted)), 1)

    def test_the_host_rounds_each_case_as_the_reference_does(self):
        """Python's `float` of an integer rounds to nearest even in binary64,
        and `struct` packs that double into `f16` and `f32` rounding to
        nearest even again, which can differ from one rounding. So the
        narrower formats are checked only on integers that binary64 holds
        exactly, which every case below 2^53 is."""
        for t, (ffmt, ifmt) in HOST.items():
            f = Format(*FORMATS[t])
            for w in (*cases.WIDTHS, *cases.ODD_WIDTHS):
                for signed in (True, False):
                    for x in cases.integers(w, signed, f):
                        if t != "f64" and abs(x) >= 2**53:
                            continue
                        with self.subTest(t=t, w=w, signed=signed, x=x):
                            try:
                                host = struct.unpack(ifmt, struct.pack(ffmt, float(x)))[
                                    0
                                ]
                            except OverflowError:
                                host = f.inf(x < 0)
                            want = f.zero() if x == 0 else f.round(Fraction(x))
                            self.assertEqual(host, want)

    def test_the_cases_reach_each_edge(self):
        f32 = Format(8, 23)
        u64 = cases.integers(64, False, f32)
        # A tie at the top of an unsigned i64, which the backend halves.
        self.assertIn(2**63 + 2**39, u64)
        self.assertIn(2**63 + 2**39 + 1, u64)
        u128 = cases.integers(128, False, f32)
        # Either side of overflow at f32, which only an unsigned i128 reaches.
        big = (2**24 - 1) * 2**104
        self.assertIn(big + 2**103 - 1, u128)
        self.assertIn(big + 2**103, u128)
        self.assertEqual(f32.round(Fraction(big + 2**103)), f32.inf())
        self.assertEqual(f32.round(Fraction(big + 2**103 - 1)), big_bits(f32))
        s128 = cases.integers(128, True, f32)
        self.assertIn(-(2**127), s128)
        f16 = Format(5, 10)
        self.assertIn(65520, cases.integers(32, True, f16))
        self.assertIn(-65520, cases.integers(32, True, f16))

    def test_every_function_has_its_cases_and_poison(self):
        for module in cases.FILES:
            text = (CANONICAL / f"{module}.toml").read_text(encoding="utf-8")
            tests = tomllib.loads(text)["tests"]
            native = module.split("-")[-1] in cases.DIFFERENTIAL
            for name, _, w, t, signed in cases.functions(module):
                n = len(cases.integers(w, signed, Format(*FORMATS[t]))) + 1
                with self.subTest(module=module, func=name):
                    mine = [x for x in tests if x["func"] == f"@{name}"]
                    self.assertEqual(len([x for x in mine if "expect" in x]), n)
                    plain = len([x for x in mine if "expect" not in x])
                    self.assertEqual(plain, n if native else 0)


def big_bits(f: Format) -> int:
    """The bits of the largest finite value of `f`."""
    return (f.top - 1) << f.m | (2**f.m - 1)


if __name__ == "__main__":
    unittest.main()
