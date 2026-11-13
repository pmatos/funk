"""Tests of the corpus of #241's bit casts: the committed files of
`tests/fir/canonical/` hold exactly what `float_bitcast_cases.py` writes,
and each expected result has its operand's bits, read apart from the
generator with `float_text.decode`; and the host's `struct` reads each edge
at `f16`, `f32` and `f64` as `float_ref.py` does."""

import math
import struct
import tomllib
import unittest
from fractions import Fraction

import float_bitcast_cases as cases
from float_arith_cases import CANONICAL
from float_bitcast_cases import FORMATS
from float_text import decode

# The host's own reading of a float's bits, by `struct`.
HOST = {"f16": ("<e", "<H"), "f32": ("<f", "<I"), "f64": ("<d", "<Q")}


def bits_of_int(n: int, s: str) -> int:
    """The bits of `iN` that the signed integer `s` writes."""
    v = int(s)
    assert -(2 ** (n - 1)) <= v < 2 ** (n - 1), s
    return v % 2**n


def wrong_expectations(t: str, text: str) -> list[str]:
    """The tests of a committed test file at the type `t` whose expected
    result does not have its operand's bits."""
    e, m = FORMATS[t]
    n = 1 + e + m
    wrong = []
    for test in tomllib.loads(text)["tests"]:
        if "expect" not in test:
            continue
        [arg], [want] = test["args"], test["expect"]
        if arg == "poison":
            if want != "poison":
                wrong.append(f"{test}: a poison operand gives poison")
            continue
        if test["func"] == "@to_bits":
            float_text, int_text = arg, want
        else:
            int_text, float_text = arg, want
        if decode(e, m, float_text) != bits_of_int(n, int_text):
            wrong.append(str(test))
    return wrong


class Tests(unittest.TestCase):
    def test_the_committed_corpus_is_what_the_generator_writes(self):
        for path, text in cases.files().items():
            with self.subTest(path=path):
                committed = (CANONICAL / path).read_text(encoding="utf-8")
                self.assertEqual(committed, text)

    def test_each_expected_result_has_its_operand_s_bits(self):
        for t in FORMATS:
            path = CANONICAL / f"float-bitcast-{t}.toml"
            with self.subTest(path=path.name):
                text = path.read_text(encoding="utf-8")
                self.assertEqual(wrong_expectations(t, text), [])

    def test_a_wrong_expected_result_is_found(self):
        text = (CANONICAL / "float-bitcast-f32.toml").read_text(encoding="utf-8")
        old = '{ func = "@to_bits", args = ["1.0"], expect = ["1065353216"] }'
        self.assertEqual(text.count(old), 1)
        planted = text.replace(old, old.replace("1065353216", "1065353217"))
        self.assertEqual(len(wrong_expectations("f32", planted)), 1)

    def test_the_host_reads_each_edge_as_the_reference_does(self):
        """The host's `struct` reads each edge as `float_ref.py` does: the
        same number, infinity or zero with its sign, or a NaN. Python reads
        a float through a double, which may quiet a signalling NaN, so a
        NaN's bits are not compared here: the native tests compare them."""
        for t, (ffmt, ifmt) in HOST.items():
            e, m = FORMATS[t]
            f = cases.Format(e, m)
            for b in cases.edges(f):
                with self.subTest(t=t, bits=hex(b)):
                    x = struct.unpack(ffmt, struct.pack(ifmt, b))[0]
                    kind = f.decode(b)
                    if kind == ("nan",):
                        self.assertTrue(math.isnan(x))
                    elif kind[0] == "fin":
                        self.assertEqual(Fraction(x), kind[1])
                    else:
                        self.assertEqual(math.copysign(1, x), -1 if kind[1] else 1)
                        self.assertEqual(x == 0, kind[0] == "zero")
                        self.assertEqual(math.isinf(x), kind[0] == "inf")
                    self.assertEqual(decode(e, m, cases.spell(e, m, b)), b)

    def test_every_case_runs_both_ways_and_differentially_where_lowered(self):
        for t in FORMATS:
            e, m = FORMATS[t]
            text = (CANONICAL / f"float-bitcast-{t}.toml").read_text(encoding="utf-8")
            tests = tomllib.loads(text)["tests"]
            n = len(cases.edges(cases.Format(e, m)))
            with self.subTest(t=t):
                for func in ("@to_bits", "@of_bits"):
                    checked = [x for x in tests if x["func"] == func and "expect" in x]
                    self.assertEqual(len(checked), n + 1)
                    plain = [
                        x for x in tests if x["func"] == func and "expect" not in x
                    ]
                    want = n + 1 if t in cases.DIFFERENTIAL else 0
                    self.assertEqual(len(plain), want)

    def test_the_edges_are_each_kind_of_float(self):
        f = cases.Format(8, 23)
        self.assertEqual(
            cases.edges(f),
            [
                0x0000_0000,
                0x8000_0000,
                0x0000_0001,
                0x8000_0001,
                0x007F_FFFF,
                0x0080_0000,
                0x3F80_0000,
                0xBF80_0000,
                0x7F7F_FFFF,
                0xFF7F_FFFF,
                0x7F80_0000,
                0xFF80_0000,
                0x7FC0_0000,
                0xFFC0_0001,
                0x7F80_0001,
                0xFFFF_FFFF,
            ],
        )


if __name__ == "__main__":
    unittest.main()
