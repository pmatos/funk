"""Tests of the corpus of #229's float arithmetic: the committed files of
`tests/fir/canonical/` hold exactly what `float_arith_cases.py` writes, and
each expected result is what `float_ref.py` computes."""

import tomllib
import unittest

import float_arith_cases as cases
import float_ref as ref
from float_arith_cases import CANONICAL, FORMATS, nan_bits
from float_ref import Format
from float_text import decode


def wrong_expectations(t: str, text: str) -> list[str]:
    """The tests of a committed test file at the type `t` whose expected
    result is not the reference's: for a result that is not a NaN, its
    bits, and for a NaN, the NaN that the test's choice names."""
    e, m = FORMATS[t]
    f = Format(e, m)
    wrong = []
    for test in tomllib.loads(text)["tests"]:
        if "expect" not in test:
            continue
        [want] = test["expect"]
        if "poison" in test["args"]:
            if want != "poison":
                wrong.append(f"{test}: a poison operand gives poison")
            continue
        bits = [decode(e, m, a) for a in test["args"]]
        got = cases.result(f, test["func"][1:], bits)
        if "choices" in test:
            [c] = test["choices"]
            ok = cases.is_nan(f, got) and decode(e, m, want) == nan_bits(f, int(c))
        else:
            ok = not cases.is_nan(f, got) and decode(e, m, want) == got
        if not ok:
            wrong.append(str(test))
    return wrong


class Tests(unittest.TestCase):
    def test_the_committed_corpus_is_what_the_generator_writes(self):
        for path, text in cases.files().items():
            with self.subTest(path=path):
                committed = (CANONICAL / path).read_text(encoding="utf-8")
                self.assertEqual(committed, text)

    def test_each_expected_result_is_the_reference_s(self):
        for name in cases.MODULES:
            for t in FORMATS:
                path = CANONICAL / f"{name}-{t}.toml"
                with self.subTest(path=path.name):
                    text = path.read_text(encoding="utf-8")
                    self.assertEqual(wrong_expectations(t, text), [])

    def test_a_wrong_expected_result_is_found(self):
        text = (CANONICAL / "float-binary-f32.toml").read_text(encoding="utf-8")
        old = '{ func = "@fadd", args = ["1.0", "1.0"], expect = ["2.0"] }'
        self.assertEqual(text.count(old), 1)
        planted = text.replace(old, old.replace('"2.0"', '"2.0000002"'))
        self.assertEqual(len(wrong_expectations("f32", planted)), 1)
        nan = 'choices = ["0"], expect = ["0x7fc00000"]'
        self.assertIn(nan, text)
        planted = text.replace(nan, 'choices = ["0"], expect = ["0xffc00000"]', 1)
        self.assertEqual(len(wrong_expectations("f32", planted)), 1)

    def test_every_case_is_tested_in_every_way_it_can_be(self):
        f = Format(8, 23)
        text = (CANONICAL / "float-binary-f32.toml").read_text(encoding="utf-8")
        tests = tomllib.loads(text)["tests"]
        differential = [t for t in tests if "expect" not in t]
        nans = [t for t in tests if "choices" in t]
        self.assertTrue(nans)
        for t in tests:
            bits = [decode(8, 23, a) for a in t["args"] if a != "poison"]
            if "expect" in t and "choices" not in t and "poison" not in t["args"]:
                plain = {k: v for k, v in t.items() if k != "expect"}
                self.assertIn(plain, differential)
            if "choices" in t:
                self.assertTrue(cases.is_nan(f, cases.result(f, t["func"][1:], bits)))

    def test_a_choice_names_a_nan_as_the_spec_s_nan_bits_does(self):
        f32 = Format(8, 23)
        # The checks of `nanBits` in `lean/Fir/Core/FloatArith.lean`.
        self.assertEqual(nan_bits(f32, 0), 0x7FC00000)
        self.assertEqual(nan_bits(f32, 0x800000), 0xFFC00000)
        self.assertEqual(nan_bits(f32, 1), 0x7F800001)
        self.assertEqual(nan_bits(f32, -1), 0xFFFFFFFF)
        tiny = Format(2, 1)
        self.assertEqual([nan_bits(tiny, c) for c in range(4)], [7, 7, 15, 15])
        for e, m in FORMATS.values():
            f = Format(e, m)
            for c in cases.NAN_CHOICES:
                self.assertTrue(cases.is_nan(f, nan_bits(f, c)))
            self.assertEqual(ref.Format(e, m).nan(), nan_bits(f, 0))


if __name__ == "__main__":
    unittest.main()
