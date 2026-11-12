"""Tests of the hard inputs of `frem` and `fmod` (#310): the committed
`lean/FirTest/FloatRem.lean` holds exactly what `float_rem_cases.py`
prints, and each case's stated result is the reference's."""

import unittest
from fractions import Fraction
from pathlib import Path

import float_ref as ref
import float_rem_cases as cases
from float_cases import bits_of, expected
from float_ref import Format

LEAN = Path(__file__).resolve().parents[2] / "lean" / "FirTest" / "FloatRem.lean"


class Tests(unittest.TestCase):
    def test_the_lean_module_is_what_the_generator_prints(self):
        self.assertEqual(cases.known_answers(), LEAN.read_text(encoding="utf-8"))

    def test_each_case_states_the_reference_s_result_at_every_format(self):
        for e, m in [(5, 10), (8, 7), (8, 23), (11, 52), (15, 112)]:
            f = Format(e, m)
            for op, args, expect, label in cases.hard_cases(f):
                with self.subTest(f"float<{e},{m}>: {label}"):
                    bits = [bits_of(f, a) for a in args]
                    self.assertEqual(cases.OPS[op](f, *bits), expected(f, expect))

    def test_the_issue_s_example(self):
        f = Format(11, 52)
        x, y = f.exact(Fraction(11, 2)), f.exact(Fraction(2))
        self.assertEqual(f.decode(ref.remainder(f, x, y)), ("fin", Fraction(-1, 2)))
        self.assertEqual(f.decode(ref.fmod(f, x, y)), ("fin", Fraction(3, 2)))


if __name__ == "__main__":
    unittest.main()
