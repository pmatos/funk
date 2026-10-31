"""Tests of the set rule and of declared results (#14), on hand-built sets
of outcomes and hand-built reports of `fir-ref run`."""

import unittest

from refine import FAILED, FUEL_EXHAUSTED, INVALID, PASSED, RETURN, STUCK, UB, Outcome
from sets import (
    Declared,
    Outcomes,
    Path,
    judge_declared,
    judge_set,
    problem,
    sample,
    undeclared,
    witness,
)


def ret(*values):
    return Outcome(RETURN, tuple(values))


def status(j):
    return None if j is None else j.status


class SetRule(unittest.TestCase):
    def test_a_run_with_no_choice_is_compared_exactly(self):
        one = Outcomes(0, (ret("7"),))
        self.assertEqual(judge_set(one, ("7",), ["i8"]).status, PASSED)
        j = judge_set(one, ("6",), ["i8"])
        self.assertEqual(j.status, FAILED)
        self.assertEqual(j.why, "value 1 is 6, not 7")
        poison = Outcomes(0, (ret("poison"),))
        self.assertEqual(judge_set(poison, ("-128",), ["i8"]).status, PASSED)
        self.assertEqual(judge_set(poison, ("128",), ["i8"]).status, FAILED)
        ub = Outcomes(0, (Outcome(UB, reason="r"),))
        self.assertEqual(judge_set(ub, ("7",), ["i8"]).status, INVALID)
        two = Outcomes(0, (ret("1"), ret("2")))
        self.assertEqual(judge_set(two, ("1",), ["i8"]).status, FAILED)

    def test_a_native_result_passes_when_it_is_in_the_set(self):
        s = Outcomes(1, (ret("0"), ret("2"), ret("-2")))
        for v in ["0", "2", "-2"]:
            self.assertEqual(judge_set(s, (v,), ["i8"]).status, PASSED, v)
        j = judge_set(s, ("1",), ["i8"])
        self.assertEqual(j.status, FAILED)
        self.assertIn('none of the 3 outcomes: ["0"], ["2"], ["-2"]', j.why)
        self.assertEqual(judge_set(s, "exits with 2", ["i8"]).status, FAILED)
        self.assertEqual(judge_set(s, ("0", "0"), ["i8"]).status, FAILED)

    def test_poison_in_the_set_takes_any_value_of_its_type(self):
        s = Outcomes(1, (ret("4", "poison"), ret("6", "1")))
        self.assertEqual(judge_set(s, ("4", "-128"), ["i8", "i8"]).status, PASSED)
        self.assertEqual(judge_set(s, ("6", "1"), ["i8", "i8"]).status, PASSED)
        self.assertEqual(judge_set(s, ("6", "2"), ["i8", "i8"]).status, FAILED)
        self.assertEqual(judge_set(s, ("4", "true"), ["i8", "i8"]).status, FAILED)

    def test_ub_in_a_set_makes_the_test_invalid(self):
        s = Outcomes(1, (ret("7"), Outcome(UB, reason="division by zero")))
        j = judge_set(s, ("7",), ["i8"])
        self.assertEqual(j.status, INVALID)
        self.assertIn("UB (division by zero)", j.why)
        self.assertEqual(status(problem(s.outcomes)), INVALID)

    def test_fuel_exhausted_in_a_set_makes_the_test_invalid(self):
        s = Outcomes(2, (ret("7"), Outcome(FUEL_EXHAUSTED)))
        self.assertEqual(judge_set(s, ("7",), ["i8"]).status, INVALID)

    def test_a_stuck_path_fails_the_test(self):
        s = Outcomes(1, (ret("7"), Outcome(STUCK, reason="r")))
        self.assertEqual(judge_set(s, ("7",), ["i8"]).status, FAILED)
        both = Outcomes(1, (Outcome(STUCK, reason="r"), Outcome(UB, reason="u")))
        self.assertEqual(judge_set(both, ("7",), ["i8"]).status, INVALID)

    def test_a_set_with_no_problem(self):
        self.assertIsNone(problem((ret("1"), ret("poison"))))


ZERO = Declared(("0",), ("5",))


class Declarations(unittest.TestCase):
    def test_a_witness_gives_its_result(self):
        self.assertIsNone(witness(1, ZERO, Path(ret("0"), 1)))
        self.assertIsNone(witness(1, Declared(("0",), ()), Path(ret("0"), 0)))
        j = witness(2, ZERO, Path(ret("1"), 1))
        self.assertEqual(j.status, FAILED)
        self.assertEqual(j.why, 'the witness ["5"] of result 2 gives ["1"], not ["0"]')
        self.assertEqual(status(witness(1, ZERO, Path(ret("0"), 2))), FAILED)

    def test_a_witness_that_no_longer_fits_is_never_a_pass(self):
        for misfit in [
            "the run makes 2 choices, and --choices gives 1",
            "the run makes choice 1, of type i8, and --choices gives 0 choices",
            "choice 1, 300, is not a value of type i8",
        ]:
            got = "exits with 2: fir-ref: @f: the choices do not fit the run: " + misfit
            j = witness(1, ZERO, got)
            self.assertEqual(j.status, FAILED)
            self.assertIn("does not give it", j.why)
            self.assertIn(misfit, j.why)

    def test_a_witness_that_reaches_ub_makes_the_test_invalid(self):
        j = witness(1, ZERO, Path(Outcome(UB, reason="r"), 1))
        self.assertEqual(j.status, INVALID)
        self.assertIn('the witness ["5"] of result 1 hits UB (r)', j.why)
        self.assertEqual(
            status(witness(1, ZERO, Path(Outcome(FUEL_EXHAUSTED), 1))), INVALID
        )
        stuck = Path(Outcome(STUCK, reason="r"), 1)
        self.assertEqual(status(witness(1, ZERO, stuck)), FAILED)

    def test_a_declaration_that_misses_a_possible_result(self):
        s = Outcomes(1, (ret("0"), ret("1")))
        j = undeclared(s, [ZERO])
        self.assertEqual(j.status, FAILED)
        self.assertEqual(j.why, 'the test does not declare ["1"], which the set holds')
        s3 = Outcomes(1, (ret("0"), ret("1"), ret("poison")))
        self.assertIn("does not declare 2 outcomes", undeclared(s3, [ZERO]).why)
        self.assertIsNone(undeclared(s, [ZERO, Declared(("1",), ("1",))]))
        self.assertIsNone(undeclared(Outcomes(1, (ret("0"),)), [ZERO]))

    def test_a_sampled_run_gives_a_declared_result(self):
        self.assertIsNone(sample(3, Path(ret("0"), 1, ("-7",)), [ZERO]))
        self.assertIsNone(sample(3, Path(ret("0"), 0, ()), [ZERO]))

    def test_a_sampled_result_that_the_test_does_not_declare(self):
        j = sample(3, Path(ret("2"), 1, ("-7",)), [ZERO])
        self.assertEqual(j.status, FAILED)
        self.assertEqual(
            j.why,
            'seed 3 draws ["-7"] and returns ["2"], which the test does not declare',
        )

    def test_a_sampled_ub_makes_the_test_invalid(self):
        j = sample(4, Path(Outcome(UB, reason="r"), 1, ("0",)), [ZERO])
        self.assertEqual(j.status, INVALID)
        self.assertIn('seed 4 draws ["0"] and hits UB (r)', j.why)
        fuel = Path(Outcome(FUEL_EXHAUSTED), 1, ("0",))
        self.assertEqual(status(sample(4, fuel, [ZERO])), INVALID)
        stuck = Path(Outcome(STUCK, reason="r"), 1, ("0",))
        self.assertEqual(status(sample(4, stuck, [ZERO])), FAILED)

    def test_a_sampled_run_says_what_it_drew(self):
        self.assertEqual(status(sample(1, Path(ret("0"), 1), [ZERO])), FAILED)
        self.assertEqual(status(sample(1, Path(ret("0"), 2, ("1",)), [ZERO])), FAILED)
        self.assertEqual(status(sample(1, "exits with 2", [ZERO])), FAILED)

    def test_native_code_refines_a_declared_result(self):
        both = [ZERO, Declared(("poison",), ("1",))]
        self.assertEqual(judge_declared([ZERO], ("0",), ["i64"]).status, PASSED)
        self.assertEqual(judge_declared([ZERO], ("1",), ["i64"]).status, FAILED)
        self.assertIn(
            "none of the 1 declared results",
            judge_declared([ZERO], ("1",), ["i64"]).why,
        )
        self.assertEqual(judge_declared(both, ("1",), ["i64"]).status, PASSED)
        self.assertEqual(judge_declared(both, "exits with 2", ["i64"]).status, FAILED)


if __name__ == "__main__":
    unittest.main()
