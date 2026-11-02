"""Tests of the refinement comparison (#13)."""

import unittest

from refine import (
    FAILED,
    FUEL_EXHAUSTED,
    INVALID,
    PASSED,
    RETURN,
    STUCK,
    UB,
    Outcome,
    expected,
    is_value,
    refines,
)


def ret(*values):
    return Outcome(RETURN, tuple(values))


class Refines(unittest.TestCase):
    def status(self, ref, native, types):
        return refines(ref, tuple(native), types).status

    def test_a_value_against_a_value(self):
        self.assertEqual(self.status(ret("6"), ["6"], ["i32"]), PASSED)
        self.assertEqual(self.status(ret("6"), ["7"], ["i32"]), FAILED)
        self.assertEqual(self.status(ret("true"), ["true"], ["i1"]), PASSED)
        self.assertEqual(self.status(ret("true"), ["1"], ["i1"]), FAILED)

    def test_poison_against_any_value_of_its_type(self):
        for v in ["0", "-128", "127"]:
            self.assertEqual(self.status(ret("poison"), [v], ["i8"]), PASSED, v)
        for v in ["128", "-129", "true", "01", "-0", "", "poison"]:
            self.assertEqual(self.status(ret("poison"), [v], ["i8"]), FAILED, v)
        for v in ["true", "false"]:
            self.assertEqual(self.status(ret("poison"), [v], ["i1"]), PASSED, v)

    def test_lists_of_several_values(self):
        ref = ret("2", "poison", "-1")
        types = ["i16", "i8", "i8"]
        self.assertEqual(self.status(ref, ["2", "99", "-1"], types), PASSED)
        self.assertEqual(self.status(ref, ["2", "99", "1"], types), FAILED)
        self.assertEqual(self.status(ref, ["3", "99", "-1"], types), FAILED)
        j = refines(ref, ("2", "99", "1"), types)
        self.assertIn("value 3", j.why)

    def test_lists_of_no_values(self):
        self.assertEqual(self.status(ret(), [], []), PASSED)

    def test_lists_of_different_lengths(self):
        self.assertEqual(self.status(ret("1", "2"), ["1"], ["i8", "i8"]), FAILED)
        self.assertEqual(self.status(ret("1"), ["1", "2"], ["i8"]), FAILED)
        self.assertEqual(self.status(ret(), ["0"], []), FAILED)
        self.assertEqual(self.status(ret("poison"), [], ["i8"]), FAILED)

    def test_ub_makes_a_test_invalid(self):
        ub = Outcome(UB, reason="branch on poison")
        self.assertEqual(self.status(ub, ["7"], ["i32"]), INVALID)
        self.assertEqual(self.status(ub, [], ["i32"]), INVALID)
        self.assertEqual(refines(ub, "killed by signal 8", ["i32"]).status, INVALID)

    def test_fuel_exhausted_makes_a_test_invalid(self):
        fuel = Outcome(FUEL_EXHAUSTED)
        self.assertEqual(self.status(fuel, ["7"], ["i32"]), INVALID)
        self.assertIn("fuel budget", refines(fuel, ("7",), ["i32"]).why)

    def test_stuck_is_a_failure(self):
        stuck = Outcome(STUCK, reason="a block ends without a terminator")
        self.assertEqual(self.status(stuck, ["7"], ["i32"]), FAILED)

    def test_native_code_that_fails_does_not_refine_a_return(self):
        self.assertEqual(refines(ret("1"), "exits with 2", ["i8"]).status, FAILED)
        self.assertEqual(refines(ret(), "is killed by signal 11", []).status, FAILED)


class Expected(unittest.TestCase):
    def test_values_must_be_equal(self):
        self.assertEqual(expected(ret("1", "2"), ("1", "2")).status, PASSED)
        self.assertEqual(expected(ret("1", "2"), ("1",)).status, FAILED)
        self.assertEqual(expected(ret(), ()).status, PASSED)
        self.assertEqual(expected(ret("poison"), ("poison",)).status, PASSED)
        self.assertEqual(expected(ret("poison"), ("0",)).status, FAILED)
        self.assertEqual(expected(ret("0"), ("poison",)).status, FAILED)

    def test_an_expected_ub_matches_any_reason(self):
        for reason in ["division by zero", "branch on poison", ""]:
            self.assertEqual(expected(Outcome(UB, reason=reason), UB).status, PASSED)
        self.assertEqual(expected(ret("1"), UB).status, FAILED)
        self.assertEqual(expected(Outcome(UB), ("1",)).status, FAILED)

    def test_fuel_exhausted(self):
        fuel = Outcome(FUEL_EXHAUSTED)
        self.assertEqual(expected(fuel, FUEL_EXHAUSTED).status, PASSED)
        self.assertEqual(expected(fuel, UB).status, FAILED)
        self.assertEqual(expected(ret("7"), FUEL_EXHAUSTED).status, FAILED)

    def test_stuck_never_matches(self):
        stuck = Outcome(STUCK, reason="r")
        for want in [UB, FUEL_EXHAUSTED, ("1",), ()]:
            self.assertEqual(expected(stuck, want).status, FAILED)


class IsValue(unittest.TestCase):
    def test_bounds(self):
        self.assertTrue(is_value("-64", "i7"))
        self.assertTrue(is_value("63", "i7"))
        self.assertFalse(is_value("64", "i7"))
        self.assertFalse(is_value("-65", "i7"))
        self.assertTrue(is_value("-9223372036854775808", "i64"))
        self.assertFalse(is_value("9223372036854775808", "i64"))
        self.assertTrue(is_value("0", "i16777215"))
        self.assertFalse(is_value("1" * 40, "i32"))

    def test_spelling(self):
        for bad in ["+1", "007", "-0", "1.0", " 1", "0x1", "true"]:
            self.assertFalse(is_value(bad, "i8"), bad)
        self.assertFalse(is_value("0", "ptr"))
        self.assertFalse(is_value("0", "i0"))


if __name__ == "__main__":
    unittest.main()
