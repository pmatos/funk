"""How the harness judges native NaNs on the part of a set that fir-ref
lists when it tries a few NaNs (ADR-2026-11-16-1630), with planted
results."""

import unittest
from dataclasses import replace

import native_floats
import sets
from corpus import Test
from differential import evaluate
from refine import FAILED, INVALID, PASSED, UB, Outcome
from sets import SEEDS, BudgetExceeded, Declared, Outcomes, Path
from test_differential import RecordedRuns, returned

INF = "0x7f800000"
QUIET = "0x7fc00000"
X86 = "0xffc00000"
# The bits that native code prints for X86, read as an `i32`.
X86_NATIVE = "-4194304"
# `inf - inf`, whose result is any NaN.
NAN_TEST = Test("m.fir", "@fsub", args=(INF, INF))
F32 = ("f32",)
F32_PAIR = ("f32", "f32")
# What `--nans` with none given lists: the positive quiet NaN alone.
QUIET_ONLY = Outcomes(1, (returned(QUIET),), False)
WITH_X86 = Outcomes(1, (returned(QUIET), returned(X86)), False)


class NativeNaNs(unittest.TestCase):
    def test_a_float_that_is_a_nan_is_given_by_its_bits(self):
        self.assertEqual(
            native_floats.nans((X86, "1.0", QUIET), ("f32",) * 3), (X86, QUIET)
        )

    def test_an_integer_with_a_nan_s_bits_is_given_once(self):
        self.assertEqual(native_floats.nans((X86, X86_NATIVE), ("f32", "i32")), (X86,))
        self.assertEqual(native_floats.nans(("-1",), ("i16",)), ("0xffff",))

    def test_values_that_are_no_nan_give_none(self):
        self.assertEqual(native_floats.nans((INF, "7", "-1"), ("f32", "i32", "i8")), ())
        self.assertEqual(native_floats.nans("is killed by signal 8", F32), ())


class SetRules(unittest.TestCase):
    def test_a_result_outside_a_part_of_the_set_says_it_was_cut_short(self):
        j = sets.judge_set(QUIET_ONLY, ("1.0",), F32)
        self.assertEqual(j.status, FAILED)
        self.assertIn("cut the NaN choices short", j.why)
        whole = replace(QUIET_ONLY, complete=True)
        self.assertNotIn("short", sets.judge_set(whole, ("1.0",), F32).why)

    def test_a_part_of_the_set_needs_its_outcomes_declared_and_no_more(self):
        results = (Declared(("127",), ("0",)), Declared(("-1",), ("-1",)))
        part = Outcomes(1, (returned("127"),), False)
        self.assertIsNone(sets.undeclared(part, results))
        whole = replace(part, complete=True)
        self.assertIn(
            "which the set does not hold", sets.undeclared(whole, results).why
        )
        other = Outcomes(1, (returned("0"),), False)
        self.assertIn('does not declare ["0"]', sets.undeclared(other, results).why)


class Judged(unittest.TestCase):
    def judge(self, runs, test=NAN_TEST, types=F32):
        result = evaluate(test, types, F32_PAIR, runs)
        self.assertFalse(runs.responses, "every supplied response must be consumed")
        return result

    def test_an_allowed_native_nan_passes_once_fir_ref_tries_it(self):
        runs = RecordedRuns(QUIET_ONLY, (X86_NATIVE,), WITH_X86)
        result = self.judge(runs)
        self.assertEqual(result.judgement.status, PASSED)
        self.assertIn(f"with native code's NaNs {X86}, fir-ref makes 1", result.detail)
        self.assertEqual(
            runs.calls,
            [
                ("exhaustive", NAN_TEST.args),
                ("native", ("2139095040", "2139095040")),
                ("exhaustive", NAN_TEST.args, (X86,)),
            ],
        )

    def test_the_quiet_nan_passes_with_no_second_run(self):
        runs = RecordedRuns(QUIET_ONLY, ("2143289344",))
        self.assertEqual(self.judge(runs).judgement.status, PASSED)
        self.assertEqual(len(runs.calls), 2)

    def test_a_wrong_result_that_is_no_nan_fails(self):
        runs = RecordedRuns(QUIET_ONLY, ("1065353216",))
        j = self.judge(runs).judgement
        self.assertEqual(j.status, FAILED)
        self.assertIn('refines none of the 1 outcomes: ["0x7fc00000"]', j.why)
        self.assertIn("cut the NaN choices short", j.why)
        self.assertEqual(len(runs.calls), 2)

    def test_a_nan_where_none_is_allowed_fails_with_no_second_run(self):
        for ref in (
            Outcomes(0, (returned("1.0"),)),
            Outcomes(1, (returned("1.0"), returned("2.0"))),
        ):
            runs = RecordedRuns(ref, (X86_NATIVE,))
            j = self.judge(runs).judgement
            self.assertEqual(j.status, FAILED)
            self.assertNotIn("short", j.why)
            self.assertEqual(len(runs.calls), 2)

    def test_a_native_nan_that_no_nan_choice_gives_fails(self):
        runs = RecordedRuns(QUIET_ONLY, (X86_NATIVE,), QUIET_ONLY)
        j = self.judge(runs).judgement
        self.assertEqual(j.status, FAILED)
        self.assertIn(f"with native code's NaNs {X86}", j.why)
        self.assertIn("cut the NaN choices short", j.why)

    def test_trying_native_nans_past_the_budget_proves_nothing(self):
        runs = RecordedRuns(QUIET_ONLY, (X86_NATIVE,), BudgetExceeded(16))
        j = self.judge(runs).judgement
        self.assertEqual(j.status, INVALID)
        self.assertIn("chooses more than its budget of 16 bits", j.why)
        self.assertIn("declares its results, each with a witness", j.why)

    def test_ub_that_a_native_nan_reaches_proves_nothing(self):
        ub = Outcomes(1, (returned(QUIET), Outcome(UB, reason="r")), False)
        runs = RecordedRuns(QUIET_ONLY, (X86_NATIVE,), ub)
        j = self.judge(runs).judgement
        self.assertEqual(j.status, INVALID)
        self.assertIn("the set holds UB (r)", j.why)

    def test_each_set_of_native_nans_runs_once_over_the_stand_ins(self):
        test = replace(NAN_TEST, args=("poison", INF))
        runs = RecordedRuns(QUIET_ONLY, (X86_NATIVE,), WITH_X86, *[(X86_NATIVE,)] * 4)
        self.assertEqual(self.judge(runs, test).judgement.status, PASSED)
        reruns = [c for c in runs.calls if c[0] == "exhaustive" and len(c) == 3]
        self.assertEqual(reruns, [("exhaustive", test.args, (X86,))])


class DeclaredOnAPart(unittest.TestCase):
    """A run that computes on a NaN's bits, here its top byte, declares its
    results: the part listed must be declared, and seeds sample the rest."""

    RESULTS = (Declared(("127",), ("0",)), Declared(("-1",), ("-1",)))
    TEST = replace(NAN_TEST, results=RESULTS)
    PART = Outcomes(1, (returned("127"),), False)
    WITNESSES = (Path(returned("127"), 1), Path(returned("-1"), 1))

    def judge(self, *responses):
        runs = RecordedRuns(*responses)
        result = evaluate(self.TEST, ("i8",), F32_PAIR, runs)
        self.assertFalse(runs.responses, "every supplied response must be consumed")
        return result, runs

    def seeds(self, *drawn):
        return [Path(returned(d), 1, ("0",)) for d in drawn]

    def test_native_passes_on_a_declared_result_the_part_does_not_list(self):
        drawn = self.seeds(*["127", "-1"] * (len(SEEDS) // 2))
        result, runs = self.judge(self.PART, *self.WITNESSES, *drawn, ("-1",))
        self.assertEqual(result.judgement.status, PASSED)
        self.assertIn("each outcome listed is declared, and 32 seeded", result.detail)
        self.assertNotIn(("exhaustive", self.TEST.args, ("0xff",)), runs.calls)

    def test_a_seed_outside_the_declared_results_fails(self):
        result, _ = self.judge(
            self.PART, *self.WITNESSES, *self.seeds("127", "5"), ("-1",)
        )
        self.assertEqual(result.judgement.status, FAILED)
        self.assertIn("seed 1 draws", result.detail)

    def test_a_native_result_outside_the_declared_results_fails(self):
        drawn = self.seeds(*["127"] * len(SEEDS))
        result, _ = self.judge(self.PART, *self.WITNESSES, *drawn, ("3",))
        self.assertEqual(result.judgement.status, FAILED)
        self.assertIn("refines none of the 2 declared results", result.detail)


if __name__ == "__main__":
    unittest.main()
