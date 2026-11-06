"""Differential judgement through its interface, with recorded tool runs."""

import unittest
from collections import deque
from dataclasses import replace

from corpus import Test
from differential import evaluate
from refine import FAILED, FUEL_EXHAUSTED, INVALID, PASSED, RETURN, STUCK, UB, Outcome
from sets import SEEDS, BudgetExceeded, Declared, Outcomes, Path


def returned(*values):
    return Outcome(RETURN, values)


ONE = Outcomes(0, (returned("7"),))
WIDE = BudgetExceeded(16)
DECLARED = Declared(("7",), ("3",))
WITNESS = Path(returned("7"), 1)
SAMPLE = Path(returned("7"), 1, ("3",))
TEST = Test("m.fir", "@f")
POISON = replace(TEST, args=("poison",))
DECLARING = replace(POISON, results=(DECLARED,))
VECTORS = [("0",), ("1",), ("-1",), ("-128",), ("127",)]


class RecordedRuns:
    """The in-memory adapter: each requested run consumes one response."""

    def __init__(self, *responses, unavailable=None):
        self.responses = deque(responses)
        self.calls = []
        self.unavailable = unavailable

    def _next(self, *call):
        self.calls.append(call)
        return self.responses.popleft()

    def exhaustive(self, args):
        return self._next("exhaustive", args)

    def scripted(self, args, choices):
        return self._next("scripted", args, choices)

    def sampled(self, args, seed):
        return self._next("sampled", args, seed)

    def native(self, args):
        return self._next("native", args)


class Differential(unittest.TestCase):
    def judge(self, runs, test=TEST, types=("i8",), params=("i8",)):
        result = evaluate(test, types, params, runs)
        self.assertFalse(runs.responses, "every supplied response must be consumed")
        return result

    def test_exact_run_returns_the_complete_explanation(self):
        runs = RecordedRuns(ONE, ("7",))
        result = self.judge(runs)
        self.assertEqual(result.judgement.status, PASSED)
        self.assertEqual(
            result.detail, 'fir-ref returns ["7"]; native code returns ["7"]'
        )
        self.assertEqual(runs.calls, [("exhaustive", ()), ("native", ())])

    def test_native_failure_is_judged_after_the_reference_run(self):
        runs = RecordedRuns(ONE, "is killed by signal 8")
        result = self.judge(runs)
        self.assertEqual(result.judgement.status, FAILED)
        self.assertIn("native code fails where fir-ref returns", result.detail)

    def test_poison_runs_every_vector_and_reports_the_first(self):
        runs = RecordedRuns(ONE, *[("7",)] * 5)
        result = self.judge(runs, POISON)
        self.assertEqual(result.judgement.status, PASSED)
        self.assertEqual(
            result.detail,
            'fir-ref returns ["7"]; native code returns ["7"] on 0, and passes'
            " on all 5 argument vectors with stand-ins for poison",
        )
        self.assertEqual(
            runs.calls,
            [("exhaustive", ("poison",))] + [("native", a) for a in VECTORS],
        )

    def test_first_failing_poison_vector_stops_without_recheck_within_budget(self):
        runs = RecordedRuns(ONE, ("7",), ("8",))
        result = self.judge(runs, POISON)
        self.assertEqual(result.judgement.status, FAILED)
        self.assertIn('returns ["8"] on 1, one of 5 argument vectors', result.detail)
        self.assertIn("value 1 is 8, not 7", result.detail)
        self.assertEqual(
            runs.calls,
            [("exhaustive", ("poison",)), ("native", ("0",)), ("native", ("1",))],
        )

    def test_reference_error_precedes_missing_types_but_still_runs_native(self):
        runs = RecordedRuns("exits with 2: broken reference", ("7",))
        result = self.judge(runs, types=None)
        self.assertEqual(result.judgement.status, FAILED)
        self.assertEqual(result.judgement.why, "")
        self.assertEqual(
            result.detail,
            'fir-ref exits with 2: broken reference; native code returns ["7"]',
        )

    def test_missing_result_types_precede_budget_and_still_show_one_vector(self):
        runs = RecordedRuns(WIDE, ("7",))
        result = self.judge(runs, POISON, types=None)
        self.assertEqual(result.judgement.status, FAILED)
        self.assertEqual(result.judgement.why, "cannot read the result types of @f")
        self.assertEqual(runs.calls[-1], ("native", ("0",)))

    def test_unbuilt_executable_is_judged_after_the_reference_run(self):
        runs = RecordedRuns(ONE, unavailable="is not built: build failed")
        result = self.judge(runs)
        self.assertEqual(result.judgement.status, FAILED)
        self.assertIn("native code is not built: build failed", result.detail)
        self.assertEqual(runs.calls, [("exhaustive", ())])

    def test_reference_ub_still_invalidates_an_unbuilt_test(self):
        runs = RecordedRuns(
            Outcomes(1, (Outcome(UB, reason="zero"),)),
            unavailable="is not built: build failed",
        )
        result = self.judge(runs)
        self.assertEqual(result.judgement.status, INVALID)
        self.assertIn("the set holds UB (zero)", result.detail)

    def test_invalid_standins_do_not_run_native(self):
        runs = RecordedRuns(ONE)
        result = self.judge(runs, POISON, params=("ptr",))
        self.assertEqual(result.judgement.status, FAILED)
        self.assertIn("ptr has no stand-in", result.detail)
        self.assertEqual(runs.calls, [("exhaustive", ("poison",))])

    def test_budget_verdict_precedes_invalid_standins(self):
        runs = RecordedRuns(WIDE)
        result = self.judge(runs, POISON, params=None)
        self.assertEqual(result.judgement.status, INVALID)
        self.assertIn("cannot read the parameter types", result.detail)
        self.assertIn("declares its results, each with a witness", result.detail)

    def test_no_choice_ub_keeps_its_distinct_explanation(self):
        runs = RecordedRuns(Outcomes(0, (Outcome(UB),)), ("7",))
        result = self.judge(runs, POISON)
        self.assertEqual(result.judgement.status, INVALID)
        self.assertIn("UB allows any result", result.detail)
        self.assertNotIn("the set holds UB", result.detail)
        self.assertNotIn("one of", result.detail)

    def test_declared_results_use_witnesses_before_native_but_no_samples_within_budget(
        self,
    ):
        test = replace(TEST, results=(DECLARED,))
        runs = RecordedRuns(ONE, WITNESS, ("7",))
        result = self.judge(runs, test)
        self.assertEqual(result.judgement.status, PASSED)
        self.assertIn("each witness gives its result, and the set is", result.detail)
        self.assertEqual(
            runs.calls,
            [("exhaustive", ()), ("scripted", (), ("3",)), ("native", ())],
        )

    def test_declared_set_problem_precedes_witnesses_and_uses_one_vector(self):
        ref = Outcomes(1, (Outcome(UB), Outcome(STUCK)))
        runs = RecordedRuns(ref, "is killed by signal 8")
        result = self.judge(runs, DECLARING)
        self.assertEqual(result.judgement.status, FAILED)
        self.assertEqual(result.judgement.why, "no run of a valid module is stuck")
        self.assertEqual(runs.calls, [("exhaustive", ("poison",)), ("native", ("0",))])

    def test_first_bad_witness_stops_declaration_checks(self):
        test = replace(DECLARING, results=(DECLARED, Declared(("8",), ("4",))))
        runs = RecordedRuns(WIDE, "exits with 2: misfit", ("7",))
        result = self.judge(runs, test)
        self.assertEqual(result.judgement.status, FAILED)
        self.assertIn("misfit", result.detail)
        self.assertEqual(
            runs.calls,
            [
                ("exhaustive", ("poison",)),
                ("scripted", ("poison",), ("3",)),
                ("native", ("0",)),
            ],
        )

    def test_witnesses_precede_the_exact_set_comparison(self):
        ref = Outcomes(1, (returned("7"), returned("8")))
        runs = RecordedRuns(ref, WITNESS, ("7",))
        result = self.judge(runs, replace(TEST, results=(DECLARED,)))
        self.assertEqual(result.judgement.status, FAILED)
        self.assertIn('does not declare ["8"]', result.detail)
        self.assertEqual(runs.calls[1], ("scripted", (), ("3",)))

    def test_first_bad_sample_stops_before_native_evidence(self):
        runs = RecordedRuns(WIDE, WITNESS, SAMPLE, "exits with 2", ("7",))
        result = self.judge(runs, DECLARING)
        self.assertEqual(result.judgement.status, FAILED)
        self.assertIn("seed 1: fir-ref exits with 2", result.detail)
        self.assertEqual(
            runs.calls,
            [
                ("exhaustive", ("poison",)),
                ("scripted", ("poison",), ("3",)),
                ("sampled", ("poison",), 0),
                ("sampled", ("poison",), 1),
                ("native", ("0",)),
            ],
        )

    def test_past_budget_checks_all_seeds_then_every_native_vector(self):
        runs = RecordedRuns(WIDE, WITNESS, *[SAMPLE] * len(SEEDS), *[("7",)] * 5)
        result = self.judge(runs, DECLARING)
        self.assertEqual(result.judgement.status, PASSED)
        self.assertIn("32 seeded runs give declared results", result.detail)
        self.assertEqual(
            runs.calls,
            [("exhaustive", ("poison",)), ("scripted", ("poison",), ("3",))]
            + [("sampled", ("poison",), seed) for seed in SEEDS]
            + [("native", args) for args in VECTORS],
        )

    def test_only_a_failing_poison_vector_past_budget_is_rechecked(self):
        runs = RecordedRuns(WIDE, WITNESS, *[SAMPLE] * len(SEEDS), ("7",), ("8",), ONE)
        result = self.judge(runs, DECLARING)
        self.assertEqual(result.judgement.status, FAILED)
        self.assertIn('on 1, fir-ref returns ["7"]', result.detail)
        self.assertEqual(
            runs.calls[-3:],
            [("native", ("0",)), ("native", ("1",)), ("exhaustive", ("1",))],
        )

    def test_recheck_fuel_invalidates_the_test(self):
        runs = RecordedRuns(
            WIDE,
            WITNESS,
            *[SAMPLE] * len(SEEDS),
            ("8",),
            Outcomes(0, (Outcome(FUEL_EXHAUSTED),)),
        )
        result = self.judge(runs, DECLARING)
        self.assertEqual(result.judgement.status, INVALID)
        self.assertIn("on 0, fir-ref runs out of fuel", result.detail)

    def test_seeded_recheck_collects_all_seeds_and_prioritizes_ub_over_fuel(self):
        rechecked = [
            Path(Outcome(FUEL_EXHAUSTED), 0),
            "exits with 2: ignored during recheck",
            Path(Outcome(STUCK), 0),
            Path(Outcome(UB, reason="hidden"), 0),
        ] + [SAMPLE] * (len(SEEDS) - 4)
        runs = RecordedRuns(
            WIDE, WITNESS, *[SAMPLE] * len(SEEDS), ("8",), WIDE, *rechecked
        )
        result = self.judge(runs, DECLARING)
        self.assertEqual(result.judgement.status, INVALID)
        self.assertIn("on 0, fir-ref --seed 3 hits UB (hidden)", result.detail)
        self.assertEqual(
            runs.calls[-len(SEEDS) :],
            [("sampled", ("0",), seed) for seed in SEEDS],
        )

    def test_recheck_stuck_preserves_the_original_failure(self):
        runs = RecordedRuns(
            WIDE,
            WITNESS,
            *[SAMPLE] * len(SEEDS),
            ("8",),
            Outcomes(0, (Outcome(STUCK, reason="bad path"),)),
        )
        result = self.judge(runs, DECLARING)
        self.assertEqual(result.judgement.status, FAILED)
        self.assertIn("refines none of the 1 declared results", result.detail)
        self.assertIn("is stuck (bad path)", result.detail)

    def test_no_poison_failure_is_never_rechecked(self):
        runs = RecordedRuns(WIDE, WITNESS, *[SAMPLE] * len(SEEDS), ("8",))
        result = self.judge(runs, replace(TEST, results=(DECLARED,)))
        self.assertEqual(result.judgement.status, FAILED)
        self.assertEqual(runs.calls[-1], ("native", ()))

    def test_tool_start_errors_propagate_to_the_corpus_runner(self):
        class CannotStart(RecordedRuns):
            def exhaustive(self, args):
                raise OSError("cannot start fir-ref")

        with self.assertRaisesRegex(OSError, "cannot start fir-ref"):
            evaluate(TEST, ("i8",), (), CannotStart())


if __name__ == "__main__":
    unittest.main()
