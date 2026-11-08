"""Tests of the run of generated programs: its counts and `fir-ref fmt`."""

import unittest

import programs
import tools


class Share(unittest.TestCase):
    def test_too_few_runs_compared_is_a_failure(self):
        t = programs.Tally(
            compared=10, interpreter_only={"its set of outcomes holds UB": 390}
        )
        self.assertIn("10 of 400", t.too_few_compared())

    def test_enough_runs_compared_passes(self):
        t = programs.Tally(compared=300, interpreter_only={"x": 100})
        self.assertIsNone(t.too_few_compared())

    def test_a_small_replay_has_no_floor(self):
        t = programs.Tally(compared=0, interpreter_only={"x": 3})
        self.assertIsNone(t.too_few_compared())

    def test_the_counts_name_each_reason(self):
        t = programs.Tally(compared=2, planted=1, interpreter_only={"a reason": 3})
        self.assertIn("2 of 5 runs", t.show())
        self.assertIn("3: a reason", t.show())


class Fmt(unittest.TestCase):
    def test_a_text_that_parses_is_clean(self):
        self.assertIsNone(programs.fmt_problem(tools.Ran(0, "text\n", "")))

    def test_a_parse_error_at_a_position_is_clean(self):
        ran = tools.Ran(1, "", "/tmp/a.fir:3:4: parse error: unexpected token\n")
        self.assertIsNone(programs.fmt_problem(ran))

    def test_an_exit_of_1_with_no_position_is_a_failure(self):
        ran = tools.Ran(1, "", "uncaught exception: out of memory\n")
        self.assertIn("uncaught", programs.fmt_problem(ran))

    def test_a_signal_is_a_failure(self):
        self.assertIn("signal 11", programs.fmt_problem(tools.Ran(-11, "", "")))

    def test_a_timeout_is_a_failure(self):
        self.assertIn("does not end", programs.fmt_problem(tools.Ran(None, "", "")))


if __name__ == "__main__":
    unittest.main()
