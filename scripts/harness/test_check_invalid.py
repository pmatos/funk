"""Tests of how check_invalid.py judges the harness's run on the fixture
corpus, on hand-written reports."""

import unittest

from check_invalid import problem

FROZEN = (
    "invalid canonical/div-frozen.fir @sdiv_frozen 7 127: fir-ref makes 1 choice"
    ' and gives 10 outcomes; native code returns ["0"]: the set holds UB'
    " (sdiv by zero), which allows any result, so the test proves nothing"
)
REJECT = (
    "passed  reject/div.toml #1: funk verify: parse-error at 3:13;"
    " fir-ref validate: parse-error at 3:13 (sdiv takes two operands of one type)"
)
ACCEPTED = (
    "passed  canonical/div-frozen.fir: funk verify: accepted;"
    " fir-ref validate: accepted"
)
NOTE = (
    "        funk verify and fir-ref validate accept 1 of the 1 modules that"
    " Rust printed: 0 from its generator and 1 from the corpus"
)
SUMMARY = "4 checks: 3 passed, 0 failed, 1 invalid"
REPORT = f"{ACCEPTED}\n{NOTE}\n{REJECT}\n{FROZEN}\n{SUMMARY}\n"


class Problem(unittest.TestCase):
    def test_the_test_invalid_for_sdiv_by_zero_passes(self):
        self.assertIsNone(problem(1, REPORT))

    def test_the_test_must_be_invalid(self):
        for status in ("passed  ", "failed  "):
            out = REPORT.replace(FROZEN, status + FROZEN.removeprefix("invalid "))
            self.assertIn(
                f"does not report canonical/div-frozen.fir @sdiv_frozen 7 127"
                f" invalid: {status}",
                problem(1, out),
            )
        self.assertIn("no line names it", problem(1, ""))

    def test_the_reason_must_name_a_zero_divisor(self):
        fuel = FROZEN.replace(
            "the set holds UB (sdiv by zero), which allows any result",
            "a path runs out of fuel",
        )
        self.assertIn("not for sdiv by zero", problem(1, REPORT.replace(FROZEN, fuel)))

    def test_every_other_check_must_pass(self):
        out = REPORT.replace(REJECT, "failed" + REJECT.removeprefix("passed"))
        self.assertIn("another check does not pass: failed  reject", problem(1, out))

    def test_the_harness_must_exit_with_1(self):
        for status in (0, 2):
            self.assertIn(f"exits with {status}, not 1", problem(status, REPORT))


if __name__ == "__main__":
    unittest.main()
