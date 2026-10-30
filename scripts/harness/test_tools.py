"""Tests of how the harness reads what funk, fir-ref and native code print."""

import unittest

from refine import FUEL_EXHAUSTED, RETURN, STUCK, UB, Outcome
from tools import Ran, Verdict, build_failure, native_values, outcome, verdict


class FirRefRun(unittest.TestCase):
    def test_results(self):
        cases = [
            (
                '{"kind":"return","values":["6","poison"]}',
                Outcome(RETURN, ("6", "poison")),
            ),
            ('{"kind":"return","values":[]}', Outcome(RETURN, ())),
            ('{"kind":"ub","reason":"why"}', Outcome(UB, reason="why")),
            ('{"kind":"fuel-exhausted"}', Outcome(FUEL_EXHAUSTED)),
        ]
        for out, want in cases:
            self.assertEqual(outcome(Ran(0, out + "\n", "")), want)
        stuck = '{"kind":"stuck","reason":"no terminator"}\n'
        self.assertEqual(
            outcome(Ran(1, stuck, "")), Outcome(STUCK, reason="no terminator")
        )

    def test_errors_are_not_results(self):
        no_rules = "fir-ref: @f: sub has no execution rules yet\n"
        self.assertEqual(
            outcome(Ran(2, "", no_rules)),
            "exits with 2: fir-ref: @f: sub has no execution rules yet",
        )
        self.assertIsInstance(outcome(Ran(1, "", "f.fir:1:1: parse error: x\n")), str)
        self.assertIsInstance(outcome(Ran(-11, "", "")), str)
        self.assertIsInstance(outcome(Ran(None, "", "")), str)

    def test_a_status_that_does_not_fit_the_result_is_an_error(self):
        self.assertIsInstance(
            outcome(Ran(1, '{"kind":"return","values":[]}\n', "")), str
        )
        self.assertIsInstance(
            outcome(Ran(0, '{"kind":"stuck","reason":"r"}\n', "")), str
        )
        self.assertIsInstance(
            outcome(Ran(0, '{"kind":"return","values":[1]}\n', "")), str
        )
        self.assertIsInstance(outcome(Ran(0, '{"kind":"maybe"}\n', "")), str)
        self.assertIsInstance(outcome(Ran(0, "{}\n{}\n", "")), str)


class Native(unittest.TestCase):
    def test_values(self):
        self.assertEqual(
            native_values(Ran(0, '{"values":["1","true"]}\n', "")), ("1", "true")
        )
        self.assertEqual(native_values(Ran(0, '{"values":[]}\n', "")), ())

    def test_failures(self):
        self.assertEqual(
            native_values(Ran(2, "", "exe: 128 is not a value of type i8\n")),
            "exits with 2: exe: 128 is not a value of type i8",
        )
        self.assertEqual(native_values(Ran(-8, "", "")), "is killed by signal 8")
        self.assertIsInstance(native_values(Ran(0, "", "")), str)
        self.assertIsInstance(native_values(Ran(0, '{"values":[1]}\n', "")), str)
        self.assertIsInstance(
            native_values(Ran(0, '{"values":[]}\n', "warning\n")), str
        )


class Verdicts(unittest.TestCase):
    def report(self, verdict_, diags="[]"):
        return f'{{"file":"f.fir","verdict":"{verdict_}","diagnostics":{diags}}}\n'

    def test_verdicts(self):
        self.assertEqual(
            verdict(Ran(0, self.report("accepted"), "")), Verdict("accepted")
        )
        d = '[{"kind":"validation-error","message":"m","func":"f"}]'
        got = verdict(Ran(1, self.report("validation-error", d), ""))
        self.assertEqual(got, Verdict("validation-error", message="m"))

    def test_a_parse_error_has_its_position(self):
        d = '[{"kind":"parse-error","message":"m","line":3,"column":7}]'
        got = verdict(Ran(1, self.report("parse-error", d), ""))
        self.assertEqual(got, Verdict("parse-error", (3, 7), "m"))
        d = '[{"kind":"parse-error","message":"m"}]'
        self.assertIsInstance(verdict(Ran(1, self.report("parse-error", d), "")), str)

    def test_no_report_is_an_error(self):
        self.assertIsInstance(verdict(Ran(-6, "", "abort\n")), str)
        self.assertIsInstance(verdict(Ran(1, self.report("rejected"), "")), str)

    def test_the_status_fits_the_verdict(self):
        d = '[{"kind":"parse-error","message":"m","line":3,"column":7}]'
        for status, report, want in [
            (1, self.report("accepted"), "exits with 1 but reports accepted"),
            (2, self.report("accepted"), "exits with 2 but reports accepted"),
            (0, self.report("parse-error", d), "exits with 0 but reports parse-error"),
            (
                0,
                self.report("validation-error"),
                "exits with 0 but reports validation-error",
            ),
            (1, self.report("io-error"), "exits with 1 but reports io-error"),
        ]:
            self.assertEqual(verdict(Ran(status, report, "")), want)


class NoReport(unittest.TestCase):
    def test_the_failure_shows_what_the_tool_printed(self):
        for out, shown in [
            ("", "prints nothing"),
            ("not json\n", "prints not json"),
            ("{}\n{}\n", "prints 2 lines, the first {}"),
        ]:
            want = f"exits with 0 and {shown}, not one JSON report"
            self.assertEqual(verdict(Ran(0, out, "")), want)
            self.assertEqual(outcome(Ran(0, out, "")), want)
            self.assertEqual(native_values(Ran(0, out, "")), want)
            self.assertEqual(build_failure(Ran(0, out, "")), want)
        self.assertEqual(
            verdict(Ran(1, "", "f.fir: cannot read\n")),
            "exits with 1 and prints nothing, not one JSON report: f.fir: cannot read",
        )


class Build(unittest.TestCase):
    def test_build(self):
        paths = '"object":"o","executable":"e"'
        ok = f'{{"file":"f","verdict":"accepted","diagnostics":[],{paths}}}\n'
        self.assertIsNone(build_failure(Ran(0, ok, "")))
        d = '[{"kind":"unsupported","message":"not i7"}]'
        no = f'{{"file":"f","verdict":"unsupported","diagnostics":{d}}}\n'
        self.assertEqual(build_failure(Ran(1, no, "")), "unsupported: not i7")
        self.assertIsInstance(build_failure(Ran(2, "", "funk: usage\n")), str)


if __name__ == "__main__":
    unittest.main()
