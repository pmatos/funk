"""The process adapter preserves commands, decoding and native-only limits."""

import unittest
from pathlib import Path as FilePath
from unittest.mock import patch

import tools
from corpus import Test
from execution import ProcessRuns
from sets import BudgetExceeded, Outcomes, Path

TEST = Test("m.fir", "@f", args=("poison",), fuel=99)


class Execution(unittest.TestCase):
    def setUp(self):
        self.runs = ProcessRuns("fir-ref", FilePath("m.fir"), TEST, FilePath("exe"))

    def test_exhaustive_uses_given_arguments_and_decodes_the_budget(self):
        with patch.object(
            tools,
            "run",
            return_value=tools.Ran(
                0, '{"kind":"choice-budget-exceeded","budget":16}\n', ""
            ),
        ) as run:
            self.assertEqual(self.runs.exhaustive(("0",)), BudgetExceeded(16))
        run.assert_called_once_with(
            ["fir-ref", "run", "--fuel", "99", "--exhaustive", "--", "m.fir", "@f", "0"]
        )

    def test_scripted_distinguishes_omitted_and_explicit_empty_choices(self):
        response = tools.Ran(0, '{"kind":"return","values":["7"],"choices":0}\n', "")
        with patch.object(tools, "run", return_value=response) as run:
            self.assertIsInstance(self.runs.scripted(TEST.args, None), Path)
            self.assertIsInstance(self.runs.scripted(TEST.args, ()), Path)
        base = ["fir-ref", "run", "--fuel", "99"]
        tail = ["--", "m.fir", "@f", "poison"]
        self.assertEqual(run.call_args_list[0].args[0], base + tail)
        self.assertEqual(run.call_args_list[1].args[0], base + ["--choices", ""] + tail)

    def test_sampled_passes_seed_and_decodes_its_sequence(self):
        response = tools.Ran(
            0, '{"kind":"return","values":["7"],"choices":1,"sequence":["3"]}\n', ""
        )
        with patch.object(tools, "run", return_value=response) as run:
            self.assertEqual(self.runs.sampled(TEST.args, 9).sequence, ("3",))
        run.assert_called_once_with(
            [
                "fir-ref",
                "run",
                "--fuel",
                "99",
                "--seed",
                "9",
                "--",
                "m.fir",
                "@f",
                "poison",
            ]
        )

    def test_exhaustive_decodes_outcomes_and_scripted_rejects_bad_json(self):
        response = tools.Ran(
            0,
            '{"kind":"outcomes","choices":0,"outcomes":[{"kind":"return","values":[]}]}\n',
            "",
        )
        with patch.object(tools, "run", return_value=response):
            self.assertIsInstance(self.runs.exhaustive(()), Outcomes)
        with patch.object(tools, "run", return_value=tools.Ran(0, "bad JSON\n", "")):
            self.assertIn("not one JSON report", self.runs.scripted((), None))

    def test_native_uses_the_limited_runner_and_strict_decoder(self):
        with patch.object(
            tools, "run_native", return_value=tools.Ran(0, '{"values":["7"]}\n', "")
        ) as run:
            self.assertEqual(self.runs.native(("0",)), ("7",))
        run.assert_called_once_with(["exe", "@f", "0"])
        with patch.object(
            tools,
            "run_native",
            return_value=tools.Ran(0, '{"values":["7"]}\n', "unexpected error\n"),
        ):
            self.assertIn("unexpected error", self.runs.native(("0",)))

    def test_unavailable_executable_is_exposed_without_starting_a_process(self):
        runs = ProcessRuns("fir-ref", FilePath("m.fir"), TEST, "is not built: failed")
        self.assertEqual(runs.unavailable, "is not built: failed")
        self.assertIsNone(self.runs.unavailable)

    def test_process_start_errors_propagate(self):
        with (
            patch.object(tools, "run", side_effect=OSError("missing fir-ref")),
            self.assertRaisesRegex(OSError, "missing fir-ref"),
        ):
            self.runs.exhaustive(TEST.args)


if __name__ == "__main__":
    unittest.main()
