"""Tests for scripts/rust_speed.py. Run: python scripts/test_rust_speed.py"""

import contextlib
import copy
import io
import json
import tempfile
import unittest
from pathlib import Path

from rust_speed import (
    BadFile,
    load_baseline,
    main,
    over_margin,
    parse_measured,
    percent_change,
)

BASELINE = {
    "recorded_on": "ubuntu-26.04",
    "glibc": "glibc 2.43",
    "valgrind": "valgrind-3.25.1",
    "sizes": {"adds": 100, "blocks": 20},
    "instructions": {
        "adds": {"fmt": 1000, "verify": 2000, "build": 3000},
        "blocks": {"fmt": 100, "verify": 200, "build": 300},
    },
}


def measured_text(**changes: int) -> str:
    lines = []
    for input_name, row in BASELINE["instructions"].items():
        for command, count in row.items():
            lines.append(
                f"{input_name} {command} {changes.get(f'{input_name}_{command}', count)}"
            )
    return "\n".join(lines) + "\n"


class Margin(unittest.TestCase):
    def test_exactly_ten_percent_is_within_the_margin(self):
        self.assertFalse(over_margin(1000, 1100))

    def test_one_instruction_past_ten_percent_is_over(self):
        self.assertTrue(over_margin(1000, 1101))

    def test_lower_counts_are_within_the_margin(self):
        self.assertFalse(over_margin(1000, 1))

    def test_percent_change(self):
        self.assertEqual(percent_change(1000, 1100), 10.0)
        self.assertEqual(percent_change(1000, 900), -10.0)


class Compare(unittest.TestCase):
    def run_compare(
        self, measured: str, *flags: str, baseline=BASELINE
    ) -> tuple[int, str]:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "baseline.json").write_text(json.dumps(baseline), encoding="utf-8")
            (root / "counts").write_text(measured, encoding="utf-8")
            out = io.StringIO()
            with contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
                status = main(
                    [
                        "compare",
                        str(root / "baseline.json"),
                        str(root / "counts"),
                        *flags,
                    ]
                )
        return status, out.getvalue()

    def test_equal_counts_pass(self):
        status, out = self.run_compare(measured_text())
        self.assertEqual(status, 0)
        self.assertIn("within the margin", out)

    def test_a_count_over_the_margin_fails_and_names_old_new_and_percent(self):
        status, out = self.run_compare(measured_text(blocks_build=331))
        self.assertEqual(status, 1)
        self.assertIn("funk build on blocks: 300 -> 331 (+10.33%)", out)

    def test_a_count_at_the_margin_passes(self):
        status, _ = self.run_compare(measured_text(blocks_build=330))
        self.assertEqual(status, 0)

    def test_advisory_reports_but_passes(self):
        status, out = self.run_compare(measured_text(adds_fmt=2000), "--advisory")
        self.assertEqual(status, 0)
        self.assertIn("funk fmt on adds: 1000 -> 2000 (+100.00%)", out)
        self.assertIn("CI decides", out)

    def test_a_missing_measurement_is_an_error(self):
        status, out = self.run_compare("adds fmt 1000\n")
        self.assertEqual(status, 2)
        self.assertIn("do not match", out)

    def test_a_baseline_without_a_count_is_an_error(self):
        baseline = copy.deepcopy(BASELINE)
        del baseline["instructions"]["adds"]["fmt"]
        status, out = self.run_compare(measured_text(), baseline=baseline)
        self.assertEqual(status, 2)
        self.assertIn("adds must name exactly", out)


class Files(unittest.TestCase):
    def test_a_malformed_line_is_rejected(self):
        with self.assertRaises(BadFile):
            parse_measured("adds fmt\n")

    def test_a_non_numeric_count_is_rejected(self):
        with self.assertRaises(BadFile):
            parse_measured(measured_text().replace("1000", "x", 1))

    def test_a_count_of_zero_is_rejected(self):
        with self.assertRaises(BadFile):
            parse_measured(measured_text(adds_fmt=0))

    def test_the_sizes_command_prints_adds_then_blocks(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "baseline.json"
            path.write_text(json.dumps(BASELINE), encoding="utf-8")
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                status = main(["sizes", str(path)])
        self.assertEqual((status, out.getvalue()), (0, "100 20\n"))

    def test_the_committed_baseline_is_well_formed(self):
        baseline = load_baseline(
            str(Path(__file__).with_name("rust-speed-baseline.json"))
        )
        self.assertEqual(set(baseline["sizes"]), {"adds", "blocks"})


if __name__ == "__main__":
    unittest.main()
