"""Tests for scripts/suite_summary.py, and for how scripts/check-rust.sh
calls it, against fake cargo and rustc. Run: python scripts/test_suite_summary.py
"""

import io
import os
import re
import subprocess
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path
from unittest import mock

from suite_summary import cargo_test, harness, lean_counts, main, strip_lean

REPO = Path(__file__).resolve().parent.parent
RUST = re.search(
    r'^channel = "(.*)"$', (REPO / "rust-toolchain.toml").read_text(), re.MULTILINE
)[1]

CARGO = """\
running 3 tests
test a ... ok
test b ... ignored
test c ... ok

test result: \x1b[32mok\x1b[0m. 2 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out; finished in 0.01s

running 2 tests
test d ... FAILED
test e ... ok

test result: FAILED. 1 passed; 1 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s

   Doc-tests funk_ir

running 1 test
test src/lib.rs - f (line 3) ... ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.20s
"""


def tool(path: Path, body: str) -> None:
    path.write_text("#!/usr/bin/env bash\n" + body, encoding="utf-8")
    path.chmod(0o755)


class Summary(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(self.enterContext(tempfile.TemporaryDirectory()))
        self.summary = self.tmp / "summary.md"
        self.enterContext(
            mock.patch.dict(os.environ, {"GITHUB_STEP_SUMMARY": str(self.summary)})
        )

    def run_main(self, *args: str) -> tuple[int, str]:
        out = io.StringIO()
        with redirect_stdout(out):
            status = main(list(args))
        return status, out.getvalue()

    def test_cargo_test_sums_every_target(self):
        self.assertEqual(cargo_test(CARGO), [3, 5, 4, 1, 1])
        self.assertIsNone(cargo_test("error[E0425]: cannot find value `x`\n"))

    def test_cargo_test_writes_the_summary_and_the_log(self):
        log = self.tmp / "cargo.log"
        log.write_text(CARGO, encoding="utf-8")
        status, out = self.run_main("cargo-test", str(log), "101")
        self.assertEqual(status, 0)
        self.assertIn(
            "Rust tests (cargo test): 3 test targets, 5 tests run, 4 passed,"
            " 1 failed, 1 ignored\n",
            out,
        )
        text = self.summary.read_text(encoding="utf-8")
        self.assertIn("### Rust tests (cargo test)\n", text)
        self.assertIn("| Test targets | Tests run | Passed | Failed | Ignored |", text)
        self.assertIn("| 3 | 5 | 4 | 1 | 1 |", text)
        self.assertIn("cargo test exited with status 101.", text)

    def test_a_passing_run_without_counts_fails(self):
        log = self.tmp / "cargo.log"
        log.write_text("nothing\n", encoding="utf-8")
        self.assertEqual(self.run_main("cargo-test", str(log), "0")[0], 1)
        status, out = self.run_main("cargo-test", str(log), "101")
        self.assertEqual(status, 0)
        self.assertIn("cargo test exited with status 101.", out)

    def test_strip_lean_blanks_comments_and_literals(self):
        src = (
            "/- outer /- inner -/\n#guard 1 -/\n"
            '#guard s = "a /- b"\n'
            "def q := '\"' -- #guard\n"
            "theorem t' : x' = '/' := rfl\n"
            '/-- doc\ntheorem in a doc -/\nexample : "two\nlines" = "" := rfl\n'
        )
        out = strip_lean(src)
        self.assertEqual(out.count("\n"), src.count("\n"))
        self.assertEqual(out.splitlines()[1], "")
        self.assertEqual(out.splitlines()[2], "#guard s = ")
        self.assertEqual(out.splitlines()[3], "def q :=  ")
        self.assertEqual(out.splitlines()[4], "theorem t' : x' =  := rfl")
        self.assertEqual(out.splitlines()[5:], ["", "", "example : ", " =  := rfl"])

    def test_lean_counts_each_library(self):
        lean = self.tmp / "lean"
        (lean / "Fir").mkdir(parents=True)
        (lean / "FirTest" / "Deep").mkdir(parents=True)
        (lean / ".lake" / "FirTest").mkdir(parents=True)
        (lean / "Fir.lean").write_text("import Fir.A\n#guard true\n")
        (lean / "Fir" / "A.lean").write_text(
            "@[simp] theorem a : 1 = 1 := rfl\n  private theorem b : True := ⟨⟩\n"
        )
        (lean / "FirTest" / "Deep" / "B.lean").write_text(
            "#guard_msgs in\n#eval 1\n  #guard 2 = 2\nexample : True := ⟨⟩\n"
            "-- #guard false\n/- theorem c -/\n#guard_expr 1 = 1\n"
        )
        (lean / ".lake" / "FirTest" / "C.lean").write_text("#guard true\n")
        (lean / "lakefile.lean").write_text("#guard true\n")
        self.assertEqual(
            lean_counts(lean), [["Fir", 1, 0, 2, 0], ["FirTest", 1, 1, 0, 1]]
        )
        status, out = self.run_main("lean", str(lean))
        self.assertEqual(status, 0)
        self.assertIn(
            "Lean checks that building lean/ ran: FirTest: 1 #guard,"
            " 1 #guard_msgs, 0 theorems, 1 examples\n",
            out,
        )
        self.assertIn(
            "| :-- | --: | --: | --: | --: |\n| Fir | 1 | 0 | 2 | 0 |",
            self.summary.read_text(),
        )

    def test_harness_reads_its_last_count_line(self):
        text = "passed  a: b\n1 checks: 1 passed, 0 failed, 0 invalid\n"
        text += "20818 checks: 20816 passed, 1 failed, 1 invalid\n"
        self.assertEqual(harness(text), [20818, 20816, 1, 1])
        log = self.tmp / "harness.log"
        log.write_text(text, encoding="utf-8")
        status, out = self.run_main("harness", str(log), "1", "0")
        self.assertEqual(status, 0)
        self.assertIn(
            "20,818 checks, 20,816 passed, 1 failed, 1 invalid,"
            " passed invalid-verdict fixture\n",
            out,
        )
        self.assertIn("The harness exited with status 1.", out)

    def test_harness_without_counts(self):
        log = self.tmp / "harness.log"
        log.write_text("harness: no such file\n", encoding="utf-8")
        self.assertEqual(self.run_main("harness", str(log), "0", "0")[0], 1)
        status, out = self.run_main("harness", str(log), "2", "1")
        self.assertEqual(status, 0)
        self.assertIn("failed invalid-verdict fixture", out)

    def test_counts_writes_one_row(self):
        status, out = self.run_main("counts", "Round trip", "texts=861", "result=ok")
        self.assertEqual(status, 0)
        self.assertEqual(out, "Round trip: 861 texts, ok result\n")
        self.assertIn(
            "| Texts | Result |\n| --: | --: |\n| 861 | ok |", self.summary.read_text()
        )

    def test_usage(self):
        out = io.StringIO()
        with mock.patch("sys.stderr", out):
            self.assertEqual(main(["counts", "Title"]), 2)
            self.assertEqual(main(["lean"]), 2)
        self.assertFalse(self.summary.exists())


class CheckRust(unittest.TestCase):
    """check-rust.sh test writes the counts only when GITHUB_STEP_SUMMARY is
    set, and exits with cargo's status either way."""

    def setUp(self):
        self.tmp = Path(self.enterContext(tempfile.TemporaryDirectory()))
        self.bin = self.tmp / "bin"
        self.bin.mkdir()
        (self.tmp / "out.txt").write_text(CARGO, encoding="utf-8")
        tool(
            self.bin / "cargo",
            f'if [[ $1 == --version ]]; then echo "cargo {RUST} (fake)"; exit; fi\n'
            'echo "$*" >>"$LOG/cargo"\ncat "$LOG/out.txt"\nexit "$STATUS"\n',
        )
        tool(self.bin / "rustc", f'echo "rustc {RUST} (fake)"\n')

    def run_script(self, status: int, summary: Path | None):
        env = {k: v for k, v in os.environ.items() if k != "GITHUB_STEP_SUMMARY"}
        env.update(LOG=str(self.tmp), STATUS=str(status))
        env["PATH"] = f"{self.bin}:{env['PATH']}"
        if summary is not None:
            env["GITHUB_STEP_SUMMARY"] = str(summary)
        return subprocess.run(
            ["bash", str(REPO / "scripts" / "check-rust.sh"), "test"],
            check=False,
            env=env,
            capture_output=True,
            text=True,
            timeout=60,
        )

    def test_in_ci_the_counts_go_to_the_summary(self):
        summary = self.tmp / "summary.md"
        for status in (0, 101):
            done = self.run_script(status, summary)
            self.assertEqual(done.returncode, status, done.stderr)
            self.assertIn("test d ... FAILED\n", done.stdout)
            self.assertIn("Rust tests (cargo test): 3 test targets,", done.stdout)
        text = summary.read_text(encoding="utf-8")
        self.assertEqual(text.count("| 3 | 5 | 4 | 1 | 1 |"), 2)
        self.assertEqual(text.count("cargo test exited with status 101."), 1)
        calls = (self.tmp / "cargo").read_text().splitlines()
        self.assertEqual(calls, ["test --workspace --locked"] * 2)

    def test_locally_it_runs_cargo_test_alone(self):
        for status in (0, 101):
            done = self.run_script(status, None)
            self.assertEqual(done.returncode, status, done.stderr)
            self.assertEqual(done.stdout, CARGO)
        self.assertEqual(list(self.tmp.glob("*.md")), [])


if __name__ == "__main__":
    unittest.main()
