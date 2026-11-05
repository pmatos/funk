"""Tests for scripts/run_unittests.py: each runs a test module both as a
test hook's old entry did, `python FILE` or `python -m unittest ...`, and
through the runner, and compares what they did.
Run: python scripts/test_run_unittests.py"""

import json
import os
import re
import subprocess
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

RUNNER = Path(__file__).resolve().with_name("run_unittests.py")
HEADER = "| Tests run | Passed | Failed | Errors | Skipped |"

# Writes the state that a test module sees to the file that PROBE names.
PROBE = """
import json, os, sys, unittest

class Probe(unittest.TestCase):
    def test_state(self):
        main = sys.modules["__main__"]
        state = {
            "name": __name__,
            "file": __file__,
            "argv": sys.argv,
            "path": sys.path[:2],
            "main": [getattr(main, "__file__", None), main.__spec__ is None],
            "summary": os.environ.get("GITHUB_STEP_SUMMARY"),
        }
        with open(os.environ["PROBE"], "a") as f:
            f.write(json.dumps(state) + "\\n")

if __name__ == "__main__":
    unittest.main()
"""

MIXED = """
import unittest

class Mixed(unittest.TestCase):
    def test_passes(self):
        '''A docstring, which -v prints.'''

    def test_fails(self):
        self.fail("no")

    def test_errs(self):
        raise RuntimeError("boom")

    @unittest.skip("not here")
    def test_skipped(self):
        pass

    @unittest.expectedFailure
    def test_expected(self):
        self.fail("as expected")

    @unittest.expectedFailure
    def test_unexpected(self):
        pass

    def test_subtests(self):
        for i in range(3):
            with self.subTest(i=i):
                self.assertNotEqual(i, 1)

if __name__ == "__main__":
    unittest.main()
"""

PASSING = """
import unittest

class Passing(unittest.TestCase):
    def test_one(self):
        pass

    @unittest.skip("not here")
    def test_two(self):
        pass

if __name__ == "__main__":
    unittest.main()
"""

SKIPPED_ONLY = """
import unittest

@unittest.skip("not here")
class Skipped(unittest.TestCase):
    def test_one(self):
        pass

if __name__ == "__main__":
    unittest.main()
"""

EMPTY = """
import unittest

if __name__ == "__main__":
    unittest.main()
"""

BROKEN = """
import unittest
import no_such_module_here

if __name__ == "__main__":
    unittest.main()
"""

UNCOMPILABLE = """
import unittest

def (:
    pass
"""

# A test that runs a suite of its own, as a test of a test runner might.
NESTED = """
import sys, unittest

class Inner(unittest.TestCase):
    def test_a(self):
        pass

    def test_b(self):
        pass

class Outer(unittest.TestCase):
    def test_runs_a_suite(self):
        module = sys.modules[__name__]
        unittest.main(module=module, defaultTest="Inner", argv=["x"], exit=False)

if __name__ == "__main__":
    unittest.main(defaultTest="Outer")
"""


def normal(text: str) -> str:
    """`text` without the times that unittest prints."""
    return re.sub(r"in \d+\.\d+s", "in Xs", text)


class Runner(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(self.enterContext(tempfile.TemporaryDirectory()))
        (self.tmp / "t").mkdir()
        self.summary = self.tmp / "summary.md"
        self.probe = self.tmp / "probe.jsonl"

    def write(self, name: str, text: str) -> str:
        (self.tmp / "t" / name).write_text(textwrap.dedent(text), encoding="utf-8")
        return f"t/{name}"

    def run_python(self, args: list[str], summary: bool = False):
        env = {k: v for k, v in os.environ.items() if k != "GITHUB_STEP_SUMMARY"}
        env["PROBE"] = str(self.probe)
        if summary:
            env["GITHUB_STEP_SUMMARY"] = str(self.summary)
        return subprocess.run(
            [sys.executable, *args],
            check=False,
            cwd=self.tmp,
            env=env,
            capture_output=True,
            text=True,
            timeout=60,
        )

    def both(self, args: list[str], summary: bool = True):
        """The old entry's run of `args`, then the runner's."""
        old = self.run_python(args)
        new = self.run_python([str(RUNNER), "a-hook", *args], summary)
        return old, new

    def assertSameRun(self, old, new):
        self.assertEqual(new.returncode, old.returncode, new.stderr)
        self.assertEqual(normal(new.stderr), normal(old.stderr))

    def rows(self) -> str:
        return self.summary.read_text(encoding="utf-8")

    def test_a_file_sees_what_python_file_gives_it(self):
        path = self.write("test_probe.py", PROBE)
        old, new = self.both([path, "-v"])
        self.assertSameRun(old, new)
        before, after = map(json.loads, self.probe.read_text().splitlines())
        self.assertEqual(after, before)
        self.assertEqual(before["name"], "__main__")
        self.assertEqual(before["argv"], [path, "-v"])
        self.assertEqual(before["path"][0], str(self.tmp / "t"))
        self.assertIsNone(after["summary"])
        self.assertIn("| 1 | 1 | 0 | 0 | 0 |", self.rows())

    def test_discover_sees_what_python_m_unittest_gives_it(self):
        self.write("test_probe.py", PROBE)
        args = ["-m", "unittest", "discover", "-s", "t", "-p", "test_*.py", "-v"]
        old, new = self.both(args)
        self.assertSameRun(old, new)
        before, after = map(json.loads, self.probe.read_text().splitlines())
        self.assertEqual(after, before)
        self.assertEqual(before["name"], "test_probe")
        self.assertEqual(before["path"], [str(self.tmp / "t"), str(self.tmp)])
        self.assertIsNone(after["summary"])
        self.assertIn("| 1 | 1 | 0 | 0 | 0 |", self.rows())

    def test_every_outcome_is_counted_and_fails_the_run(self):
        path = self.write("test_mixed.py", MIXED)
        old, new = self.both([path, "-v"])
        self.assertSameRun(old, new)
        self.assertEqual(new.returncode, 1)
        header = HEADER + " Expected failures | Unexpected successes |"
        self.assertIn(header, self.rows())
        # Seven tests, one of which passes; a failing subtest counts as a failure.
        self.assertIn("| 7 | 1 | 2 | 1 | 1 | 1 | 1 |", self.rows())
        self.assertIn("unittest exited with status 1.", self.rows())
        self.assertIn(
            "Python tests (a-hook): 7 tests run, 1 passed, 2 failed, 1 errors,",
            new.stdout,
        )

    def test_a_passing_run_names_no_status(self):
        path = self.write("test_passing.py", PASSING)
        old, new = self.both([path])
        self.assertSameRun(old, new)
        self.assertEqual(new.returncode, 0)
        self.assertEqual(self.rows().count("| 2 | 1 | 0 | 0 | 1 |"), 1)
        self.assertNotIn("exited", self.rows())
        self.assertNotIn("Expected failures", self.rows())

    def test_a_module_that_cannot_import(self):
        path = self.write("test_broken.py", BROKEN)
        old, new = self.both([path])
        self.assertSameRun(old, new)
        self.assertEqual(new.returncode, 1)
        self.assertIn("ModuleNotFoundError", self.rows())
        old, new = self.both(["-m", "unittest", "discover", "-s", "t"])
        self.assertSameRun(old, new)
        self.assertEqual(new.returncode, 1)
        self.assertIn("| 1 | 0 | 0 | 1 | 0 |", self.rows())

    def test_a_file_that_does_not_compile(self):
        path = self.write("test_uncompilable.py", UNCOMPILABLE)
        old, new = self.both([path])
        self.assertSameRun(old, new)
        self.assertEqual(new.returncode, 1)
        self.assertIn("The tests did not run: SyntaxError", self.rows())

    def test_discover_from_a_missing_directory(self):
        args = ["-m", "unittest", "discover", "-s", "gone", "-p", "test_*.py"]
        old, new = self.both(args)
        self.assertEqual(new.returncode, old.returncode)
        self.assertEqual(new.returncode, 1)
        self.assertIn("ImportError", new.stderr)
        self.assertIn("The tests did not run: ImportError", self.rows())

    def test_no_tests_exits_as_unittest_does(self):
        path = self.write("test_empty.py", EMPTY)
        old, new = self.both([path])
        self.assertSameRun(old, new)
        self.assertIn("No test ran.", self.rows())
        old, new = self.both(["-m", "unittest", "discover", "-s", "t"])
        self.assertSameRun(old, new)

    def test_a_missing_file(self):
        old, new = self.both(["t/test_gone.py"])
        self.assertEqual(new.returncode, old.returncode)
        self.assertEqual(new.returncode, 2)
        self.assertIn("can't open file", new.stderr)
        self.assertIn("There is no test file t/test_gone.py.", self.rows())

    def test_skipped_only_is_a_run(self):
        path = self.write("test_skipped.py", SKIPPED_ONLY)
        old, new = self.both([path])
        self.assertSameRun(old, new)
        self.assertEqual(new.returncode, 0)
        self.assertNotIn("No test ran.", self.rows())

    def test_a_suite_that_a_test_runs_is_not_counted(self):
        path = self.write("test_nested.py", NESTED)
        old, new = self.both([path])
        self.assertSameRun(old, new)
        self.assertIn("| 1 | 1 | 0 | 0 | 0 |", self.rows())

    def test_locally_it_prints_and_exits_as_before(self):
        for text in (PASSING, MIXED, EMPTY, BROKEN):
            path = self.write("test_one.py", text)
            old, new = self.both([path, "-v"], summary=False)
            self.assertSameRun(old, new)
            self.assertEqual(new.stdout, old.stdout)
        self.assertFalse(self.summary.exists())

    def test_bad_usage(self):
        for args in ([], ["a-hook"], ["a-hook", "-m", "pytest"]):
            done = self.run_python([str(RUNNER), *args], summary=True)
            self.assertEqual(done.returncode, 2)
            self.assertIn("Usage:", done.stderr)
        self.assertFalse(self.summary.exists())


if __name__ == "__main__":
    unittest.main()
