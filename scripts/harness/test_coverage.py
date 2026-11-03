"""Tests of the coverage matrix: what a test exercises, the counts, and the
check of the committed matrix."""

import io
import tempfile
import unittest
from pathlib import Path

import coverage
from cells import Cell

MODULE = """func @f(%a: i8) -> i8, i8 {
^entry:
  %b: i8 = call @g %a @0
  ret %a, %b @0
}

func @g(%a: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %b: i8 = add nuw %a, %one @0
  ret %b @0
}

func @h() {
^entry:
  ret @0
}

locs {
  @0 = unknown
}
"""
TESTS = """tests = [
  { func = "@f", args = ["1"] },
  { func = "@g", args = ["1"], expect = ["2"] },
  { func = "@g", args = ["-1"], expect = ["poison"] },
]
"""
REJECT = '[[reject]]\nverdict = "parse-error"\nrule = "r"\ntext = "x"\n'


def corpus(root: Path, module: str = MODULE, tests: str = TESTS) -> Path:
    root.mkdir(exist_ok=True)
    (root / "canonical").mkdir()
    (root / "reject").mkdir()
    (root / "canonical" / "m.fir").write_text(module)
    (root / "canonical" / "m.toml").write_text(tests)
    (root / "reject" / "r.toml").write_text(REJECT)
    return root


class Tests(unittest.TestCase):
    def test_a_test_exercises_the_functions_it_calls(self):
        with tempfile.TemporaryDirectory() as d:
            counts = coverage.count(corpus(Path(d)))
        diff, interp = counts["differential"], counts["interpreter"]
        self.assertEqual(
            dict(diff),
            {
                Cell("values", "func", "several", "i8"): 1,
                Cell("values", "call", "one", "i8"): 1,
                Cell("values", "ret", "several", "i8"): 1,
                Cell("values", "ret", "one", "i8"): 1,
                Cell("ops", "const", "", "i8"): 1,
                Cell("ops", "add", "nuw", "i8"): 1,
            },
        )
        self.assertEqual(
            dict(interp),
            {
                Cell("values", "func", "one", "i8"): 2,
                Cell("values", "ret", "one", "i8"): 2,
                Cell("ops", "const", "", "i8"): 2,
                Cell("ops", "add", "nuw", "i8"): 2,
            },
        )

    def test_recursion_is_read_once(self):
        functions = {
            "@f": coverage.firtext.Function("@f", (), (), ()),
        }
        self.assertEqual(coverage.reachable(functions, "@f"), ["@f"])

    def test_the_matrix_and_its_check(self):
        with tempfile.TemporaryDirectory() as d:
            root = corpus(Path(d) / "corpus")
            matrix = Path(d) / "out" / "README.md"
            err = io.StringIO()
            self.assertEqual(coverage.run(root, matrix, True, err), 1)
            text = matrix.read_text()
            self.assertIn("| `add` | `nuw` | **0** | 1 | **0** |", text)
            self.assertIn(
                "no test exercises the cell differential: add i1", err.getvalue()
            )
            self.assertIn("the cell interpreter: zext from i7 to i128", err.getvalue())
            self.assertNotIn("stale", err.getvalue())
            matrix.write_text(text.replace("| 1 |", "| 2 |", 1))
            err = io.StringIO()
            self.assertEqual(coverage.run(root, matrix, False, err), 1)
            self.assertIn("is stale", err.getvalue())

    def test_a_corpus_it_cannot_read(self):
        for module, tests, needle in [
            (MODULE, 'tests = [{ func = "@k" }]\n', "there is no function @k"),
            (MODULE.replace("call @g", "call @k"), TESTS, "there is no function @k"),
            (MODULE.replace("add nuw", "and nuw"), TESTS, "and nuw is not a cell"),
            (MODULE.replace("^entry:\n  %one", "^entry:\n  %one %"), TESTS, "m.fir"),
        ]:
            with self.subTest(needle=needle):
                with tempfile.TemporaryDirectory() as d:
                    root = corpus(Path(d), module, tests)
                    err = io.StringIO()
                    status = coverage.run(root, Path(d) / "matrix.md", False, err)
                self.assertEqual(status, 2)
                self.assertIn(needle, err.getvalue())


if __name__ == "__main__":
    unittest.main()
