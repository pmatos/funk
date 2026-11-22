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

    def test_a_kernel_s_test_counts_its_table_s_ops(self):
        kernel = MODULE.replace(
            "locs {",
            "module @dev() {\n  dialects gpu\n\n"
            "  func @k() -> i32 {\n  ^e:\n"
            "    %i: i32 = gpu.work_item_id gpu.x @0\n"
            "    %j: i32 = call @g %i @0\n    ret %j @0\n  }\n\n"
            "  func @g(%a: i32) -> i32 {\n  ^e:\n"
            "    %b: i32 = mul %a, %a @0\n    ret %b @0\n  }\n\n"
            "  module @in() {\n    dialects gpu\n\n"
            "    func @k() -> i32 {\n    ^e:\n"
            "      %i: i32 = gpu.num_work_groups gpu.z @0\n      ret %i @0\n    }\n\n"
            "  }\n\n}\n\nlocs {",
        )
        tests = TESTS.replace(
            "]\n",
            '  { func = "@dev::@k", expect = ["0"] },\n'
            '  { func = "@dev::@in::@k", expect = ["1"] },\n]\n',
        )
        with tempfile.TemporaryDirectory() as d:
            with_kernel = coverage.count(corpus(Path(d), kernel, tests))
        with tempfile.TemporaryDirectory() as d:
            without = coverage.count(corpus(Path(d)))
        self.assertEqual(with_kernel["differential"], without["differential"])
        added = with_kernel["interpreter"] - without["interpreter"]
        self.assertEqual(
            dict(added),
            {
                Cell("gpu", "gpu.work_item_id", "gpu.x", "i32"): 1,
                Cell("gpu", "gpu.num_work_groups", "gpu.z", "i32"): 1,
                Cell("ops", "mul", "", "i32"): 1,
                Cell("values", "call", "one", "i32"): 1,
                Cell("values", "ret", "one", "i32"): 2,
                Cell("values", "func", "one", "i32"): 2,
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
            out = Path(d) / "out"
            matrix = out / "README.md"
            err = io.StringIO()
            self.assertEqual(coverage.run(root, matrix, True, err), 1)
            self.assertEqual(
                sorted(p.name for p in out.iterdir()),
                ["README.md", "differential.md", "interpreter.md"],
            )
            self.assertIn(
                "(differential.md): 573 cells, 6 with a test", matrix.read_text()
            )
            diff = (out / "differential.md").read_text()
            self.assertIn("| `add` | `nuw` | **0** | 1 | **0** |", diff)
            self.assertNotIn("gpu", diff)
            text = (out / "interpreter.md").read_text()
            self.assertIn("| `add` | `nuw` | **0** | **0** | 2 | **0** |", text)
            self.assertIn("| `gpu.work_item_id` | `gpu.x` | **0** |", text)
            self.assertIn(
                "no test exercises the cell differential: add i1", err.getvalue()
            )
            self.assertIn("the cell interpreter: zext from i7 to i128", err.getvalue())
            self.assertIn(
                "the cell interpreter: gpu.num_work_groups gpu.z i32", err.getvalue()
            )
            self.assertNotIn("stale", err.getvalue())
            for name in ("README.md", "interpreter.md"):
                page = out / name
                fresh = page.read_text()
                page.write_text(fresh + "\n")
                err = io.StringIO()
                self.assertEqual(coverage.run(root, matrix, False, err), 1)
                self.assertIn(f"{name} is stale", err.getvalue())
                page.write_text(fresh)
            (out / "differential.md").unlink()
            err = io.StringIO()
            self.assertEqual(coverage.run(root, matrix, False, err), 1)
            self.assertIn("differential.md is stale", err.getvalue())

    def test_a_corpus_it_cannot_read(self):
        for module, tests, needle in [
            (MODULE, 'tests = [{ func = "@k" }]\n', "there is no function @k"),
            (MODULE.replace("call @g", "call @k"), TESTS, "there is no function @k"),
            (MODULE.replace("add nuw", "and nuw"), TESTS, "and nuw is not a cell"),
            (MODULE.replace("^entry:\n  %one", "^entry:\n  %one %"), TESTS, "m.fir"),
            (
                MODULE,
                'tests = [{ func = "@h::@f", expect = [] }]\n',
                "no function @h::@f",
            ),
            (
                MODULE.replace("add nuw", "gpu.work_item_id gpu.w"),
                TESTS,
                "gpu.work_item_id gpu.w of ('i8', 'i8') to ('i8',) is not a cell",
            ),
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
