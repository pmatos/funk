"""Tests of the cells of the `gpu` dialect, and that they follow its ops in
Lean (#406)."""

import re
import unittest
from pathlib import Path

import cells
import coverage
import gpu_cells
from cells import Cell, CellError, of_op
from firtext import Op

GPU = Path(__file__).resolve().parents[2] / "lean" / "Fir" / "Gpu"


def lean(name: str) -> str:
    return (GPU / f"{name}.lean").read_text(encoding="utf-8")


def constructors(text: str, name: str) -> list[str]:
    """The constructors of the inductive type `name`, in order."""
    start = text.index(f"inductive {name} where")
    end = text.index("deriving", start)
    return re.findall(r"\n  \| (\w+)", text[start:end])


def words(text: str, name: str) -> dict[str, str]:
    """The word that the Lean definition `name` gives each constructor."""
    start = text.index(f"def {name} ")
    end = text.index("\n\n", start)
    return dict(re.findall(r'\| \.(\w+) => "([\w.]+)"', text[start:end]))


class FollowsLean(unittest.TestCase):
    def assert_cells_follow(self, ops: str, text: str, valid: str) -> None:
        """One cell per constructor of `Query` and of `Dim`, by the words
        that `Text.lean` gives them, at the one width of `Op.Valid`; `Op`
        has no other constructor."""
        self.assertEqual(constructors(ops, "Op"), ["query"])
        queries = words(text, "Query.name")
        self.assertEqual(
            tuple(queries.get(q) for q in constructors(ops, "Query")),
            gpu_cells.GPU_OPS,
        )
        dims = words(text, "Dim.word")
        self.assertEqual(
            tuple(dims.get(d) for d in constructors(ops, "Dim")), gpu_cells.DIMS
        )
        widths = re.findall(r"\| \.query _ _ w => w = (\d+)", valid)
        self.assertEqual([f"i{w}" for w in widths], [gpu_cells.GPU_WIDTH])

    def test_the_ops_of_gpu(self):
        self.assert_cells_follow(lean("Ops"), lean("Text"), lean("Validation"))

    def test_a_new_op_question_or_dimension_fails_the_check(self):
        ops, text, valid = lean("Ops"), lean("Text"), lean("Validation")
        query = "  | query (q : Query) (d : Dim) (w : Nat)\n"
        size = "  | numWorkGroups\n"
        z = "  | z\n"
        for name, edit in [
            ("an op", (query, query + "  | barrier\n")),
            ("a question", (size, size + "  | subgroupId\n")),
            ("a dimension", (z, z + "  | w\n")),
        ]:
            self.assertEqual(ops.count(edit[0]), 1, edit[0])
            with self.subTest(edit=name), self.assertRaises(AssertionError):
                self.assert_cells_follow(ops.replace(*edit), text, valid)
        with self.subTest(edit="a width"), self.assertRaises(AssertionError):
            self.assert_cells_follow(ops, text, valid.replace("w = 32", "w = 64"))


class Cells(unittest.TestCase):
    def test_the_cells_of_an_op(self):
        op = Op("gpu.work_group_size", ("gpu.z",), (), ("i32",), ())
        self.assertEqual(
            of_op(op), {Cell("gpu", "gpu.work_group_size", "gpu.z", "i32")}
        )

    def test_a_text_that_is_not_a_cell(self):
        for op in [
            Op("gpu.work_item_id", ("gpu.w",), (), ("i32",), ()),
            Op("gpu.work_item_id", (), (), ("i32",), ()),
            Op("gpu.work_item_id", ("gpu.x",), (), ("i64",), ()),
            Op("gpu.work_item_id", ("gpu.x",), ("i32",), ("i32",), ()),
        ]:
            with self.subTest(op=op), self.assertRaises(CellError):
                of_op(op)

    def test_the_cell_set(self):
        found = [c for c in cells.cells((8,), gpu=True) if c.table == "gpu"]
        self.assertEqual(len(found), 12)
        self.assertEqual(found[1], Cell("gpu", "gpu.work_item_id", "gpu.y", "i32"))
        self.assertFalse(any(c.table == "gpu" for c in cells.cells((8,))))

    def test_only_the_interpreter_only_side_has_them(self):
        self.assertEqual(
            [side.name for side in coverage.SIDES if side.gpu], ["interpreter"]
        )


if __name__ == "__main__":
    unittest.main()
