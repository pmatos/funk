"""Tests of the cells of `memcpy`, `memmove` and `memset`, and that they
follow the ops' names in Lean (#234)."""

import re
import unittest
from pathlib import Path

import cells
import copy_cells
import coverage
from cells import Cell, CellError, of_op
from firtext import Op

TEXT = (
    Path(__file__).resolve().parents[2] / "lean" / "Fir" / "Core" / "MemCopyText.lean"
)


def op(name: str, attrs: tuple[str, ...], operands: tuple[str, ...], results=()) -> Op:
    return Op(name, attrs, operands, tuple(results), ())


class CopyCells(unittest.TestCase):
    def test_the_names_are_those_of_lean(self):
        text = TEXT.read_text(encoding="utf-8")
        start = text.index("def CopyKind.name ")
        names = re.findall(
            r'\| \.\w+ => "(\w+)"', text[start : text.index("\n\n", start)]
        )
        self.assertEqual(tuple(names), copy_cells.COPY_OPS)

    def test_a_copy_is_a_cell_at_the_width_of_its_length(self):
        for name in copy_cells.COPY_OPS:
            for ptr in ("ptr", "ptr(3)"):
                found = of_op(op(name, ("nonatomic",), (ptr, ptr, "i33")))
                self.assertEqual(found, {Cell("copies", name, "", "i33")})

    def test_a_fill_is_a_cell_at_the_width_of_its_length(self):
        for ptr, value in (("ptr", "i8"), ("ptr(3)", "i16")):
            found = of_op(op("memset", ("nonatomic",), (ptr, value, "i33")))
            self.assertEqual(found, {Cell("copies", "memset", "", "i33")})

    def test_other_texts_are_not_cells(self):
        for bad in (
            op("memcpy", ("seq_cst",), ("ptr", "ptr", "i64")),
            op("memcpy", ("nonatomic",), ("ptr", "ptr(1)", "i64")),
            op("memmove", ("nonatomic",), ("ptr", "ptr", "f64")),
            op("memmove", ("nonatomic",), ("ptr", "ptr")),
            op("memcpy", ("nonatomic",), ("ptr", "ptr", "i64"), ("i64",)),
            op("memset", ("seq_cst",), ("ptr", "i8", "i64")),
            op("memset", ("nonatomic",), ("ptr", "ptr", "i64")),
            op("memset", ("nonatomic",), ("i64", "i8", "i64")),
            op("memset", ("nonatomic",), ("ptr", "i8")),
        ):
            with self.assertRaises(CellError):
                of_op(bad)

    def test_both_sides_have_the_cells_at_their_pointer_widths(self):
        for side in coverage.SIDES:
            found = {c for c in side.cells() if c.table == "copies"}
            want = {
                Cell("copies", o, "", f"i{w}")
                for o in copy_cells.MEM_OPS
                for w in side.offsets
            }
            self.assertEqual(found, want, side.name)

    def test_the_catalog_has_no_copies_by_default(self):
        self.assertNotIn("copies", {t.kind for t in cells.catalog((8,), (), (8,))})


if __name__ == "__main__":
    unittest.main()
