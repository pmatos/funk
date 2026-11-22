"""Tests of the cells of `ptr_expose` and `ptr_from_int`, and that they
follow the ops' names in Lean (#232)."""

import re
import unittest
from pathlib import Path

import address_cells
import coverage
from cells import Cell, CellError, of_op
from firtext import Op

TEXT = Path(__file__).resolve().parents[2] / "lean" / "Fir" / "Core" / "Text.lean"


def op(name: str, operands: tuple[str, ...], results: tuple[str, ...], attrs=()) -> Op:
    return Op(name, tuple(attrs), operands, results, ())


class AddressCells(unittest.TestCase):
    def test_the_names_are_those_of_lean(self):
        text = TEXT.read_text(encoding="utf-8")
        names = re.findall(r'\.ptr(?:Expose|FromInt) \.\. => "(\w+)"', text)
        self.assertEqual(tuple(names), address_cells.ADDRESS_OPS)

    def test_each_op_is_a_cell_at_the_width_of_its_integer(self):
        for ptr, i in (("ptr", "i64"), ("ptr(1)", "i32"), ("ptr(3)", "i7")):
            self.assertEqual(
                of_op(op("ptr_expose", (ptr,), (i,))),
                {Cell("addresses", "ptr_expose", "", i)},
            )
            self.assertEqual(
                of_op(op("ptr_from_int", (i,), (ptr,))),
                {Cell("addresses", "ptr_from_int", "", i)},
            )

    def test_every_other_shape_is_not_a_cell(self):
        for name, operands, results, attrs in (
            ("ptr_expose", ("ptr",), ("ptr",), ()),
            ("ptr_expose", ("i64",), ("ptr",), ()),
            ("ptr_expose", ("ptr",), ("i64",), ("nonatomic",)),
            ("ptr_expose", ("ptr", "i64"), ("i64",), ()),
            ("ptr_expose", ("ptr",), ("f32",), ()),
            ("ptr_expose", ("ptr",), ("ix",), ()),
            ("ptr_from_int", ("ptr",), ("ptr",), ()),
            ("ptr_from_int", ("ptr",), ("i64",), ()),
            ("ptr_from_int", ("i64",), (), ()),
        ):
            with (
                self.subTest(name=name, operands=operands, results=results),
                self.assertRaises(CellError),
            ):
                of_op(op(name, operands, results, attrs))

    def test_each_side_has_the_cells_at_its_address_widths(self):
        sides = {side.name: side.cells() for side in coverage.SIDES}
        for name, widths in (
            ("differential", address_cells.ADDRESS_DIFFERENTIAL),
            ("interpreter", address_cells.ADDRESS_INTERPRETER),
        ):
            expected = [
                Cell("addresses", o, "", f"i{w}")
                for o in address_cells.ADDRESS_OPS
                for w in widths
            ]
            self.assertEqual(
                [c for c in sides[name] if c.table == "addresses"], expected
            )


if __name__ == "__main__":
    unittest.main()
