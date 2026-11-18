"""Tests of the cells of the field address `fieldaddr` (#236)."""

import unittest

import cells
import coverage
from cells import Cell, CellError, of_op
from firtext import Op


class Tests(unittest.TestCase):
    def test_a_field_address_is_a_cell_with_no_index_or_at_its_index(self):
        for ptr in ("ptr", "ptr(1)"):
            op = Op("fieldaddr", ("@pair", "1"), (ptr,), (ptr,), ())
            self.assertEqual(of_op(op), {Cell("fields", "fieldaddr", "", "")})
            op = Op("fieldaddr", ('@"a b"', "0"), (ptr, "i33"), (ptr,), ())
            self.assertEqual(of_op(op), {Cell("fields", "fieldaddr", "", "i33")})

    def test_any_other_text_of_it_is_not_a_cell(self):
        for bad in [
            Op("fieldaddr", ("@pair",), ("ptr",), ("ptr",), ()),
            Op("fieldaddr", ("@pair", "1", "2"), ("ptr",), ("ptr",), ()),
            Op("fieldaddr", ("1", "@pair"), ("ptr",), ("ptr",), ()),
            Op("fieldaddr", ("@pair", "-1"), ("ptr",), ("ptr",), ()),
            Op("fieldaddr", ("@pair", "@q"), ("ptr",), ("ptr",), ()),
            Op("fieldaddr", ("pair", "1"), ("ptr",), ("ptr",), ()),
            Op("fieldaddr", ("@pair", "1"), ("ptr", "f32"), ("ptr",), ()),
            Op("fieldaddr", ("@pair", "1"), ("ptr", "ptr"), ("ptr",), ()),
            Op("fieldaddr", ("@pair", "1"), ("ptr", "i8", "i8"), ("ptr",), ()),
            Op("fieldaddr", ("@pair", "1"), (), ("ptr",), ()),
            Op("fieldaddr", ("@pair", "1"), ("ptr",), (), ()),
            Op("fieldaddr", ("@pair", "1"), ("i64",), ("i64",), ()),
            Op("fieldaddr", ("@pair", "1"), ("ptr",), ("ptr(1)",), ()),
        ]:
            with self.subTest(op=bad), self.assertRaises(CellError):
                of_op(bad)

    def test_a_side_has_a_cell_with_no_index_and_one_at_each_field_width(self):
        found = cells.cells((8,), offsets=(8,), fields=(1, 64))
        self.assertEqual(
            [c for c in found if c.table == "fields"],
            [Cell("fields", "fieldaddr", "", w) for w in ("", "i1", "i64")],
        )
        self.assertFalse(
            any(c.table == "fields" for c in cells.cells((8,), offsets=(8,)))
        )

    def test_only_the_interpreter_only_side_has_them_until_the_backend_lowers_it(self):
        self.assertEqual(cells.FIELD_DIFFERENTIAL, ())
        self.assertEqual(cells.FIELD_INTERPRETER, cells.INTERPRETER)
        sides = {side.name: side for side in coverage.SIDES}
        self.assertEqual(sides["differential"].fields, cells.FIELD_DIFFERENTIAL)
        self.assertEqual(sides["interpreter"].fields, cells.FIELD_INTERPRETER)

    def test_the_matrix_shows_each_cell(self):
        self.assertEqual(
            coverage.show(Cell("fields", "fieldaddr", "", "")),
            "fieldaddr with no index",
        )
        self.assertEqual(
            coverage.show(Cell("fields", "fieldaddr", "", "i8")), "fieldaddr by i8"
        )


if __name__ == "__main__":
    unittest.main()
