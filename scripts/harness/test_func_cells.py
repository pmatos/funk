"""Tests of the cell of the address of a function `funcaddr` (#235)."""

import unittest

import cells
import coverage
from cells import Cell, CellError, of_op
from firtext import Op


class Tests(unittest.TestCase):
    def test_an_address_of_a_function_is_one_cell_in_any_memory(self):
        for sym, ptr in (("@f", "ptr"), ('@"a b"', "ptr(1)")):
            op = Op("funcaddr", (sym,), (), (ptr,), ())
            self.assertEqual(of_op(op), {Cell("functions", "funcaddr", "", "")})

    def test_any_other_text_of_it_is_not_a_cell(self):
        for bad in [
            Op("funcaddr", (), (), ("ptr",), ()),
            Op("funcaddr", ("f",), (), ("ptr",), ()),
            Op("funcaddr", ("@f", "@g"), (), ("ptr",), ()),
            Op("funcaddr", ("@f",), ("ptr",), ("ptr",), ()),
            Op("funcaddr", ("@f",), (), ("i64",), ()),
            Op("funcaddr", ("@f",), (), (), ()),
        ]:
            with self.subTest(op=bad), self.assertRaises(CellError):
                of_op(bad)

    def test_only_the_interpreter_side_has_it_until_the_backend_lowers_it(self):
        sides = {side.name: side for side in coverage.SIDES}
        self.assertFalse(sides["differential"].func_addrs)
        self.assertTrue(sides["interpreter"].func_addrs)
        found = cells.cells((8,), offsets=(8,), func_addrs=True)
        self.assertEqual(
            [c for c in found if c.table == "functions"],
            [Cell("functions", "funcaddr", "", "")],
        )
        self.assertFalse(
            any(c.table == "functions" for c in cells.cells((8,), offsets=(8,)))
        )

    def test_the_matrix_shows_the_cell(self):
        self.assertEqual(
            coverage.show(Cell("functions", "funcaddr", "", "")), "funcaddr"
        )


if __name__ == "__main__":
    unittest.main()
