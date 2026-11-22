"""Tests of the cell of the address of a global `globaladdr` (#237)."""

import unittest

import cells
import coverage
from cells import Cell, CellError, of_op
from firtext import Op


class Tests(unittest.TestCase):
    def test_an_address_of_a_global_is_one_cell_in_any_memory(self):
        for sym, ptr in (("@msg", "ptr"), ('@"a b"', "ptr(1)")):
            op = Op("globaladdr", (sym,), (), (ptr,), ())
            self.assertEqual(of_op(op), {Cell("globals", "globaladdr", "", "")})

    def test_any_other_text_of_it_is_not_a_cell(self):
        for bad in [
            Op("globaladdr", (), (), ("ptr",), ()),
            Op("globaladdr", ("msg",), (), ("ptr",), ()),
            Op("globaladdr", ("@msg", "@tbl"), (), ("ptr",), ()),
            Op("globaladdr", ("@msg",), ("ptr",), ("ptr",), ()),
            Op("globaladdr", ("@msg",), (), ("i64",), ()),
            Op("globaladdr", ("@msg",), (), (), ()),
        ]:
            with self.subTest(op=bad), self.assertRaises(CellError):
                of_op(bad)

    def test_only_the_interpreter_side_has_it_until_the_backend_lowers_it(self):
        sides = {side.name: side for side in coverage.SIDES}
        self.assertFalse(sides["differential"].global_addrs)
        self.assertTrue(sides["interpreter"].global_addrs)
        found = cells.cells((8,), offsets=(8,), global_addrs=True)
        self.assertEqual(
            [c for c in found if c.table == "globals"],
            [Cell("globals", "globaladdr", "", "")],
        )
        self.assertFalse(
            any(c.table == "globals" for c in cells.cells((8,), offsets=(8,)))
        )

    def test_the_matrix_shows_the_cell(self):
        self.assertEqual(
            coverage.show(Cell("globals", "globaladdr", "", "")), "globaladdr"
        )


if __name__ == "__main__":
    unittest.main()
