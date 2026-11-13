"""Tests of the cells of the coverage matrix's conversions, between floats
and integers and between formats, and of its pointer offsets."""

import unittest

import cells
from cells import Cell, CellError, of_op
from firtext import Op


class Tests(unittest.TestCase):
    def test_a_bitcast_is_a_cell_for_each_pair_of_types(self):
        found = cells.cells((8,), ("f32", "f128"))
        self.assertEqual(
            {c for c in found if c.op == "bitcast"},
            {
                Cell("conversions", "bitcast", "f32", "i32"),
                Cell("conversions", "bitcast", "i32", "f32"),
                Cell("conversions", "bitcast", "f128", "i128"),
                Cell("conversions", "bitcast", "i128", "f128"),
            },
        )
        to_bits = Op("bitcast", (), ("bf16",), ("i16",), ())
        self.assertEqual(
            of_op(to_bits), {Cell("conversions", "bitcast", "bf16", "i16")}
        )
        of_bits = Op("bitcast", (), ("i64",), ("f64",), ())
        self.assertEqual(of_op(of_bits), {Cell("conversions", "bitcast", "i64", "f64")})
        for bad in [
            Op("bitcast", ("round(rne)",), ("f32",), ("i32",), ()),
            Op("bitcast", (), ("f32",), ("i64",), ()),
            Op("bitcast", (), ("f32",), ("f32",), ()),
            Op("bitcast", (), ("i32",), ("i32",), ()),
            Op("bitcast", (), (), ("i32",), ()),
            Op("bitcast", (), ("f32", "f32"), ("i32",), ()),
        ]:
            with self.subTest(op=bad), self.assertRaises(CellError):
                of_op(bad)

    def test_a_conversion_between_formats_is_a_cell_for_each_pair_it_takes(self):
        found = cells.cells((8,), ("f16", "bf16", "f32"))
        self.assertEqual(
            {c for c in found if c.op in cells.FLOAT_CONVERSIONS},
            {
                Cell("conversions", "fpext", "f16", "f32"),
                Cell("conversions", "fpext", "bf16", "f32"),
                Cell("conversions", "fptrunc", "f32", "f16"),
                Cell("conversions", "fptrunc", "f32", "bf16"),
                Cell("conversions", "fptrunc", "f16", "bf16"),
                Cell("conversions", "fptrunc", "bf16", "f16"),
            },
        )
        ext = Op("fpext", (), ("f32",), ("f64",), ())
        self.assertEqual(of_op(ext), {Cell("conversions", "fpext", "f32", "f64")})
        small = Op("fpext", (), ("float(2, 1)",), ("bf16",), ())
        self.assertEqual(
            of_op(small), {Cell("conversions", "fpext", "float(2, 1)", "bf16")}
        )
        trunc = Op("fptrunc", ("round(rne)",), ("f16",), ("bf16",), ())
        self.assertEqual(of_op(trunc), {Cell("conversions", "fptrunc", "f16", "bf16")})
        for bad in [
            Op("fpext", ("round(rne)",), ("f32",), ("f64",), ()),
            Op("fptrunc", (), ("f64",), ("f32",), ()),
            Op("fpext", (), ("f64",), ("f32",), ()),
            Op("fptrunc", ("round(rne)",), ("f32",), ("f64",), ()),
            Op("fpext", (), ("bf16",), ("f16",), ()),
            Op("fpext", (), ("f32",), ("f32",), ()),
            Op("fpext", (), ("i32",), ("f64",), ()),
        ]:
            with self.subTest(op=bad), self.assertRaises(CellError):
                of_op(bad)

    def test_a_conversion_from_an_integer_is_a_cell_for_each_width_and_format(self):
        found = cells.cells((8, 128), ("f32",))
        self.assertEqual(
            {c for c in found if c.op in cells.INT_TO_FLOAT},
            {
                Cell("conversions", op, w, "f32")
                for op in ("sitofp", "uitofp")
                for w in ("i8", "i128")
            },
        )
        si = Op("sitofp", ("round(rne)",), ("i33",), ("bf16",), ())
        self.assertEqual(of_op(si), {Cell("conversions", "sitofp", "i33", "bf16")})
        ui = Op("uitofp", ("round(rne)",), ("i1",), ("f64",), ())
        self.assertEqual(of_op(ui), {Cell("conversions", "uitofp", "i1", "f64")})
        for bad in [
            Op("sitofp", (), ("i32",), ("f32",), ()),
            Op("sitofp", ("round(rtz)",), ("i32",), ("f32",), ()),
            Op("uitofp", ("round(rne)",), ("f32",), ("f32",), ()),
            Op("uitofp", ("round(rne)",), ("i32",), ("i64",), ()),
            Op("sitofp", ("round(rne)",), ("i32", "i32"), ("f32",), ()),
        ]:
            with self.subTest(op=bad), self.assertRaises(CellError):
                of_op(bad)

    def test_a_conversion_to_an_integer_is_a_cell_for_each_format_and_width(self):
        found = cells.cells((1, 64), ("f64",))
        self.assertEqual(
            {c for c in found if c.op in cells.FLOAT_TO_INT},
            {
                Cell("conversions", op, "f64", w)
                for op in ("fptosi", "fptoui")
                for w in ("i1", "i64")
            },
        )
        si = Op("fptosi", (), ("bf16",), ("i33",), ())
        self.assertEqual(of_op(si), {Cell("conversions", "fptosi", "bf16", "i33")})
        for bad in [
            Op("fptosi", ("round(rne)",), ("f32",), ("i32",), ()),
            Op("fptoui", ("round(rtz)",), ("f32",), ("i32",), ()),
            Op("fptoui", (), ("i32",), ("i32",), ()),
            Op("fptosi", (), ("f32",), ("f64",), ()),
        ]:
            with self.subTest(op=bad), self.assertRaises(CellError):
                of_op(bad)

    def test_a_pointer_offset_is_a_cell_for_each_width_of_its_integer(self):
        found = cells.cells((8, 128), ("f32",), (1, 64))
        self.assertEqual(
            {c for c in found if c.table == "pointers"},
            {Cell("pointers", "ptradd", "", w) for w in ("i1", "i64")},
        )
        self.assertFalse(any(c.table == "pointers" for c in cells.cells((8,))))
        self.assertEqual(cells.POINTER_DIFFERENTIAL, ())
        self.assertEqual(cells.POINTER_INTERPRETER, cells.INTERPRETER)
        for ptr in ("ptr", "ptr(1)"):
            op = Op("ptradd", (), (ptr, "i33"), (ptr,), ())
            self.assertEqual(of_op(op), {Cell("pointers", "ptradd", "", "i33")})
        for bad in [
            Op("ptradd", ("inbounds",), ("ptr", "i64"), ("ptr",), ()),
            Op("ptradd", (), ("ptr", "f32"), ("ptr",), ()),
            Op("ptradd", (), ("ptr", "ptr"), ("ptr",), ()),
            Op("ptradd", (), ("ptr",), ("ptr",), ()),
            Op("ptradd", (), ("ptr", "i64"), (), ()),
            Op("ptradd", (), ("i64", "i64"), ("ptr",), ()),
            Op("ptradd", (), ("ptr", "i64"), ("ptr(1)",), ()),
            Op("ptradd", (), ("ptr", "i64"), ("i64",), ()),
        ]:
            with self.subTest(op=bad), self.assertRaises(CellError):
                of_op(bad)


if __name__ == "__main__":
    unittest.main()
