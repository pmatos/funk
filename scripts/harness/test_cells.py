"""Tests of the cells of the coverage matrix, and that they follow the core
dialect's ops in Lean."""

import re
import unittest
from pathlib import Path

import cells
from cells import Cell, CellError, of_op, results
from firtext import Op

TEXT = Path(__file__).resolve().parents[2] / "lean" / "Fir" / "Core" / "Text.lean"


def definition(text: str, name: str) -> str:
    """The lines of the Lean definition `name`, up to the next blank line."""
    start = text.index(f"def {name} ")
    end = text.index("\n\n", start)
    return text[start:end]


def attr_lists(body: str) -> set[str]:
    """The attribute lists that a decoder of `Text.lean` accepts, each as
    its words joined by spaces."""
    found = set()
    for words, result in re.findall(r"\| \[([^\]]*)\] => (\w+)", body):
        if result == "some":
            found.add(" ".join(re.findall(r'\.word "(\w+)"', words)))
    return found


class Tests(unittest.TestCase):
    def test_the_ops_of_the_core_dialect(self):
        text = TEXT.read_text(encoding="utf-8")
        names = re.findall(r'=> "(\w+)"', definition(text, "Op.name"))
        self.assertEqual(sorted(names), sorted(cells.OPS))
        preds = re.findall(r"\.(\w+)", definition(text, "Pred.all").split(":=")[1])
        self.assertEqual(tuple(preds), cells.PREDS)
        self.assertEqual(attr_lists(definition(text, "decodeWrap")), set(cells.WRAP))
        self.assertEqual(attr_lists(definition(text, "decodeExact")), set(cells.EXACT))
        for op in ("add", "sub", "mul"):
            self.assertEqual(cells.AT_WIDTH[op], cells.WRAP)
        for op in ("sdiv", "udiv"):
            self.assertEqual(cells.AT_WIDTH[op], cells.EXACT)
        self.assertEqual(cells.AT_WIDTH["icmp"], cells.PREDS)

    def test_the_cell_set(self):
        widths = (1, 8, 128)
        found = cells.cells(widths)
        self.assertEqual(len(found), len(set(found)))
        rows = sum(len(a) for a in cells.AT_WIDTH.values())
        self.assertEqual(rows, 37)
        ops = [c for c in found if c.table == "ops"]
        self.assertEqual(len(ops), rows * 3)
        self.assertNotIn(Cell("ops", "and", "nuw", "i8"), found)
        self.assertNotIn(Cell("ops", "srem", "exact", "i8"), found)
        self.assertIn(Cell("ops", "icmp", "uge", "i128"), found)
        casts = [c for c in found if c.table == "casts"]
        self.assertEqual(
            sorted((c.op, c.row, c.width) for c in casts if c.op == "trunc"),
            [
                ("trunc", "i128", "i1"),
                ("trunc", "i128", "i8"),
                ("trunc", "i8", "i1"),
            ],
        )
        self.assertEqual(len(casts), 9)
        values = [c for c in found if c.table == "values"]
        self.assertEqual(len([c for c in values if not c.width]), 5)
        self.assertEqual(len(values), 5 + 8 * 3)

    def test_the_cells_of_an_op(self):
        self.assertEqual(
            of_op(Op("add", ("nuw", "nsw"), ("i8", "i8"), ("i8",), ())),
            {Cell("ops", "add", "nuw nsw", "i8")},
        )
        self.assertEqual(
            of_op(Op("const", ("-1",), (), ("i33",), ())),
            {Cell("ops", "const", "", "i33")},
        )
        self.assertEqual(
            of_op(Op("icmp", ("ult",), ("i64", "i64"), ("i1",), ())),
            {Cell("ops", "icmp", "ult", "i64")},
        )
        self.assertEqual(
            of_op(Op("select", (), ("i1", "i7", "i7"), ("i7",), ())),
            {Cell("ops", "select", "", "i7")},
        )
        self.assertEqual(
            of_op(Op("sext", (), ("i1",), ("i128",), ())),
            {Cell("casts", "sext", "i1", "i128")},
        )

    def test_passed_and_returned_values(self):
        self.assertEqual(
            of_op(Op("br", (), (), (), ((),))), {Cell("values", "br", "nothing", "")}
        )
        self.assertEqual(
            of_op(Op("cond_br", (), ("i1",), (), (("i8", "i64"), ()))),
            {
                Cell("values", "cond_br", "values", "i8"),
                Cell("values", "cond_br", "values", "i64"),
                Cell("values", "cond_br", "nothing", ""),
            },
        )
        self.assertEqual(
            of_op(Op("ret", (), ("i8",), (), ())), {Cell("values", "ret", "one", "i8")}
        )
        self.assertEqual(
            of_op(Op("call", ("@f",), ("i8",), ("i8", "i128", "i8"), ())),
            {
                Cell("values", "call", "several", "i8"),
                Cell("values", "call", "several", "i128"),
            },
        )
        self.assertEqual(results("func", ()), {Cell("values", "func", "nothing", "")})

    def test_an_op_with_no_cell_is_an_error(self):
        for op in [
            Op("and", ("nuw",), ("i8", "i8"), ("i8",), ()),
            Op("udiv", ("nuw",), ("i8", "i8"), ("i8",), ()),
            Op("icmp", ("lt",), ("i8", "i8"), ("i1",), ()),
            Op("add", ("nsw", "nuw"), ("i8", "i8"), ("i8",), ()),
            Op("zext", ("nuw",), ("i8",), ("i16",), ()),
            Op("ret", ("exact",), ("i8",), (), ()),
            Op("load", (), ("ptr",), ("i8",), ()),
        ]:
            with self.subTest(op=op), self.assertRaises(CellError):
                of_op(op)


if __name__ == "__main__":
    unittest.main()
