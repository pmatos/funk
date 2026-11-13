"""The matrix's shared cell expansion and its rendered applicability blanks."""

import unittest
from collections import Counter
from unittest.mock import patch

import cells
import coverage
from cells import Cell


class Presentation(unittest.TestCase):
    def test_counts_and_non_cells_stay_distinct_in_every_table(self):
        side = coverage.Side("sample", "Sample", (8, 32), ("f16", "bf16"), (7,))
        counts = Counter(
            {
                Cell("ops", "add", "nuw", "i8"): 2,
                Cell("floats", "fadd", "round(rne)", "f16"): 3,
                Cell("casts", "zext", "i8", "i32"): 4,
                Cell("conversions", "bitcast", "f16", "i16"): 5,
                Cell("conversions", "sitofp", "i8", "f16"): 6,
                Cell("conversions", "fptrunc", "f16", "bf16"): 7,
                Cell("conversions", "fptrunc", "bf16", "f16"): 8,
                Cell("conversions", "fptoui", "bf16", "i32"): 9,
                Cell("pointers", "ptradd", "", "i7"): 10,
                Cell("values", "ret", "nothing", ""): 11,
                Cell("values", "ret", "one", "f16"): 12,
            }
        )
        with patch.object(coverage, "SIDES", (side,)):
            text = coverage.render({"sample": counts})
            gaps = coverage.empty({"sample": counts})
        for row in (
            "| `add` | `nuw` | 2 | **0** |",
            "| `fadd` | `round(rne)` | 3 | **0** |",
            "| `zext` | `i8` |  | 4 |",
            "| `zext` | `i32` |  |  |",
            "| `bitcast` | `f16` | `i16` | 5 |",
            "| `sitofp` | `i8` | 6 | **0** |",
            "| `f16` |  | `fptrunc` 7 |",
            "| `bf16` | `fptrunc` 8 |  |",
            "| `fptoui` | `bf16` | **0** | 9 |",
            "| `ptradd` | 10 |",
            "| `ret` | returns no value | 11 |  |  |  |  |",
            "| `ret` | returns one value |  | **0** | **0** | 12 | **0** |",
        ):
            self.assertIn(row, text)
        self.assertNotIn("sample: zext from i32 to i8", gaps)
        self.assertEqual(
            gaps[:3], ["sample: const i8", "sample: const i32", "sample: add i8"]
        )
        self.assertNotIn("sample: zext from i8 to i32", gaps)
        self.assertNotIn("sample: fpext from f16 to bf16", gaps)
        self.assertNotIn("sample: ret nothing", gaps)

    def test_sides_without_pointer_widths_have_no_pointer_section(self):
        side = coverage.Side("sample", "Sample", (8,), (), ())
        with patch.object(coverage, "SIDES", (side,)):
            text = coverage.render({"sample": Counter()})
        self.assertNotIn("Pointer offsets", text)
        self.assertIn("| `trunc` | `i8` |  |", text)


class Catalog(unittest.TestCase):
    def test_rows_distinguish_uncovered_cells_from_inapplicable_pairs(self):
        tables = {
            table.kind: table for table in cells.catalog((8, 32), ("f16", "bf16"), (7,))
        }
        casts = tables["casts"]
        self.assertEqual(casts.columns, ("i8", "i32"))
        self.assertEqual(
            [(row.key, row.entries) for row in casts.rows if row.op == "zext"],
            [
                ("i8", (None, Cell("casts", "zext", "i8", "i32"))),
                ("i32", (None, None)),
            ],
        )
        conversions = tables["float_conversions"]
        self.assertEqual(
            [row.entries for row in conversions.rows],
            [
                (None, Cell("conversions", "fptrunc", "f16", "bf16")),
                (Cell("conversions", "fptrunc", "bf16", "f16"), None),
            ],
        )
        returns = [row for row in tables["values"].rows if row.op == "ret"]
        self.assertEqual(
            returns[0].entries,
            (Cell("values", "ret", "nothing", ""), None, None, None, None),
        )
        self.assertEqual(
            returns[1].entries,
            (
                None,
                Cell("values", "ret", "one", "i8"),
                Cell("values", "ret", "one", "i32"),
                Cell("values", "ret", "one", "f16"),
                Cell("values", "ret", "one", "bf16"),
            ),
        )
        self.assertEqual(
            tables["pointers"].rows[0].entries,
            (Cell("pointers", "ptradd", "", "i7"),),
        )

    def test_empty_axes_keep_labelled_rows_but_no_typed_cells(self):
        tables = {table.kind: table for table in cells.catalog(())}
        self.assertNotIn("pointers", tables)
        self.assertEqual(tables["ops"].rows[0].op, "const")
        self.assertEqual(tables["ops"].rows[0].entries, ())
        self.assertEqual(
            cells.cells(()),
            [
                Cell("values", op, "nothing", "")
                for op in ("br", "cond_br", "ret", "unreachable", "call", "func")
            ],
        )


if __name__ == "__main__":
    unittest.main()
