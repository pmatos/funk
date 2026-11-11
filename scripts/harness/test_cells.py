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


def decoded_attrs(text: str) -> dict[str, tuple[str, ...]]:
    """The attributes that are cells of each op, as `Op.decode` reads
    them: the arm of an op that reads its attributes with `decodeWrap`,
    `decodeExact` or `Pred.all` takes theirs, and an op of `plainBinOps`,
    or whose arm takes them through `bare`, takes none. A constant's value
    and a callee are not cells, and any other arm is not known."""
    body = definition(text, "Op.decode")
    arms = dict(re.findall(r'\n  \| "(\w+)" =>(.*?)(?=\n  \| |\Z)', body, re.DOTALL))
    for name in re.findall(r'\("(\w+)", \.\w+\)', definition(text, "plainBinOps")):
        arms.setdefault(name, "bare")
    readers = {
        "decodeWrap": cells.WRAP,
        "decodeExact": cells.EXACT,
        "Pred.all": cells.PREDS,
        "FPred.all": cells.FPREDS,
        "bare": ("",),
        "decodeCast": ("",),
    }
    found = {}
    for name, arm in arms.items():
        if name in ("const", "call"):
            found[name] = ("",)
            continue
        read = [
            attrs
            for reader, attrs in readers.items()
            if re.search(rf"\b{re.escape(reader)}", arm)
        ]
        found[name] = read[0] if len(read) == 1 else ("unknown",)
    return found


def flagged_ops(text: str) -> dict[str, set[str]]:
    """The constructors that each arm of `Op.attrs` gives attributes, by
    what the arm writes: the wrap flags, `exact`, a predicate's name, a
    constant or a callee."""
    found: dict[str, set[str]] = {}
    arms = re.findall(r"\n  \| ([._][^=]*)=> (.*)", definition(text, "Op.attrs"))
    for ctors, result in arms:
        found.setdefault(result.strip(), set()).update(re.findall(r"\.(\w+)", ctors))
    return found


class Tests(unittest.TestCase):
    def assert_cells_follow(self, text: str):
        names = re.findall(r'=> "(\w+)"', definition(text, "Op.name"))
        self.assertEqual(sorted(names), sorted(cells.OPS))
        preds = re.findall(r"\.(\w+)", definition(text, "Pred.all").split(":=")[1])
        self.assertEqual(tuple(preds), cells.PREDS)
        fpreds = re.findall(r"\.(\w+)", definition(text, "FPred.all").split(":=")[1])
        self.assertEqual(tuple(fpreds), cells.FPREDS)
        self.assertEqual(attr_lists(definition(text, "decodeWrap")), set(cells.WRAP))
        self.assertEqual(attr_lists(definition(text, "decodeExact")), set(cells.EXACT))
        self.assertIn("bare as", definition(text, "decodeCast"))
        self.assertEqual(
            decoded_attrs(text),
            {
                op: cells.AT_WIDTH.get(op, cells.AT_FORMAT.get(op, ("",)))
                for op in cells.OPS
            },
        )
        flagged = flagged_ops(text)
        self.assertEqual(
            set(flagged),
            {
                "[constAttr w v]",
                "[.float (floatLit e m v)]",
                "[.word p.name]",
                "f.attrs",
                'if e then [.word "exact"] else []',
                "[.sym f]",
                "[]",
            },
        )
        self.assertEqual(flagged["[constAttr w v]"], {"const"})
        self.assertEqual(flagged["[.float (floatLit e m v)]"], {"fconst"})
        self.assertEqual(flagged["[.word p.name]"], {"icmp", "fcmp"})
        self.assertEqual(flagged["f.attrs"], {"add", "sub", "mul"})
        self.assertEqual(flagged['if e then [.word "exact"] else []'], {"sdiv", "udiv"})
        self.assertEqual(flagged["[.sym f]"], {"call"})
        self.assertEqual(flagged["[]"], set())

    def test_the_ops_of_the_core_dialect(self):
        self.assert_cells_follow(TEXT.read_text(encoding="utf-8"))

    def test_a_new_flag_on_an_op_that_had_none(self):
        # `exact` on `lshr`, as LLVM has it: `Op.attrs` writes it, and
        # `Op.decode` reads it with `decodeExact` instead of through
        # `plainBinOps`. Each of the two edits alone fails the check too.
        original = TEXT.read_text(encoding="utf-8")
        to_attrs = (
            "| .sdiv _ e | .udiv _ e =>",
            "| .sdiv _ e | .udiv _ e | .lshr _ e =>",
        )
        to_decode = [
            (
                '  | "select" =>',
                (
                    '  | "lshr" => do pure (.lshr (← binWidth ts rs) (← decodeExact as))\n'
                    '  | "select" =>'
                ),
            ),
            ('("shl", .shl), ("lshr", .lshr), ', '("shl", .shl), '),
        ]
        text = original
        for old, new in [to_attrs, *to_decode]:
            self.assertEqual(text.count(old), 1, old)
            text = text.replace(old, new)
        self.assertEqual(decoded_attrs(text)["lshr"], cells.EXACT)
        self.assertEqual(flagged_ops(text)["f.attrs"], {"add", "sub", "mul"})
        decode_only = original
        for old, new in to_decode:
            decode_only = decode_only.replace(old, new)
        for name, edited in [
            ("both", text),
            ("Op.attrs", original.replace(*to_attrs)),
            ("Op.decode", decode_only),
        ]:
            with self.subTest(edit=name), self.assertRaises(AssertionError):
                self.assert_cells_follow(edited)

    def test_float_ops_are_cells_at_their_format(self):
        cmp = Op("fcmp", ("olt",), ("f64", "f64"), ("i1",), ())
        self.assertEqual(of_op(cmp), {Cell("floats", "fcmp", "olt", "f64")})
        const = Op("const", ("-4194304",), (), ("f32",), ())
        self.assertEqual(of_op(const), {Cell("floats", "const", "", "f32")})
        self.assertEqual(
            of_op(Op("const", ("1",), (), ("i32",), ())),
            {Cell("ops", "const", "", "i32")},
        )
        with self.assertRaises(CellError):
            of_op(Op("fcmp", ("slt",), ("f32", "f32"), ("i1",), ()))
        found = cells.cells((8,), ("f32", "f64"))
        floats = [c for c in found if c.table == "floats"]
        self.assertEqual(len(floats), 2 * (1 + len(cells.FPREDS)))
        self.assertIn(Cell("values", "call", "one", "f32"), found)
        values = [c for c in found if c.table == "values" and c.width]
        self.assertEqual(len(values), 8 * 3)

    def test_the_cell_set(self):
        widths = (1, 8, 128)
        found = cells.cells(widths)
        self.assertEqual(len(found), len(set(found)))
        rows = sum(len(a) for a in cells.AT_WIDTH.values())
        self.assertEqual(rows, 38)
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
        self.assertEqual(len([c for c in values if not c.width]), 6)
        self.assertEqual(len(values), 6 + 8 * 3)

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
        self.assertEqual(
            of_op(Op("poison", (), (), ("i33",), ())),
            {Cell("ops", "poison", "", "i33")},
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
            of_op(Op("unreachable", (), (), (), ())),
            {Cell("values", "unreachable", "nothing", "")},
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
            Op("poison", ("0",), (), ("i8",), ()),
            Op("load", (), ("ptr",), ("i8",), ()),
        ]:
            with self.subTest(op=op), self.assertRaises(CellError):
                of_op(op)


if __name__ == "__main__":
    unittest.main()
