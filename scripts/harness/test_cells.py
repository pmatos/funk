"""Tests of the cells of the coverage matrix, and that they follow the core
dialect's ops in Lean."""

import functools
import re
import unittest
from pathlib import Path

import cells
from address_cells import ADDRESS_OPS
from cells import Cell, CellError, of_op, results
from copy_cells import MEM_OPS
from firtext import Op

CORE = Path(__file__).resolve().parents[2] / "lean" / "Fir" / "Core"
TEXT = CORE / "Text.lean"
FLOAT_OP_TEXT = CORE / "FloatOpText.lean"
ROUNDING_TEXT = CORE / "RoundingText.lean"
VALIDATION = CORE / "Validation.lean"
OP_ATTRS = CORE / "OpAttrs.lean"
MEM_COPY_TEXT = CORE / "MemCopyText.lean"


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


@functools.cache
def round_attrs() -> tuple[str, ...]:
    """The rounding attributes that are cells, as the text writes them:
    `roundAttr` of each mode that `Op.Valid` accepts, every other mode
    decoding and failing validation."""
    rounding = ROUNDING_TEXT.read_text(encoding="utf-8")
    head = re.findall(r'\.app "(\w+)"', definition(rounding, "roundAttr"))
    valid = definition(VALIDATION.read_text(encoding="utf-8"), "Op.Valid")
    modes = sorted(set(re.findall(r"\br = \.(\w+)", valid)))
    word = definition(rounding, "RoundingMode.word")
    return tuple(
        f"{h}({w})"
        for h in head
        for m in modes
        for w in re.findall(rf'\| \.{m} => "(\w+)"', word)
    )


def op_attrs(floats: str, kind: str) -> dict[str, tuple[str, ...]]:
    """The attributes that each float op of `kind`, `FBin` or `FUnary`,
    reads by its name in `read`: a mode, of which `round(rne)` is a cell,
    or none."""
    body = definition(floats, f"{kind}.read")
    found = {}
    for name, result in re.findall(r'\n  \| "(\w+)", as => (.*)', body):
        found[name] = round_attrs() if "decodeRound" in result else ("",)
    return found


def decoded_attrs(text: str, floats: str) -> dict[str, tuple[str, ...]]:
    """The attributes that are cells of each op, as `Op.decode` reads
    them: the arm of an op that reads its attributes with `decodeWrap`,
    `decodeExact` or `Pred.all` takes theirs, `fcmp` the predicates of
    `FPred.all` through `decodeFcmp`, a float op of arithmetic
    takes `round(rne)` or none, as `decodeFma`, `FBin.read` and
    `FUnary.read` read them, a conversion from an integer `round(rne)`,
    as `decodeIntToFloat` reads it, `fptrunc` `round(rne)` and `fpext`
    none, as `decodeFptrunc` and `decodeFpext` read them, a conversion to
    an integer none, as `decodeFloatToInt` reads it, and an op of
    `plainBinOps`, or whose arm takes them through `bare`, as
    `decodePtrAdd` does, takes none. A constant's value, a callee and
    what `alloca` reads with `decodeAlloca`, its kind, type, count and
    alignment, are not cells: an allocation's cell is the width of its
    type. Nor are `load`'s and `store`'s ordering and alignment, which
    `decodeLoad` and `decodeStore` read: a load's cell is the width of its
    result, and a store's the width of its value. Nor are the layout and
    field that `decodeFieldAddr` reads for `fieldaddr`: its cell is the
    width of its index. Nor is the symbol that `decodeGlobalAddr` and
    `decodeFuncAddr` read: each address is one cell. Nor is the ordering that `decodeMemCopy` and
    `decodeMemSet` read: a copy's, a move's and a fill's cell is the width
    of its length. `decodePtrExpose` and `decodePtrFromInt` read no
    attributes. Any other arm is not known."""
    body = definition(text, "Op.decode")
    arms = dict(re.findall(r'\n  \| "(\w+)" =>(.*?)(?=\n  \| |\Z)', body, re.DOTALL))
    for name in re.findall(r'\("(\w+)", \.\w+\)', definition(text, "plainBinOps")):
        arms.setdefault(name, "bare")
    readers = {
        "decodeWrap": cells.WRAP,
        "decodeExact": cells.EXACT,
        "Pred.all": cells.PREDS,
        "FPred.all": cells.FPREDS,
        "decodeFcmp": cells.FPREDS,
        "bare": ("",),
        "decodeCast": ("",),
        "decodeFma": round_attrs(),
        "decodeBitcast": ("",),
        "decodeIntToFloat": round_attrs(),
        "decodeFpext": ("",),
        "decodeFptrunc": round_attrs(),
        "decodeFloatToInt": ("",),
        "decodePtrAdd": ("",),
        "decodeAlloca": ("",),
        "decodeLoad": ("",),
        "decodeStore": ("",),
        "decodeMemCopy": ("",),
        "decodeMemSet": ("",),
        "decodeFieldAddr": ("",),
        "decodePtrExpose": ("",),
        "decodePtrFromInt": ("",),
        "decodeGlobalAddr": ("",),
        "decodeFuncAddr": ("",),
    }
    by_ctor = {
        "decodeFBin": op_attrs(floats, "FBin"),
        "decodeFUnary": op_attrs(floats, "FUnary"),
    }
    found = {}
    for name, arm in arms.items():
        if name in ("const", "call"):
            found[name] = ("",)
            continue
        if ctor := re.search(r'(decodeFBin|decodeFUnary) "(\w+)"', arm):
            found[name] = by_ctor[ctor.group(1)].get(ctor.group(2), ("unknown",))
            continue
        read = [
            attrs
            for reader, attrs in readers.items()
            if re.search(rf"\b{re.escape(reader)}", arm)
        ]
        found[name] = read[0] if len(read) == 1 else ("unknown",)
    return found


def fast_math(floats: str, ops: str) -> tuple[tuple[str, ...], tuple[str, ...]]:
    """The words of the fast-math flags in the order `FastMath.attrs` writes
    them, and those that `FastMath.Reserved` names, which validation
    rejects."""
    words = re.findall(r'\.word "(\w+)"', definition(floats, "FastMath.attrs"))
    reserved = re.findall(r"fl\.(\w+)", definition(ops, "FastMath.Reserved"))
    return tuple(words), tuple(reserved)


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
    def assert_cells_follow(self, text: str, floats: str | None = None):
        floats = floats or FLOAT_OP_TEXT.read_text(encoding="utf-8")
        names = re.findall(r'=> "(\w+)"', definition(text, "Op.name"))
        for kind in ("FBin", "FUnary"):
            names += re.findall(r'=> "(\w+)"', definition(floats, f"{kind}.name"))
        names += re.findall(
            r'=> "(\w+)"',
            definition(MEM_COPY_TEXT.read_text(encoding="utf-8"), "CopyKind.name"),
        )
        self.assertEqual(sorted(names), sorted((*cells.OPS, *MEM_OPS, *ADDRESS_OPS)))
        preds = re.findall(r"\.(\w+)", definition(text, "Pred.all").split(":=")[1])
        self.assertEqual(tuple(preds), cells.PREDS)
        fpreds = re.findall(r"\.(\w+)", definition(text, "FPred.all").split(":=")[1])
        self.assertEqual(tuple(fpreds), cells.FPREDS)
        self.assertEqual(attr_lists(definition(text, "decodeWrap")), set(cells.WRAP))
        self.assertEqual(attr_lists(definition(text, "decodeExact")), set(cells.EXACT))
        self.assertIn("bare as", definition(text, "decodeCast"))
        self.assertIn("bare as", definition(text, "decodePtrAdd"))
        self.assertEqual(definition(floats, "decodeBitcast").count("as.isEmpty"), 2)
        self.assertIn("as.isEmpty", definition(floats, "decodeFpext"))
        self.assertIn("as.isEmpty", definition(floats, "decodeFloatToInt"))
        self.assertEqual(
            decoded_attrs(text, floats),
            {
                op: cells.ROUND
                if op in cells.INT_TO_FLOAT
                else cells.FLOAT_CONVERSIONS.get(
                    op, cells.AT_WIDTH.get(op, cells.AT_FORMAT.get(op, ("",)))
                )
                for op in (*cells.OPS, *MEM_OPS, *ADDRESS_OPS)
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
                "fl.attrs ++ [.word p.name]",
                "fl.attrs ++ [roundAttr r]",
                "[roundAttr r]",
                "fl.attrs ++ o.attrs",
                "allocaAttrs k t c a",
                "loadAttrs o a",
                "loadAttrs o none",
                "fieldAddrAttrs s i",
                "globalAddrAttrs s",
                "funcAddrAttrs s",
                "[]",
            },
        )
        self.assertEqual(flagged["[roundAttr r]"], {"sitofp", "uitofp", "fptrunc"})
        self.assertEqual(flagged["fl.attrs ++ [roundAttr r]"], {"fma"})
        self.assertEqual(flagged["fl.attrs ++ o.attrs"], {"fbin", "funary"})
        self.assertEqual(flagged["fl.attrs ++ [.word p.name]"], {"fcmp"})
        words, reserved = fast_math(floats, OP_ATTRS.read_text(encoding="utf-8"))
        self.assertEqual(words, (*cells.FAST_MATH, *cells.RESERVED))
        self.assertEqual(reserved, cells.RESERVED)
        self.assertEqual(round_attrs(), cells.ROUND)
        self.assertEqual(flagged["[constAttr w v]"], {"const"})
        self.assertEqual(flagged["[.float (floatLit e m v)]"], {"fconst"})
        self.assertEqual(flagged["[.word p.name]"], {"icmp"})
        self.assertEqual(flagged["f.attrs"], {"add", "sub", "mul"})
        self.assertEqual(flagged['if e then [.word "exact"] else []'], {"sdiv", "udiv"})
        self.assertEqual(flagged["[.sym f]"], {"call"})
        self.assertEqual(flagged["allocaAttrs k t c a"], {"alloca"})
        self.assertEqual(
            flagged["loadAttrs o a"],
            {"load", "store", "loadPtr", "storePtr", "loadFloat", "storeFloat"},
        )
        self.assertEqual(flagged["loadAttrs o none"], {"memCopy", "memSet"})
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
        floats = FLOAT_OP_TEXT.read_text(encoding="utf-8")
        self.assertEqual(decoded_attrs(text, floats)["lshr"], cells.EXACT)
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
        flags = len(cells.FAST_MATH) * len(cells.FLAGGED)
        self.assertEqual(len(floats), 2 * (1 + len(cells.FPREDS) + 10 + flags))
        add = Op("fadd", ("round(rne)",), ("f32", "f32"), ("f32",), ())
        self.assertEqual(of_op(add), {Cell("floats", "fadd", "round(rne)", "f32")})
        fma = Op("fma", ("round(rne)",), ("bf16",) * 3, ("bf16",), ())
        self.assertEqual(of_op(fma), {Cell("floats", "fma", "round(rne)", "bf16")})
        neg = Op("fneg", (), ("f128",), ("f128",), ())
        self.assertEqual(of_op(neg), {Cell("floats", "fneg", "", "f128")})
        for bad in [
            Op("fadd", (), ("f32", "f32"), ("f32",), ()),
            Op("fadd", ("round(rtz)",), ("f32", "f32"), ("f32",), ()),
            Op("fneg", ("round(rne)",), ("f32",), ("f32",), ()),
        ]:
            with self.subTest(op=bad), self.assertRaises(CellError):
                of_op(bad)
        self.assertIn(Cell("values", "call", "one", "f32"), found)
        values = [c for c in found if c.table == "values" and c.width]
        self.assertEqual(len(values), 8 * 3)

    def test_a_float_op_counts_per_flag(self):
        add = Op("fadd", ("nnan", "nsz", "round(rne)"), ("f32", "f32"), ("f32",), ())
        self.assertEqual(
            of_op(add),
            {
                Cell("floats", "fadd", "nnan", "f32"),
                Cell("floats", "fadd", "nsz", "f32"),
            },
        )
        cmp = Op("fcmp", ("ninf", "olt"), ("f64", "f64"), ("i1",), ())
        self.assertEqual(of_op(cmp), {Cell("floats", "fcmp", "ninf", "f64")})
        rem = Op("frem", ("nsz",), ("f16", "f16"), ("f16",), ())
        self.assertEqual(of_op(rem), {Cell("floats", "frem", "nsz", "f16")})
        found = cells.cells((8,), ("f32",))
        for op in cells.FLAGGED:
            for flag in cells.FAST_MATH:
                self.assertIn(Cell("floats", op, flag, "f32"), found)
        self.assertNotIn(Cell("floats", "const", "nnan", "f32"), found)
        for bad in [
            Op("fadd", ("contract", "round(rne)"), ("f32", "f32"), ("f32",), ()),
            Op("fma", ("nnan", "reassoc", "round(rne)"), ("f32",) * 3, ("f32",), ()),
            Op("fadd", ("nsz", "nnan", "round(rne)"), ("f32", "f32"), ("f32",), ()),
            Op("fneg", ("ninf", "ninf"), ("f32",), ("f32",), ()),
            Op("fadd", ("nnan",), ("f32", "f32"), ("f32",), ()),
            Op("fcmp", ("olt", "nnan"), ("f32", "f32"), ("i1",), ()),
        ]:
            with self.subTest(op=bad), self.assertRaises(CellError):
                of_op(bad)

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
