"""The cells of the coverage matrix (ADR-2026-11-03-0557).

The cell set follows the core dialect's op instances, `Op` in
`lean/Fir/Core/Ops.lean`, as `lean/Fir/Core/Text.lean` writes them: an op,
its flag set or predicate, and its width. `add`, `sub` and `mul` take the
flag sets of `decodeWrap`, `sdiv` and `udiv` those of `decodeExact`, and
`icmp` each predicate of `Pred.all`. A constant's value and a callee are
attributes but not cells, and the other ops have no attributes. A flag or
predicate that the spec does not give an op is not a cell. `poison`, which
has neither operands nor attributes, is a cell at each width of its result
(ADR-2026-11-03-0557).

- An op at a width is a cell for each width of the matrix's side.
- A width change, `zext`, `sext` or `trunc`, is a cell for each pair of
  widths from `iM` to `iN` that the spec allows: `M < N`, or `N < M` for
  `trunc`.
- A float constant, `fcmp` with each predicate of `FPred.all`, and each
  op of float arithmetic, `fadd`, `fsub`, `fmul`, `fdiv`, `sqrt` and `fma`
  with `round(rne)` and `frem`, `fmod`, `fneg` and `fabs` with no
  attribute, is a cell at each float format of the matrix's side: `f32`
  and `f64` for differential tests, which the backend lowers, and `f16`,
  `bf16`, `f32`, `f64` and `f128` for interpreter-only tests (#229, #310,
  ADR-2026-11-03-0557).
- Each of those ops but the constant has a cell for each fast-math flag,
  `nnan`, `ninf` and `nsz`, at each float format of the side: an op that
  carries flags exercises the cell of each flag it carries, and not the
  cell of the op without flags. A float op counts per flag, where an
  integer op counts per flag set, by the human's ruling of 2026-11-13 on
  #355 (#242, ADR-2026-11-03-0557). `contract` and `reassoc` are not cells,
  since validation rejects them.
- A conversion is a cell for each pair of types it converts between at
  the side's float formats: `bitcast` from each format to the integer of
  its width, and from that integer to the format (#241); `sitofp` and
  `uitofp`, with `round(rne)`, from each width of the side to each of its
  float formats (#241); `fpext`, with no attribute, and `fptrunc`, with
  `round(rne)`, from each float format of the side to each other that it
  takes: `fpext` to a format with at least as many exponent bits and as
  many mantissa bits, and `fptrunc` to every other (#241, the human's
  ruling of 2026-11-12 on #354); `fptosi` and `fptoui`, with no attribute,
  from each float format of the side to each of its widths (#241).
- The pointer offset `ptradd` is a cell for each width of its integer, and
  the stack allocation `alloca` for each width of the integer type it
  allocates, whatever its kind, count and alignment, at the side's pointer
  widths: every width for interpreter-only tests, and none yet for
  differential tests, since the backend does not lower pointers until
  stage 5 of #231.
- `br`, and each successor of `cond_br`, passes nothing, or values of a
  width or float format. `ret` returns no value, one, or several; a `call`
  gives no result, one, or several; and so does the function that a test
  runs, `func`. One value or several are cells at each width and float
  format of the side (ADR-2026-11-03-0557). `unreachable` passes nothing,
  so it is one cell.
"""

from typing import NamedTuple

from firtext import Op
from refine import bits_of, float_format

DIFFERENTIAL = (1, 8, 16, 32, 64, 128)
INTERPRETER = (1, 7, 8, 16, 32, 33, 64, 128)
FLOAT_DIFFERENTIAL = ("f32", "f64")
FLOAT_INTERPRETER = ("f16", "bf16", "f32", "f64", "f128")
# The widths of `ptradd`'s integer and of `alloca`'s type on each side
# (#231).
POINTER_DIFFERENTIAL: tuple[int, ...] = ()
POINTER_INTERPRETER = INTERPRETER

WRAP = ("", "nuw", "nsw", "nuw nsw")
EXACT = ("", "exact")
PREDS = ("eq", "ne", "slt", "sle", "sgt", "sge", "ult", "ule", "ugt", "uge")
FPREDS = (
    "oeq",
    "one",
    "olt",
    "ole",
    "ogt",
    "oge",
    "ord",
    "ueq",
    "une",
    "ult",
    "ule",
    "ugt",
    "uge",
    "uno",
)

# The ops at a width, in the order of `Op`, with the attributes that are
# cells: a flag set or a predicate.
AT_WIDTH = {
    "const": ("",),
    "add": WRAP,
    "sub": WRAP,
    "mul": WRAP,
    "sdiv": EXACT,
    "udiv": EXACT,
    "srem": ("",),
    "urem": ("",),
    "and": ("",),
    "or": ("",),
    "xor": ("",),
    "shl": ("",),
    "lshr": ("",),
    "ashr": ("",),
    "icmp": PREDS,
    "select": ("",),
    "freeze": ("",),
    "poison": ("",),
}
# The attribute of a float op that rounds (`roundAttr`).
ROUND = ("round(rne)",)
# The float ops at a format, in the order of `Op`, with the attributes
# that are cells.
AT_FORMAT = {
    "const": ("",),
    "fcmp": FPREDS,
    "fadd": ROUND,
    "fsub": ROUND,
    "fmul": ROUND,
    "fdiv": ROUND,
    "frem": ("",),
    "fmod": ("",),
    "fneg": ("",),
    "fabs": ("",),
    "sqrt": ROUND,
    "fma": ROUND,
}
# The fast-math flags, in the order the text writes them (`FastMath.attrs`):
# each of the first three is a cell of every float op but the constant, and
# validation rejects the reserved words (#242).
FAST_MATH = ("nnan", "ninf", "nsz")
RESERVED = ("contract", "reassoc")
FLAGGED = tuple(op for op in AT_FORMAT if op != "const")
# The rows of the float ops: each op's attributes, then a row for each flag.
FLOAT_ROWS = {
    op: attrs + (FAST_MATH if op in FLAGGED else ()) for op, attrs in AT_FORMAT.items()
}
CASTS = ("zext", "sext", "trunc")
# The conversions between a float and another type, which have no
# attributes: a cell for each pair of types, at the side's float formats.
CONVERSIONS = ("bitcast",)
# The conversions from an integer to a float, which carry `round(rne)`: a
# cell for each width and float format of the side.
INT_TO_FLOAT = ("sitofp", "uitofp")
# The conversions between float formats: `fpext`, which has no attribute,
# and `fptrunc`, which carries `round(rne)`. A cell for each ordered pair of
# two float formats of the side that the op takes.
FLOAT_CONVERSIONS = {"fpext": ("",), "fptrunc": ROUND}
# The conversions from a float to an integer, which have no attributes: a
# cell for each float format and width of the side.
FLOAT_TO_INT = ("fptosi", "fptoui")
# The pointer ops: the pointer offset, which has no attributes, a cell for
# each width of its integer, and the stack allocation, a cell for each width
# of the integer type it allocates, at the side's pointer widths.
POINTER_OPS = ("ptradd", "alloca")
NOTHING, PASSED, ONE, SEVERAL = "nothing", "values", "one", "several"
# The rows of passed and returned values: an op, and what it passes,
# returns or gives.
VALUES = (
    ("br", (NOTHING, PASSED)),
    ("cond_br", (NOTHING, PASSED)),
    ("ret", (NOTHING, ONE, SEVERAL)),
    ("unreachable", (NOTHING,)),
    ("call", (NOTHING, ONE, SEVERAL)),
    ("func", (NOTHING, ONE, SEVERAL)),
)
OPS = (
    *AT_WIDTH,
    *FLAGGED,
    *CASTS,
    *CONVERSIONS,
    *INT_TO_FLOAT,
    *FLOAT_CONVERSIONS,
    *FLOAT_TO_INT,
    *POINTER_OPS,
    *(op for op, _ in VALUES if op != "func"),
)


class Cell(NamedTuple):
    """`table` is `ops`, `floats`, `casts`, `conversions`, `pointers` or
    `values`.
    `row` is a flag set or predicate, the source type of a width change or a
    conversion, or what a value row passes, and empty for a pointer op;
    `width` is a width, a float format, the result type of a width change
    or a conversion, the width of a pointer offset's integer or of the
    integer an `alloca` allocates, or empty where nothing is passed."""

    table: str
    op: str
    row: str
    width: str


class CellError(Exception):
    pass


def ty(w: int) -> str:
    return f"i{w}"


class Row(NamedTuple):
    """A labelled row; `None` entries are not cells, even at a zero count."""

    op: str
    key: str
    entries: tuple[Cell | None, ...]


class Table(NamedTuple):
    """An ordered matrix section, with one entry per column in every row.

    `kind` distinguishes display sections, including the four conversion
    sections whose cells all have table `conversions`. Columns are type
    names; the empty name is the scalar or no-value column.
    """

    kind: str
    columns: tuple[str, ...]
    rows: tuple[Row, ...]


def catalog(
    widths: tuple[int, ...],
    formats: tuple[str, ...] = (),
    offsets: tuple[int, ...] = (),
) -> tuple[Table, ...]:
    """One side's taxonomy, expanded once for enumeration and display.

    Rows retain their labels even with no applicable cells. Traversing
    tables, rows and non-None entries preserves the cell order used in gap
    diagnostics. Presentation consumes these keys, never reconstructs them.
    """
    integers = tuple(map(ty, widths))
    tables = []
    for kind, ops, columns in (
        ("ops", AT_WIDTH, integers),
        ("floats", FLOAT_ROWS, formats),
    ):
        tables.append(
            Table(
                kind,
                columns,
                tuple(
                    Row(op, a, tuple(Cell(kind, op, a, t) for t in columns))
                    for op, attrs in ops.items()
                    for a in attrs
                ),
            )
        )
    tables.extend(
        [
            Table(
                "casts",
                integers,
                tuple(
                    Row(
                        op,
                        ty(m),
                        tuple(
                            Cell("casts", op, ty(m), ty(n))
                            if allowed(op, m, n)
                            else None
                            for n in widths
                        ),
                    )
                    for op in CASTS
                    for m in widths
                ),
            ),
            Table(
                "bitcasts",
                ("",),
                tuple(
                    Row("bitcast", a, (Cell("conversions", "bitcast", a, b),))
                    for f in formats
                    for a, b in ((f, bits_type(f)), (bits_type(f), f))
                ),
            ),
            Table(
                "int_to_float",
                formats,
                tuple(
                    Row(op, a, tuple(Cell("conversions", op, a, b) for b in formats))
                    for op in INT_TO_FLOAT
                    for a in integers
                ),
            ),
            Table(
                "float_conversions",
                formats,
                tuple(
                    Row(
                        "",
                        a,
                        tuple(
                            Cell("conversions", conversion(a, b), a, b)
                            if a != b
                            else None
                            for b in formats
                        ),
                    )
                    for a in formats
                ),
            ),
            Table(
                "float_to_int",
                integers,
                tuple(
                    Row(op, a, tuple(Cell("conversions", op, a, b) for b in integers))
                    for op in FLOAT_TO_INT
                    for a in formats
                ),
            ),
        ]
    )
    if offsets:
        columns = tuple(map(ty, offsets))
        tables.append(
            Table(
                "pointers",
                columns,
                tuple(
                    Row(op, "", tuple(Cell("pointers", op, "", t) for t in columns))
                    for op in POINTER_OPS
                ),
            )
        )
    columns = ("", *integers, *formats)
    tables.append(
        Table(
            "values",
            columns,
            tuple(
                Row(
                    op,
                    k,
                    tuple(
                        Cell("values", op, k, t)
                        if (k == NOTHING) == (t == "")
                        else None
                        for t in columns
                    ),
                )
                for op, kinds in VALUES
                for k in kinds
            ),
        )
    )
    return tuple(tables)


def cells(
    widths: tuple[int, ...],
    formats: tuple[str, ...] = (),
    offsets: tuple[int, ...] = (),
) -> list[Cell]:
    """Every actual cell of one side, in catalog order."""
    return [
        cell
        for table in catalog(widths, formats, offsets)
        for row in table.rows
        for cell in row.entries
        if cell is not None
    ]


def float_flags(op: Op) -> tuple[tuple[str, ...], str]:
    """The fast-math flags at the front of a float op's attributes, in the
    order `splitFlags` reads them, and its other attributes. A reserved word,
    or a flag out of order or twice, is not a cell."""
    flags, rest = [], list(op.attrs)
    order = (*FAST_MATH, *RESERVED)
    while rest and rest[0] in order:
        if flags and order.index(rest[0]) <= order.index(flags[-1]):
            raise CellError(f"{op.name} {' '.join(op.attrs)} is not a cell")
        flags.append(rest.pop(0))
    if any(f in RESERVED for f in flags):
        raise CellError(f"{op.name} {' '.join(flags)} is not valid, so not a cell")
    return tuple(flags), " ".join(rest)


def is_float(t: str) -> bool:
    """Whether `t` is a float type: an alias or `float(e, m)`."""
    b = bits_of(t)
    return b is not None and not b[1]


def is_pointer(t: str) -> bool:
    """Whether `t` is a pointer type: `ptr` or `ptr(N)`."""
    return t == "ptr" or (t.startswith("ptr(") and t.endswith(")"))


def bits_type(f: str) -> str:
    """The integer type of the width of the float type `f`."""
    return ty(bits_of(f)[0])


def allowed(op: str, m: int, n: int) -> bool:
    """Whether the spec has the width change `op` from `iM` to `iN`."""
    return n < m if op == "trunc" else m < n


def conversion(a: str, b: str) -> str:
    """The op that converts from the float format `a` to another, `b`:
    `fpext` when `b` holds every value of `a`, with at least as many
    exponent bits and as many mantissa bits, and `fptrunc` otherwise."""
    (e, m), (e2, m2) = float_format(a), float_format(b)
    return "fpext" if e <= e2 and m <= m2 else "fptrunc"


def bitcast(op: Op) -> Cell:
    """The cell of a `bitcast`: from a float to the integer of its width, or
    back. Any other text of it does not decode, so it is not a cell."""
    if not op.attrs and len(op.operands) == len(op.results) == 1:
        [a], [b] = op.operands, op.results
        for f, i in ((a, b), (b, a)):
            if is_float(f) and bits_of(i) == (bits_of(f)[0], True):
                return Cell("conversions", "bitcast", a, b)
    raise CellError(f"bitcast from {op.operands} to {op.results} is not a cell")


def int_to_float(op: Op) -> Cell:
    """The cell of a `sitofp` or `uitofp`: from an integer to a float, with
    `round(rne)`. Any other text of it does not decode, so it is not a
    cell."""
    if op.attrs == ROUND and len(op.operands) == len(op.results) == 1:
        [a], [b] = op.operands, op.results
        operand = bits_of(a)
        if operand is not None and operand[1] and is_float(b):
            return Cell("conversions", op.name, a, b)
    raise CellError(
        f"{op.name} {' '.join(op.attrs)} from {op.operands} to {op.results} is not a cell"
    )


def float_conversion(op: Op) -> Cell:
    """The cell of an `fpext` or `fptrunc`: from a float format to another
    that the op takes, with its attribute. Any other text of it does not
    decode or validate, so it is not a cell."""
    attr = " ".join(op.attrs)
    if attr in FLOAT_CONVERSIONS[op.name] and len(op.operands) == len(op.results) == 1:
        [a], [b] = op.operands, op.results
        if is_float(a) and is_float(b) and a != b and conversion(a, b) == op.name:
            return Cell("conversions", op.name, a, b)
    raise CellError(
        f"{op.name} {attr} from {op.operands} to {op.results} is not a cell"
    )


def float_to_int(op: Op) -> Cell:
    """The cell of an `fptosi` or `fptoui`: from a float to an integer, with
    no attribute. Any other text of it does not decode, so it is not a
    cell."""
    if not op.attrs and len(op.operands) == len(op.results) == 1:
        [a], [b] = op.operands, op.results
        result = bits_of(b)
        if is_float(a) and result is not None and result[1]:
            return Cell("conversions", op.name, a, b)
    raise CellError(
        f"{op.name} {' '.join(op.attrs)} from {op.operands} to {op.results} is not a cell"
    )


def pointer_offset(op: Op) -> Cell:
    """The cell of a `ptradd`: at the width of its integer. Any other text
    of it does not decode, so it is not a cell."""
    if not op.attrs and len(op.operands) == 2 and op.results == op.operands[:1]:
        pointer, offset = op.operands
        bits = bits_of(offset)
        if is_pointer(pointer) and bits is not None and bits[1]:
            return Cell("pointers", op.name, "", offset)
    raise CellError(f"{op.name} of {op.operands} to {op.results} is not a cell")


def stack_allocation(op: Op) -> Cell:
    """The cell of an `alloca`: at the width of the integer type it
    allocates, its second attribute after its kind. Its count and alignment
    are not part of its cell, as a constant's value is not. The matrix
    reads canonical modules, which both tools decode, so the rest of its
    attributes needs no check here."""
    if len(op.attrs) >= 2 and not op.operands and len(op.results) == 1:
        element = op.attrs[1]
        bits = bits_of(element)
        if is_pointer(op.results[0]) and bits is not None and bits[1]:
            return Cell("pointers", op.name, "", element)
    raise CellError(f"{op.name} {' '.join(op.attrs)} to {op.results} is not a cell")


def results(op: str, types: tuple[str, ...]) -> set[Cell]:
    """The cells of values that `op` passes, returns or gives."""
    if not types:
        return {Cell("values", op, NOTHING, "")}
    if op in ("br", "cond_br"):
        row = PASSED
    else:
        row = ONE if len(types) == 1 else SEVERAL
    return {Cell("values", op, row, t) for t in types}


def of_op(op: Op) -> set[Cell]:
    """The cells that an op exercises, at any width. An op that the core
    dialect does not have, or an attribute that is not a cell, is an
    error."""
    if op.name == "bitcast":
        return {bitcast(op)}
    if op.name in INT_TO_FLOAT:
        return {int_to_float(op)}
    if op.name in FLOAT_CONVERSIONS:
        return {float_conversion(op)}
    if op.name in FLOAT_TO_INT:
        return {float_to_int(op)}
    if op.name == "alloca":
        return {stack_allocation(op)}
    if op.name in POINTER_OPS:
        return {pointer_offset(op)}
    if op.name in AT_FORMAT and (op.name != "const" or is_float(op.results[0])):
        flags, attr = float_flags(op) if op.name in FLAGGED else ((), "")
        if attr not in AT_FORMAT[op.name]:
            raise CellError(f"{op.name} {attr} is not a cell")
        typed = op.operands if op.name == "fcmp" else op.results
        return {Cell("floats", op.name, a, typed[0]) for a in flags or (attr,)}
    if op.name in AT_WIDTH:
        attr = "" if op.name == "const" else " ".join(op.attrs)
        if attr not in AT_WIDTH[op.name]:
            raise CellError(f"{op.name} {attr} is not a cell")
        typed = op.operands if op.name == "icmp" else op.results
        return {Cell("ops", op.name, attr, typed[0])}
    if op.attrs and op.name != "call":
        raise CellError(f"{op.name} {' '.join(op.attrs)} is not a cell")
    if op.name in CASTS:
        return {Cell("casts", op.name, op.operands[0], op.results[0])}
    if op.name in ("br", "cond_br"):
        return set().union(*(results(op.name, s) for s in op.successors))
    if op.name in ("ret", "unreachable"):
        return results(op.name, op.operands)
    if op.name == "call":
        return results("call", op.results)
    raise CellError(f"{op.name} is not an op of the core dialect")
