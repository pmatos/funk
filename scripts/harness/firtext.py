"""The functions and ops of a fir module, read from its text, for the
coverage matrix (ADR-2026-11-03-0557).

It reads the grammar of the text-format chapter, `lean/Fir/Text/Grammar.lean`
and `lean/Fir/Text/Lexical.lean`: one production for every op, so the reader
knows no op by name. It keeps what the matrix needs of each op: its name, its
attributes, and the types of its operands, results and successor arguments;
`Function.callees` takes the callee of each `call`. It reads the corpus's
canonical modules, which both tools accept, and so checks no rule of
validation; a text it cannot read is an error.
"""

import re
from dataclasses import dataclass

# A number: an integer, or a float literal with its exponent's sign
# (ADR-2026-11-11-1438). Any name characters after it are read with it.
NUMBER = re.compile(r"-?\d*(?:\.\d+e-\d+)?", re.ASCII)
NAMECHARS = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789_."
PUNCT = "(){},:="


class TextError(Exception):
    pass


@dataclass(frozen=True)
class Token:
    kind: str
    text: str
    line: int


@dataclass(frozen=True)
class Op:
    """One op: `attrs` as written, `operands` and `results` as types, and
    `successors` as the types that each successor passes."""

    name: str
    attrs: tuple[str, ...]
    operands: tuple[str, ...]
    results: tuple[str, ...]
    successors: tuple[tuple[str, ...], ...]


@dataclass(frozen=True)
class Function:
    symbol: str
    params: tuple[str, ...]
    results: tuple[str, ...]
    ops: tuple[Op, ...]

    def callees(self) -> set[str]:
        return {o.attrs[0] for o in self.ops if o.name == "call" and o.attrs}


def tokens(text: str) -> list[Token]:
    """The tokens of a text: `value`, `label`, `symbol`, `locref`, `word`,
    `int`, `string` and punctuation. A symbol keeps its spelling, quoted or
    not, as a test's `func` writes it."""
    out, i, line = [], 0, 1
    while i < len(text):
        c = text[i]
        if c == "\n":
            line += 1
            i += 1
        elif c in " \t":
            i += 1
        elif text.startswith("//", i):
            while i < len(text) and text[i] != "\n":
                i += 1
        elif c == '"':
            end = string_end(text, i, line)
            out.append(Token("string", text[i:end], line))
            i = end
        elif c in "%^@":
            kind, end = sigil(text, i, line)
            out.append(Token(kind, text[i:end], line))
            i = end
        elif text.startswith("->", i):
            out.append(Token("->", "->", line))
            i += 2
        elif c in PUNCT:
            out.append(Token(c, c, line))
            i += 1
        elif c.isascii() and (c.isdigit() or c == "-"):
            end = names_end(text, max(NUMBER.match(text, i).end(), i + 1))
            out.append(Token("int", text[i:end], line))
            i = end
        elif c.isascii() and (c.isalpha() or c == "_"):
            end = names_end(text, i)
            out.append(Token("word", text[i:end], line))
            i = end
        else:
            raise TextError(f"line {line}: cannot read {c!r}")
    return out


def names_end(text: str, i: int) -> int:
    while i < len(text) and text[i] in NAMECHARS:
        i += 1
    return i


def string_end(text: str, i: int, line: int) -> int:
    """The index just past the string that starts at `i`."""
    i += 1
    while i < len(text) and text[i] != '"':
        if text[i] == "\n":
            break
        i += 2 if text[i] == "\\" else 1
    if i >= len(text) or text[i] != '"':
        raise TextError(f"line {line}: a string does not end")
    return i + 1


def sigil(text: str, i: int, line: int) -> tuple[str, int]:
    """The kind and end of a value, label, symbol or location reference."""
    c, j = text[i], i + 1
    if c == "@" and text.startswith('"', j):
        return "symbol", string_end(text, j, line)
    end = names_end(text, j)
    if end == j:
        raise TextError(f"line {line}: {c} names nothing")
    if c == "@":
        return ("locref" if text[j].isdigit() else "symbol"), end
    return ("value" if c == "%" else "label"), end


class Reader:
    def __init__(self, text: str):
        self.toks = tokens(text)
        self.i = 0

    def peek(self) -> Token | None:
        return self.toks[self.i] if self.i < len(self.toks) else None

    def at(self, kind: str) -> bool:
        t = self.peek()
        return t is not None and t.kind == kind

    def take(self, kind: str) -> Token:
        t = self.peek()
        if t is None or t.kind != kind:
            where = "the end" if t is None else f"line {t.line}, {t.text!r}"
            raise TextError(f"{where}: expected {kind}")
        self.i += 1
        return t

    def module(self) -> list[Function]:
        found = self.items()
        self.take("word")
        self.take("{")
        while not self.at("}"):
            self.i += 1
            if self.peek() is None:
                raise TextError("the location table does not end")
        self.take("}")
        if self.peek() is not None:
            raise TextError(f"line {self.peek().line}: text after the location table")
        return found

    def items(self) -> list[Function]:
        """The functions of a symbol table: its dialect set, if it has one,
        its data layout, if it has one, then its items. A nested module's
        functions are in its own table, which no call of this one reaches
        (ADR-2026-11-10-1510), so its body is skipped. The layout says
        nothing that the matrix counts, so its entries are skipped
        (ADR-2026-11-12-1821)."""
        if self.at("word") and self.peek().text == "dialects":
            self.take("word")
            self.take("word")
            while self.at(","):
                self.take(",")
                self.take("word")
        if self.at("word") and self.peek().text == "layout":
            self.take("word")
            self.entry()
            while self.at(","):
                self.take(",")
                self.entry()
        found = []
        while self.at("word") and self.peek().text != "locs":
            if self.peek().text == "module":
                self.nested()
            else:
                found.append(self.item())
        return found

    def entry(self) -> None:
        """Skips an entry of the data layout: a word applied to attributes."""
        self.take("word")
        self.take("(")
        depth = 1
        while depth:
            t = self.peek()
            if t is None:
                raise TextError("an entry of the data layout does not end")
            depth += {"(": 1, ")": -1}.get(t.kind, 0)
            self.i += 1

    def nested(self) -> None:
        self.take("word")
        self.take("symbol")
        self.take("(")
        self.take(")")
        self.take("{")
        depth = 1
        while depth:
            t = self.peek()
            if t is None:
                raise TextError("a nested module does not end")
            depth += {"{": 1, "}": -1}.get(t.kind, 0)
            self.i += 1

    def item(self) -> Function:
        kind = self.take("word")
        if kind.text != "func":
            raise TextError(f"line {kind.line}: an item of kind {kind.text}")
        symbol = self.take("symbol").text
        self.take("(")
        params = () if self.at(")") else self.defs()
        self.take(")")
        results = ()
        if self.at("->"):
            self.take("->")
            results = self.types()
        self.take("{")
        defined, ops = list(params), []
        while self.at("label"):
            self.take("label")
            if self.at("("):
                self.take("(")
                defined += self.defs()
                self.take(")")
            self.take(":")
            while not self.at("label") and not self.at("}"):
                op, made = self.op()
                ops.append(op)
                defined += made
        self.take("}")
        env = dict(defined)
        if len(env) != len(defined):
            raise TextError(f"{symbol} defines a value twice")
        return Function(
            symbol,
            tuple(t for _, t in params),
            results,
            tuple(typed(o, env, symbol) for o in ops),
        )

    def defs(self) -> tuple[tuple[str, str], ...]:
        out = [self.define()]
        while self.at(","):
            self.take(",")
            out.append(self.define())
        return tuple(out)

    def define(self) -> tuple[str, str]:
        name = self.take("value").text
        self.take(":")
        return name, self.type()

    def types(self) -> tuple[str, ...]:
        out = [self.type()]
        while self.at(","):
            self.take(",")
            out.append(self.type())
        return tuple(out)

    def type(self) -> str:
        return self.attr()

    def attr(self) -> str:
        t = self.peek()
        if t is None or t.kind not in ("word", "int", "string", "symbol"):
            raise TextError(f"line {t.line if t else '?'}: expected an attribute")
        self.i += 1
        if t.kind == "word" and self.at("("):
            self.take("(")
            args = []
            while not self.at(")"):
                args.append(self.attr())
                if not self.at(")"):
                    self.take(",")
            self.take(")")
            return f"{t.text}({', '.join(args)})"
        return t.text

    def op(self) -> tuple[Op, tuple[tuple[str, str], ...]]:
        """An op, with its operands and successor arguments as names, and
        the values it defines."""
        made: tuple[tuple[str, str], ...] = ()
        if self.at("value"):
            made = self.defs()
            self.take("=")
        name = self.take("word").text
        attrs = []
        while self.peek() and self.peek().kind in ("word", "int", "string", "symbol"):
            attrs.append(self.attr())
        operands, successors = [], []
        while self.at("value") or self.at("label"):
            if self.at("value"):
                operands.append(self.take("value").text)
            else:
                successors.append(self.successor())
            if self.at(","):
                self.take(",")
        if self.at("{"):
            raise TextError(f"line {self.peek().line}: an op with a region")
        self.take("locref")
        op = Op(
            name,
            tuple(attrs),
            tuple(operands),
            tuple(t for _, t in made),
            tuple(successors),
        )
        return op, made

    def successor(self) -> tuple[str, ...]:
        self.take("label")
        passed = []
        if self.at("("):
            self.take("(")
            passed.append(self.take("value").text)
            while self.at(","):
                self.take(",")
                passed.append(self.take("value").text)
            self.take(")")
        return tuple(passed)


def typed(op: Op, env: dict[str, str], symbol: str) -> Op:
    """`op` with the names of its operands and successor arguments replaced
    by their types."""

    def ty(name: str) -> str:
        if name not in env:
            raise TextError(f"{symbol}: {name} is not defined")
        return env[name]

    return Op(
        op.name,
        op.attrs,
        tuple(ty(v) for v in op.operands),
        op.results,
        tuple(tuple(ty(v) for v in s) for s in op.successors),
    )


def read(text: str) -> dict[str, Function]:
    """The functions of a module's text, by symbol as text writes it."""
    return {f.symbol: f for f in Reader(text).module()}
