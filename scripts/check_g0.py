"""Fail when Lean code written for every dialect names the core dialect.

This is G0's source check on the Lean side (ADR-2026-11-03-0600). fir's
spec is written once for every dialect: a dialect's ops reach the spec's
parser, printer, validation and interpreter only through the dialect's
classes, and its `decodeOp` and `opAttrs` hold its text. So the code of
the spec's chapters for every dialect (`lean/Fir/`, but the dialects' own
directories), of what `fir-ref` runs in their place (`lean/FirRef/`, but
its command line) and of G0's Lean tests must not:

* import a module of the core dialect or name anything of it: no name with
  a part `Core` or `CoreDialect`, as in `import Fir.Core.Ops`, and no
  import of a module that this check leaves out, such as the text
  chapter's example;
* write a word of the core dialect's text as a string: an op name such as
  `"add"`, an attribute such as `"nsw"` or `"true"`, or a type such as
  `"i32"`. The words are those of `lean/Fir/Core/Text.lean`.

The text chapter's example is a core module, so it is not checked. Two
files of the chapter end with the core dialect's corollaries of their
results, so they may name it, but not write its words. Comments and
commands such as `#guard` are not code, so this check skips them.

It also checks that `Core.Op.poisonClass` and `Core.Op.effects` list each
op by its constructor, with no case for the rest, so a new core op does not
build until it declares its class and its effects.
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CORE_TEXT = "lean/Fir/Core/Text.lean"
CORE_POISON = "lean/Fir/Core/Poison.lean"
POISON_DEF = "def Op.poisonClass"
CORE_EFFECTS = "lean/Fir/Core/OpEffects.lean"
EFFECTS_DEF = "def Op.effects"
# The dialects' own files. A new dialect's directory is added here, and
# ADR-2026-11-03-0600, which draws the line, is edited in place to match.
DIALECT_DIRS = ("lean/Fir/Core/",)
# fir-ref's command line: its entry point, its reports, and `fir-ref run` and
# its arguments. It runs the core dialect, so it may name it.
FIR_REF_COMMAND_LINE = {"Main", "Report", "Run", "RunArgs"}
# The text chapter's example is a module of the core dialect.
CORE_EXAMPLE = "lean/Fir/Text/Example.lean"
# Files that end with the core dialect's corollaries of their results.
NAME_CORE = {"lean/Fir/Text/PrintParse.lean", "lean/Fir/Text/ParseWellFormed.lean"}
# G0's Lean tests, whose statements must stay generic.
G0_TESTS = {"lean/FirTest/G0.lean", "lean/FirTest/G0Effects.lean"}
# The modules that G0's Lean test is split into, by subject.
G0_TEST_DIR = "lean/FirTest/G0/"
# A word of two letters or more: the core dialect's text has none shorter,
# and its file's one-letter strings are value names and symbols.
WORD = re.compile(r"[A-Za-z_][A-Za-z0-9_.]+")
INT_TYPE = re.compile(r"i[0-9]+")
COMMAND = re.compile(r"#[A-Za-z_][A-Za-z0-9_]*(?=\s|$)")
CORE_NAMES = {"Core", "CoreDialect"}
INTERPOLATED = {"s!", "m!", "f!"}


def _ident_start(c: str) -> bool:
    return c.isalpha() or c == "_" or c == "«"


def _ident_char(c: str) -> bool:
    return c.isalnum() or c in "_'!?"


def _indent(line: str) -> int:
    return len(line) - len(line.lstrip(" \t"))


class _Lexer:
    """The tokens of a Lean source: see `tokens`."""

    def __init__(self, text: str):
        self.text, self.i, self.line = text, 0, 1
        self.out: list[tuple[str, str, int]] = []

    def char_end(self) -> int | None:
        """Return the index after the char literal at i, or None if none
        starts there. A char literal is a character or an escape between
        quotes, on one line, such as `'x'`, an escaped quote or a Unicode
        escape."""
        text, i = self.text, self.i
        if text.startswith("\\", i + 1):
            end = text.find("'", i + 3, i + 12)
            return None if end < 0 or "\n" in text[i:end] else end + 1
        return i + 3 if text.startswith("'", i + 2) and text[i + 1] != "\n" else None

    def command(self) -> bool:
        """Skip a command such as `#guard` that starts its line at i, with
        the lines indented under it, and return whether there was one."""
        text, i = self.text, self.i
        start = text.rfind("\n", 0, i) + 1
        if text[start:i].strip() or not COMMAND.match(text, i):
            return False
        col = i - start
        while True:
            end = text.find("\n", i)
            if end < 0:
                self.i = len(text)
                return True
            stop = text.find("\n", end + 1)
            nxt = text[end + 1 : len(text) if stop < 0 else stop]
            if not nxt.strip() or _indent(nxt) <= col:
                self.i = end
                return True
            self.line += 1
            i = end + 1

    def skip_comment(self) -> None:
        text, depth = self.text, 0
        while self.i < len(text):
            if text.startswith("/-", self.i):
                depth += 1
                self.i += 2
            elif text.startswith("-/", self.i):
                depth -= 1
                self.i += 2
                if depth == 0:
                    return
            else:
                self.line += text[self.i] == "\n"
                self.i += 1

    def string(self, interpolated: bool) -> None:
        """Lex the string whose opening quote is before i. In an
        interpolated string, each piece of text is a string and each `{…}`
        is code."""
        text, start, line = self.text, self.i, self.line
        while self.i < len(text) and text[self.i] != '"':
            if text[self.i] == "\\" and self.i + 1 < len(text):
                self.i += 1
            elif interpolated and text[self.i] == "{":
                if start < self.i:
                    self.out.append(("str", text[start : self.i], line))
                self.i += 1
                self.code(inside_braces=True)
                start, line = self.i, self.line
                continue
            self.line += text[self.i] == "\n"
            self.i += 1
        if start < self.i or not interpolated:
            self.out.append(("str", text[start : self.i], line))
        self.i += 1

    def raw_string(self) -> bool:
        """Lex a raw string, `r"…"` or `r#"…"#`, whose `r` is before i, and
        return whether there was one."""
        text, quote = self.text, self.i
        while text.startswith("#", quote):
            quote += 1
        hashes = quote - self.i
        if not text.startswith('"', quote):
            return False
        close = '"' + "#" * hashes
        end = text.find(close, quote + 1)
        end = len(text) if end < 0 else end
        self.out.append(("str", text[quote + 1 : end], self.line))
        self.line += text.count("\n", quote, end)
        self.i = end + len(close)
        return True

    def name(self) -> None:
        text, start = self.text, self.i
        while True:
            if text.startswith("«", self.i):
                end = text.find("»", self.i)
                self.i = len(text) if end < 0 else end + 1
            while self.i < len(text) and _ident_char(text[self.i]):
                self.i += 1
            nxt = self.i + 1
            if not (text.startswith(".", self.i) and nxt < len(text)):
                break
            if not _ident_start(text[nxt]):
                break
            self.i = nxt
        word = text[start : self.i]
        if word == "r" and self.raw_string():
            return
        self.out.append(("name", word, self.line))
        quote = self.i
        while quote < len(text) and text[quote] in " \t":
            quote += 1
        if word in INTERPOLATED and text.startswith('"', quote):
            self.i = quote + 1
            self.string(interpolated=True)

    def code(self, inside_braces: bool = False) -> None:
        """Lex code up to the end, or up to the `}` that closes an
        interpolation."""
        text, depth = self.text, 0
        while self.i < len(text):
            c = text[self.i]
            if c == "#" and self.command():
                continue
            if c == "\n":
                self.line += 1
                self.i += 1
            elif c.isspace():
                self.i += 1
            elif text.startswith("--", self.i):
                end = text.find("\n", self.i)
                self.i = len(text) if end < 0 else end
            elif text.startswith("/-", self.i):
                self.skip_comment()
            elif c == '"':
                self.i += 1
                self.string(interpolated=False)
            elif c == "'" and (end := self.char_end()) is not None:
                self.i = end
            elif _ident_start(c):
                self.name()
            elif c.isdigit():
                while self.i < len(text) and (
                    text[self.i].isalnum() or text[self.i] == "_"
                ):
                    self.i += 1
            else:
                if inside_braces and c == "}" and depth == 0:
                    self.i += 1
                    return
                depth += (c == "{") - (c == "}")
                self.out.append(("other", c, self.line))
                self.i += 1


def tokens(text: str) -> list[tuple[str, str, int]]:
    """Return the code of a Lean source as (kind, text, line) tokens.

    A kind is "str" for a string literal, its text as written between the
    quotes, or each piece of an interpolated string's text; "name" for an
    identifier, dotted parts included; and "other" for any other character.
    Comments, char literals, numbers and commands that start a line with
    `#`, with the lines indented under them, are left out.
    """
    lexer = _Lexer(text)
    lexer.code()
    return lexer.out


def name_parts(name: str) -> list[str]:
    """Return the parts of a dotted name, without `«»`."""
    return [part.strip("«»") for part in name.split(".")]


def core_words(root: Path = ROOT) -> set[str]:
    """Return the words that the core dialect's text writes as strings."""
    text = (root / CORE_TEXT).read_text(encoding="utf-8")
    return {s for kind, s, _ in tokens(text) if kind == "str" and WORD.fullmatch(s)}


def _command_line() -> set[str]:
    return {f"lean/FirRef/{m}.lean" for m in FIR_REF_COMMAND_LINE}


def is_generic(rel: str) -> bool:
    """Whether the Lean file at rel, relative to the root, is written for
    every dialect. A new file is, unless it goes in a place that is not."""
    if rel == CORE_EXAMPLE or rel.startswith(DIALECT_DIRS):
        return False
    if rel.startswith(("lean/Fir/", G0_TEST_DIR)) or rel in {
        "lean/FirRef.lean",
        *G0_TESTS,
    }:
        return True
    return rel.startswith("lean/FirRef/") and rel not in _command_line()


def is_left_out(module: str) -> bool:
    """Whether the module is one of the files that this check leaves out
    because they name the core dialect."""
    rel = "lean/" + module.replace(".", "/") + ".lean"
    return rel == CORE_EXAMPLE or rel.startswith(DIALECT_DIRS) or rel in _command_line()


def generic_files(root: Path = ROOT) -> list[str]:
    """Return the Lean files written for every dialect, relative to root."""
    found = (p.relative_to(root).as_posix() for p in (root / "lean").rglob("*.lean"))
    return sorted(rel for rel in found if is_generic(rel))


def _in_operator(toks: list, k: int) -> bool:
    """Whether the `|` at toks[k] is part of an operator such as `||`, `|>`
    or `<|`, in a value, rather than the start of a case."""
    before = toks[k - 1][1] if k > 0 else ""
    after = toks[k + 1][1] if k + 1 < len(toks) else ""
    return before in ("|", "<") or after in ("|", ">")


def case_problems(root: Path, rel: str, definition: str, what: str) -> list[str]:
    """Return one message per case of the core table `definition` in `rel`
    that is not one op's constructor, such as a case for the rest. `what` is
    what the table gives each op."""
    name = definition.removeprefix("def ")
    lines = (root / rel).read_text(encoding="utf-8").splitlines()
    start = next((k for k, s in enumerate(lines) if s.startswith(definition)), None)
    if start is None:
        return [f"{rel}: no `{definition}`, so no op's {what} is checked"]
    end = start + 1
    while end < len(lines) and lines[end][:1].isspace():
        end += 1
    toks = tokens("\n".join(lines[start:end]))
    found, ops = [], 0
    for k, (kind, s, line) in enumerate(toks):
        if (kind, s) != ("other", "|") or _in_operator(toks, k):
            continue
        head = [t[1] for t in toks[k + 1 : k + 3]]
        if len(head) == 2 and head[0] == "." and toks[k + 2][0] == "name":
            ops += 1
        else:
            found.append(
                f"{rel}:{start + line}: {name} has a case that is not one op's constructor"
            )
    if not ops:
        found.append(f"{rel}:{start + 1}: {name} lists no op")
    return found


def poison_problems(root: Path = ROOT) -> list[str]:
    """Return one message per case of `Core.Op.poisonClass` that is not one
    op's constructor."""
    return case_problems(root, CORE_POISON, POISON_DEF, "class")


def effects_problems(root: Path = ROOT) -> list[str]:
    """Return one message per case of `Core.Op.effects` that is not one op's
    constructor."""
    return case_problems(root, CORE_EFFECTS, EFFECTS_DEF, "effect set")


def problems(root: Path = ROOT) -> list[str]:
    """Return one message per place where generic code names the core dialect."""
    words = core_words(root)
    if not words:
        return [f"{CORE_TEXT}: no words found, so nothing would be checked"]
    found = []
    for rel in generic_files(root):
        toks = tokens((root / rel).read_text(encoding="utf-8"))
        for k, (kind, s, line) in enumerate(toks):
            imported = k > 0 and toks[k - 1][1] == "import"
            parts = name_parts(s)
            if (
                kind == "name"
                and rel not in NAME_CORE
                and parts[0] != "Lean"
                and (CORE_NAMES & set(parts) or (imported and is_left_out(s)))
            ):
                verb = "imports" if imported else "names"
                found.append(f"{rel}:{line}: {verb} the core dialect: {s}")
            elif kind == "str" and (s in words or INT_TYPE.fullmatch(s)):
                found.append(f'{rel}:{line}: writes the core dialect\'s word "{s}"')
    return found + poison_problems(root) + effects_problems(root)


def main() -> int:
    found = problems()
    if not found:
        return 0
    print(
        "Lean code written for every dialect names the core dialect, or a core"
        " op declares no poison class or no effects (G0, ADR-2026-11-03-0600):",
        file=sys.stderr,
    )
    for message in found:
        print(f"  {message}", file=sys.stderr)
    print(
        "\nMove the core dialect's part into lean/Fir/Core/, and give the"
        " generic code what it needs\nthrough the dialect's classes, such as"
        " DialectText's decodeOp and opAttrs. List each core op\nin"
        " Core.Op.poisonClass and Core.Op.effects, with no case for the rest.",
        file=sys.stderr,
    )
    return 1


if __name__ == "__main__":
    sys.exit(main())
