"""Fail when Lean code written for every dialect names the core dialect.

This is G0's source check on the Lean side (ADR-2026-11-03-0600). fir's
spec is written once for every dialect: a dialect's ops reach the spec's
parser, printer, validation and interpreter only through the dialect's
classes, and its `decodeOp` and `opAttrs` hold its text. So the code of
the spec's chapters for every dialect (`lean/Fir/`, but the core dialect's
own `lean/Fir/Core/`) and of what `fir-ref` runs in their place
(`lean/FirRef/`, but its command line) must not:

* import a module of the core dialect or name anything of it: no name with
  a part `Core` or `CoreDialect`, as in `import Fir.Core.Ops`;
* write a word of the core dialect's text as a string: an op name such as
  `"add"`, an attribute such as `"nsw"` or `"true"`, or a type such as
  `"i32"`. The words are those of `lean/Fir/Core/Text.lean`.

The text chapter's example is a core module, so it is not checked. Two
files of the chapter end with the core dialect's corollaries of their
results, so they may name it, but not write its words. Comments and
commands such as `#guard` are not code, so this check skips them.
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CORE_TEXT = "lean/Fir/Core/Text.lean"
# fir-ref's command line runs the core dialect, so it may name it.
FIR_REF_COMMAND_LINE = {"Main", "Report", "Run", "RunArgs", "Sample"}
# The text chapter's example is a module of the core dialect.
CORE_EXAMPLE = "lean/Fir/Text/Example.lean"
# Files that end with the core dialect's corollaries of their results.
NAME_CORE = {"lean/Fir/Text/PrintParse.lean", "lean/Fir/Text/ParseWellFormed.lean"}
# A word of two letters or more: the core dialect's text has none shorter,
# and its file's one-letter strings are value names and symbols.
WORD = re.compile(r"[A-Za-z_][A-Za-z0-9_.]+")
INT_TYPE = re.compile(r"i[0-9]+")
CORE_NAMES = {"Core", "CoreDialect"}


def _ident_start(c: str) -> bool:
    return c.isalpha() or c == "_"


def _ident_char(c: str) -> bool:
    return c.isalnum() or c in "_'!?"


def _char_end(text: str, i: int) -> int | None:
    """Return the index after the char literal at i, or None if none starts
    there. A char literal is a character or an escape between quotes, on one
    line, such as `'x'`, an escaped quote or a Unicode escape."""
    if text.startswith("\\", i + 1):
        end = text.find("'", i + 3, i + 12)
        return None if end < 0 or "\n" in text[i:end] else end + 1
    return i + 3 if text.startswith("'", i + 2) and text[i + 1] != "\n" else None


def tokens(text: str) -> list[tuple[str, str, int]]:
    """Return the code of a Lean source as (kind, text, line) tokens.

    A kind is "str" for a string literal, its text as written between the
    quotes; "name" for an identifier, dotted parts included; and "other"
    for any other character. Comments, char literals, numbers and commands
    that start a line with `#`, with their indented lines, are left out.
    """
    out: list[tuple[str, str, int]] = []
    i, line, n = 0, 1, len(text)
    while i < n:
        c = text[i]
        at_line_start = i == 0 or text[i - 1] == "\n"
        if at_line_start and c == "#" and i + 1 < n and text[i + 1].isalpha():
            while True:
                end = text.find("\n", i)
                if end < 0:
                    i = n
                    break
                line += 1
                i = end + 1
                if i >= n or not text[i].isspace() or text[i] == "\n":
                    break
        elif c == "\n":
            line += 1
            i += 1
        elif c.isspace():
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = n if end < 0 else end
        elif text.startswith("/-", i):
            depth = 0
            while i < n:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                    if depth == 0:
                        break
                else:
                    line += text[i] == "\n"
                    i += 1
        elif c == '"':
            start, i = i + 1, i + 1
            while i < n and text[i] != '"':
                if text[i] == "\\" and i + 1 < n:
                    i += 1
                line += text[i] == "\n"
                i += 1
            out.append(("str", text[start:i], line))
            i += 1
        elif c == "'" and (end := _char_end(text, i)) is not None:
            i = end
        elif c == "«":
            end = text.find("»", i)
            i = n if end < 0 else end + 1
        elif _ident_start(c):
            start = i
            while i < n and (
                _ident_char(text[i])
                or (text[i] == "." and i + 1 < n and _ident_start(text[i + 1]))
            ):
                i += 1
            out.append(("name", text[start:i], line))
        elif c.isdigit():
            while i < n and (text[i].isalnum() or text[i] == "_"):
                i += 1
        else:
            out.append(("other", c, line))
            i += 1
    return out


def core_words(root: Path = ROOT) -> set[str]:
    """Return the words that the core dialect's text writes as strings."""
    text = (root / CORE_TEXT).read_text(encoding="utf-8")
    return {s for kind, s, _ in tokens(text) if kind == "str" and WORD.fullmatch(s)}


def is_generic(rel: str) -> bool:
    """Whether the Lean file at rel, relative to the root, is written for
    every dialect. A new file is, unless it goes in a place that is not."""
    if rel == CORE_EXAMPLE or rel.startswith("lean/Fir/Core/"):
        return False
    if rel.startswith("lean/Fir/") or rel == "lean/FirRef.lean":
        return True
    command_line = {f"lean/FirRef/{m}.lean" for m in FIR_REF_COMMAND_LINE}
    return rel.startswith("lean/FirRef/") and rel not in command_line


def generic_files(root: Path = ROOT) -> list[str]:
    """Return the Lean files written for every dialect, relative to root."""
    found = (p.relative_to(root).as_posix() for p in (root / "lean").rglob("*.lean"))
    return sorted(rel for rel in found if is_generic(rel))


def problems(root: Path = ROOT) -> list[str]:
    """Return one message per place where generic code names the core dialect."""
    words = core_words(root)
    if not words:
        return [f"{CORE_TEXT}: no words found, so nothing would be checked"]
    found = []
    for rel in generic_files(root):
        toks = tokens((root / rel).read_text(encoding="utf-8"))
        for k, (kind, s, line) in enumerate(toks):
            if (
                kind == "name"
                and rel not in NAME_CORE
                and CORE_NAMES & set(s.split("."))
            ):
                verb = "imports" if k > 0 and toks[k - 1][1] == "import" else "names"
                found.append(f"{rel}:{line}: {verb} the core dialect: {s}")
            elif kind == "str" and (s in words or INT_TYPE.fullmatch(s)):
                found.append(f'{rel}:{line}: writes the core dialect\'s word "{s}"')
    return found


def main() -> int:
    found = problems()
    if not found:
        return 0
    print(
        "Lean code written for every dialect names the core dialect"
        " (G0, ADR-2026-11-03-0600):",
        file=sys.stderr,
    )
    for message in found:
        print(f"  {message}", file=sys.stderr)
    print(
        "\nMove the core dialect's part into lean/Fir/Core/, and give the"
        " generic code what it needs\nthrough the dialect's classes, such as"
        " DialectText's decodeOp and opAttrs.",
        file=sys.stderr,
    )
    return 1


if __name__ == "__main__":
    sys.exit(main())
