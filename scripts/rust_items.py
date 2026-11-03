"""A small reader of Rust source for scripts/check_unsafe_code.py: its
tokens without comments, each string literal one token, and its items,
nested in modules, impls, traits and `verus!` blocks."""

import re
from typing import NamedTuple

ITEM_KINDS = {
    "fn",
    "struct",
    "enum",
    "union",
    "trait",
    "impl",
    "static",
    "const",
    "type",
    "mod",
    "extern",
    "use",
    "macro_rules",
}
# The words that this reader gives a meaning to. `r#unsafe` is an
# identifier, never the keyword, so a raw identifier keeps its `r#` only
# when it spells one of them.
KEYWORDS = ITEM_KINDS | {"unsafe", "as", "for", "dyn", "mut", "async"}
OPEN = {"(": ")", "[": "]", "{": "}"}
TOKEN = re.compile(
    r"""(?P<space>\s+)
    | (?P<line>//[^\n]*)
    | (?P<block>/\*)
    | (?P<raw>(?:br|cr|r)(?P<hashes>\#*)")
    | (?P<str>[bc]?")
    | (?P<char>b?'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F_]*\}|.)|[^\\'\n])')
    | (?P<life>'[A-Za-z_][A-Za-z0-9_]*)
    | (?P<ident>(?:r\#)?[A-Za-z_][A-Za-z0-9_]*)
    | (?P<num>[0-9][A-Za-z0-9_]*)
    | (?P<punct>.)""",
    re.VERBOSE | re.DOTALL,
)


class Item(NamedTuple):
    """Tokens lo to hi of an item. `kind` is an item keyword, `name!` for a
    macro, `inner` for inner attributes, or None. A module, impl, trait or
    `verus!` block is two items, its header and its closing brace, around
    the items it holds."""

    path: str
    kind: str | None
    lo: int
    hi: int
    in_verus: bool


def tokens(text: str) -> list[tuple[str, str, int]]:
    """Rust tokens as (kind, text, line), without comments; a string
    literal is one `str` token that holds its source text, so no word in it
    reads as an identifier. A raw identifier loses its `r#` unless it
    spells a keyword."""
    out = []
    pos, line = 0, 1
    while pos < len(text):
        match = TOKEN.match(text, pos)
        assert match is not None
        kind, end = match.lastgroup, match.end()
        if kind == "hashes":
            kind = "raw"
        if kind == "block":
            depth = 1
            while depth and end < len(text):
                if text.startswith("/*", end):
                    depth, end = depth + 1, end + 2
                elif text.startswith("*/", end):
                    depth, end = depth - 1, end + 2
                else:
                    end += 1
        elif kind == "raw":
            close = '"' + "#" * len(match["hashes"])
            found = text.find(close, end)
            end = len(text) if found < 0 else found + len(close)
            out.append(("str", text[pos:end], line))
        elif kind == "str":
            while end < len(text) and text[end] != '"':
                end += 2 if text[end] == "\\" else 1
            end += 1
            out.append(("str", text[pos:end], line))
        elif kind == "ident":
            word = match.group()
            bare = word.removeprefix("r#")
            out.append((kind, word if bare in KEYWORDS else bare, line))
        elif kind not in ("space", "line"):
            out.append((kind, match.group(), line))
        line += text.count("\n", pos, end)
        pos = end
    return out


def group_end(toks, i: int) -> int:
    """The index just past the bracket group that opens at toks[i]."""
    depth = 0
    for j in range(i, len(toks)):
        text = toks[j][1] if toks[j][0] == "punct" else ""
        if text in OPEN:
            depth += 1
        elif text in OPEN.values():
            depth -= 1
            if depth == 0:
                return j + 1
    return len(toks)


def is_punct(toks, i: int, text: str) -> bool:
    return 0 <= i < len(toks) and toks[i][0] == "punct" and toks[i][1] == text


def is_ident(toks, i: int, text: str) -> bool:
    return 0 <= i < len(toks) and toks[i][0] == "ident" and toks[i][1] == text


def attributes(toks) -> set[int]:
    """The indices of the tokens inside attributes, `#[...]` or `#![...]`."""
    inside = set()
    for i in range(len(toks)):
        if is_punct(toks, i, "#"):
            j = i + 2 if is_punct(toks, i + 1, "!") else i + 1
            if is_punct(toks, j, "["):
                inside.update(range(j, group_end(toks, j)))
    return inside


def skip_attributes(toks, i: int, end: int) -> int:
    while i < end and is_punct(toks, i, "#") and not is_punct(toks, i + 1, "!"):
        i = group_end(toks, i + 1)
    return i


def head(toks, i: int, end: int) -> tuple[str, int] | None:
    """The kind of the item that starts at toks[i] (an item keyword, or
    `name!` for a macro, by path or not), and the index of that token."""
    i = skip_attributes(toks, i, end)
    while i < end:
        kind, text, _ = toks[i]
        if is_punct(toks, i, "("):
            i = group_end(toks, i)
            continue
        if is_punct(toks, i, ":") and is_punct(toks, i + 1, ":"):
            i += 2
            continue
        if kind == "ident" and is_punct(toks, i + 1, "!") and text != "macro_rules":
            return f"{text}!", i
        nxt = toks[i + 1][1] if i + 1 < end else ""
        if text == "const" and nxt in ("fn", "unsafe", "async", "extern"):
            i += 1
            continue
        if kind == "ident" and text in ITEM_KINDS:
            return text, i
        if kind != "ident" and kind != "str":
            return None
        i += 1
    return None


def item_end(toks, i: int, end: int, kind: str | None) -> int:
    """The index just past the item that starts at toks[i]: past its first
    `;`, or past its first brace group unless it is a constant, static,
    type alias or `use`, whose value or path may hold braces."""
    value = kind in ("const", "static", "type", "use")
    i = skip_attributes(toks, i, end)
    while i < end:
        if is_punct(toks, i, ";"):
            return i + 1
        if toks[i][0] == "punct" and toks[i][1] in OPEN:
            brace = toks[i][1] == "{"
            i = group_end(toks, i)
            if brace and not value:
                return i
            continue
        i += 1
    return end


def name_of(toks, kind: str, at: int, end: int) -> str:
    if kind.endswith("!"):
        return kind
    if kind == "extern" and at + 1 < end and toks[at + 1][0] == "str":
        if is_punct(toks, at + 2, "{"):
            close = group_end(toks, at + 2)
            fns = [
                toks[j + 1][1]
                for j in range(at + 2, close - 1)
                if toks[j][1] == "fn" and toks[j + 1][0] == "ident"
            ]
            return "+".join(fns) or "extern"
        found = head(toks, at + 2, end)
        return name_of(toks, *found, end) if found else "extern"
    if kind == "impl":
        body = next((j for j in range(at, end) if is_punct(toks, j, "{")), end)
        idents = [j for j in range(at + 1, body) if toks[j][0] == "ident"]
        after_for = [j for j in idents if toks[j - 1][1] == "for"]
        own = [j for j in idents if toks[j][1] not in ("for", "dyn", "unsafe")]
        target = after_for[-1:] or own[:1]
        return toks[target[0]][1] if target else "impl"
    nxt = at + 1
    while nxt < end and (toks[nxt][1] == "mut" or is_punct(toks, nxt, "!")):
        nxt += 1
    return toks[nxt][1] if nxt < end and toks[nxt][0] == "ident" else kind


def items(toks, start: int, end: int, path: str = "", in_verus: bool = False):
    """Yield an Item for each item between start and end, and for those
    nested in modules, impls, traits and `verus!` blocks. A file's inner
    attributes are the item `<module>`."""
    i = start
    while i < end:
        first = i
        if is_punct(toks, i, "#") and is_punct(toks, i + 1, "!"):
            i = group_end(toks, i + 2)
            yield Item(join(path, "<module>"), "inner", first, i, in_verus)
            continue
        found = head(toks, i, end)
        kind, at = found if found else (None, i)
        i = item_end(toks, i, end, kind)
        name = name_of(toks, kind, at, end) if kind else "<unnamed>"
        body = next((j for j in range(at, i) if is_punct(toks, j, "{")), None)
        nested = kind in ("mod", "impl", "trait", "verus!") and body is not None
        if not nested:
            yield Item(join(path, name), kind, first, i, in_verus)
            continue
        inner = path if kind == "verus!" else join(path, name)
        yield Item(join(path, name), kind, first, body + 1, in_verus)
        yield from items(toks, body + 1, i - 1, inner, in_verus or kind == "verus!")
        yield Item(join(path, name), kind, i - 1, i, in_verus)


def join(path: str, name: str) -> str:
    return f"{path}::{name}" if path else name
