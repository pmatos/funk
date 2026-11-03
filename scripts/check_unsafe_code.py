"""Fail on unsafe Rust that Verus does not prove, and on any assumption of a
proof outside the trusted base (ADR-2026-11-03-0808).

Unsafe code may live only in a verified module: a file of VERIFIED_MODULES,
in a crate that opts into Verus, so that the verus-proof hook proves it.
There, `unsafe` may appear inside `verus!`, where Verus checks it, and on the
items of TRUSTED_BASE, which ADR-2026-11-03-0808 lists. Everywhere else it
fails. So do `unsafe_code` in an attribute other than a trusted one, or below
`forbid` in the manifest of a crate with no verified module; an assumption
(`assume`, `admit`, `axiom`, `external_body`, `assume_specification` and
their kin) other than on a trusted item; code that Verus does not see when it
verifies; a verified module whose crate does not opt in; and a trusted item
that is gone. The check reads the Rust files and Cargo manifests that git
tracks, without comments and strings.
"""

import re
import subprocess
import sys
import tomllib
from pathlib import Path

ADR = "docs/adrs/2026-11-03-0808-unsafe-rust-needs-a-verus-proof-with-a-listed-trusted-base.md"

VERIFIED_MODULES = {"crates/funk-start-fds/src/record.rs"}

# Item -> the marks it may carry. `<module>` is the file's inner attributes;
# an extern block is named after the functions it declares.
TRUSTED_BASE = {
    "crates/funk-start-fds/src/record.rs": {
        "<module>": {"unsafe_code"},
        "fcntl": {"unsafe"},
        "getfd": {"external_body", "unsafe"},
        "last_error": {"external_body"},
        "Slots": {"external_body"},
        "take_slots": {"axiom"},
        "store": {"external_body"},
        "RECORD": {"unsafe"},
    },
}

# Words that make Verus assume instead of prove: they count in Verus crates.
ASSUMPTIONS = {"assume", "admit", "axiom", "external"}
ASSUMPTION_PREFIXES = ("assume_", "external_")
# Configurations that differ between Verus's run and cargo's build.
VERUS_CFGS = {"verus_keep_ghost", "verus_only"}
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


def tokens(text: str) -> list[tuple[str, str, int]]:
    """Rust tokens as (kind, text, line), without comments; a string
    literal is one `str` token without its contents."""
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
            out.append(("str", "", line))
        elif kind == "str":
            while end < len(text) and text[end] != '"':
                end += 2 if text[end] == "\\" else 1
            end += 1
            out.append(("str", "", line))
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
    return i < len(toks) and toks[i][0] == "punct" and toks[i][1] == text


def skip_attributes(toks, i: int, end: int) -> int:
    while i < end and is_punct(toks, i, "#") and not is_punct(toks, i + 1, "!"):
        i = group_end(toks, i + 1)
    return i


def head(toks, i: int, end: int) -> tuple[str, int] | None:
    """The kind of the item that starts at toks[i] (an item keyword, or
    `name!` for a macro), and the index of that token."""
    i = skip_attributes(toks, i, end)
    while i < end:
        kind, text, _ = toks[i]
        if is_punct(toks, i, "("):
            i = group_end(toks, i)
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
    `;`, or past its first brace group unless it is a constant, static or
    type alias, whose value may hold braces."""
    value = kind in ("const", "static", "type")
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


def items(toks, start: int, end: int, path: str, in_verus: bool):
    """Yield (item path, first token, end token, inside verus!) for the
    items between start and end, and for those nested in modules, impls,
    traits and `verus!` blocks, whose own tokens are their header and their
    closing brace. A file's inner attributes are the item `<module>`."""
    i = start
    while i < end:
        first = i
        if is_punct(toks, i, "#") and is_punct(toks, i + 1, "!"):
            i = group_end(toks, i + 2)
            yield join(path, "<module>"), first, i, in_verus
            continue
        found = head(toks, i, end)
        kind, at = found if found else (None, i)
        i = item_end(toks, i, end, kind)
        name = name_of(toks, kind, at, end) if kind else "<unnamed>"
        body = next((j for j in range(at, i) if is_punct(toks, j, "{")), None)
        nested = kind in ("mod", "impl", "trait", "verus!") and body is not None
        if not nested:
            yield join(path, name), first, i, in_verus
            continue
        inner = path if kind == "verus!" else join(path, name)
        yield join(path, name), first, body + 1, in_verus
        yield from items(toks, body + 1, i - 1, inner, in_verus or kind == "verus!")
        yield join(path, name), i - 1, i, in_verus


def join(path: str, name: str) -> str:
    return f"{path}::{name}" if path else name


def marks(word: str, verus_crate: bool) -> str | None:
    if word in ("unsafe", "unsafe_code", "cfg", "cfg_attr") or word in VERUS_CFGS:
        return word
    if verus_crate and (word in ASSUMPTIONS or word.startswith(ASSUMPTION_PREFIXES)):
        return word
    return None


def file_problems(path: str, text: str, verus_crate: bool, used: set) -> list[str]:
    toks = tokens(text)
    verified = path in VERIFIED_MODULES
    trusted = TRUSTED_BASE.get(path, {})
    found = []
    for item, lo, hi, in_verus in items(toks, 0, len(toks), "", False):
        for kind, word, line in toks[lo:hi]:
            mark = marks(word, verus_crate) if kind == "ident" else None
            if mark is None or (mark in ("cfg", "cfg_attr") and not verified):
                continue
            if mark in trusted.get(item, ()):
                used.add((path, item, mark))
            elif mark != "unsafe" or not (verified and in_verus):
                found.append(f"{path}:{line}: `{word}` in {item}: {why(mark)}")
    return found


def why(mark: str) -> str:
    if mark in VERUS_CFGS or mark in ("cfg", "cfg_attr"):
        return "Verus would not see the code that it selects"
    if mark in ("unsafe", "unsafe_code"):
        return (
            "unsafe code only inside verus! in a verified module, or on a trusted item"
        )
    return "Verus would assume it without proof; only a trusted item may"


def manifest(root: Path, path: str) -> dict:
    with open(root / path, "rb") as f:
        return tomllib.load(f)


def crate_of(path: str, manifests: list[str]) -> str | None:
    dirs = [m.removesuffix("Cargo.toml") for m in manifests]
    owners = [d for d in dirs if path.startswith(d)]
    return max(owners, key=len) + "Cargo.toml" if owners else None


def is_verus_crate(data: dict) -> bool:
    tables = [data.get(k, {}) for k in ("dependencies", "dev-dependencies")]
    tables += [t.get("dependencies", {}) for t in data.get("target", {}).values()]
    meta = data.get("package", {}).get("metadata", {})
    return "verus" in meta or any("vstd" in t for t in tables)


def opts_in(data: dict) -> bool:
    meta = data.get("package", {}).get("metadata", {}).get("verus", {})
    return meta.get("verify") is True


def lint_level(data: dict) -> str | None:
    for lints in (data.get("lints", {}), data.get("workspace", {}).get("lints", {})):
        level = lints.get("rust", {}).get("unsafe_code")
        if level is not None:
            return level.get("level") if isinstance(level, dict) else level
    return None


def problems(root: Path, rust_files: list[str], manifests: list[str]) -> list[str]:
    """One message per violation in the given repository-relative files."""
    found, used = [], set()
    data = {m: manifest(root, m) for m in manifests}
    verified_crates = {crate_of(m, manifests) for m in VERIFIED_MODULES}
    for path in sorted(rust_files):
        crate = crate_of(path, manifests)
        verus_crate = crate is not None and is_verus_crate(data[crate])
        text = (root / path).read_text(encoding="utf-8")
        found += file_problems(path, text, verus_crate, used)
    for module in sorted(VERIFIED_MODULES):
        crate = crate_of(module, manifests)
        if module in rust_files and (crate is None or not opts_in(data[crate])):
            found.append(
                f"{module}: a verified module, but its crate does not opt into"
                " Verus with [package.metadata.verus] verify = true"
            )
    for path in sorted(manifests):
        level = lint_level(data[path])
        if level not in (None, "forbid") and path not in verified_crates:
            found.append(
                f"{path}: unsafe_code is {level}, not forbid, in a crate with"
                " no verified module"
            )
    for path, trusted in sorted(TRUSTED_BASE.items()):
        for item, allowed in sorted(trusted.items()):
            for mark in sorted(
                allowed - {m for p, i, m in used if (p, i) == (path, item)}
            ):
                found.append(
                    f"{path}: trusted item {item} has no `{mark}`; remove it"
                    " from the trusted base"
                )
    return found


def git(*args: str) -> str:
    return subprocess.run(
        ["git", *args], check=True, capture_output=True, text=True
    ).stdout


def main() -> int:
    root = Path(git("rev-parse", "--show-toplevel").strip())
    files = [f for f in git("-C", str(root), "ls-files", "-z").split("\0") if f]
    rust = [f for f in files if f.endswith(".rs")]
    manifests = [f for f in files if f == "Cargo.toml" or f.endswith("/Cargo.toml")]
    found = problems(root, rust, manifests)
    for message in found:
        print(message, file=sys.stderr)
    if found:
        print(f"\nUnsafe Rust needs a Verus proof; see {ADR}.", file=sys.stderr)
    return 1 if found else 0


if __name__ == "__main__":
    sys.exit(main())
