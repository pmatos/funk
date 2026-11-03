"""The rules of scripts/check_unsafe_code.py on what may be added to a
verified module and to its crate (ADR-2026-11-03-0808).

A pin holds the tokens of a text, not what its names resolve to. A new
item could take a name that a pinned text uses, such as `type int = u8;`
or a `mod core`, and change what that text means while its digest stays
the same. So inside `verus!` a verified module holds only pinned items and
new proof or spec functions, which Verus proves, whose names no pinned
text holds. Outside `verus!` its text is pinned whole.

The rest of a crate with a verified module neither uses vstd nor calls
`verus!`, so Verus can name none of its items, such as `CLOSED`, and no
item outside the module can write them under Verus's eye. No file of that
crate holds an `extern crate`, which could rename a crate, such as
`extern crate self as std;`, and retarget every `std::` path of a pinned
text.
"""

from rust_items import head, is_ident, is_punct, skip_attributes
from unsafe_pins import is_pinned, protected

# The words, before `fn`, of a function that Verus proves and erases.
GHOST_MODES = {"proof", "spec"}


def verus_item_problems(path: str, toks, entries) -> list[str]:
    """Inside `verus!`, each item is pinned or is a proof or spec function
    whose name no pinned text holds."""
    taken = protected(path, toks, entries)
    found, seen = [], set()
    for entry in entries:
        if not entry.in_verus or is_pinned(path, entry.path) or entry.path in seen:
            continue
        seen.add(entry.path)
        name = entry.path.rsplit("::", 1)[-1]
        where = f"{path}:{toks[entry.lo][2]}: {entry.path}"
        if not is_ghost_fn(toks, entry):
            found.append(
                f"{where}: inside verus! a verified module adds only proof or"
                " spec functions; this is not one"
            )
        elif name in taken:
            found.append(
                f"{where}: a pinned text holds the name `{name}`, so a new item"
                " may not take it"
            )
    return found


def is_ghost_fn(toks, entry) -> bool:
    found = head(toks, entry.lo, entry.hi)
    if found is None or found[0] != "fn":
        return False
    start = skip_attributes(toks, entry.lo, entry.hi)
    return any(toks[i][1] in GHOST_MODES for i in range(start, found[1]))


def crate_problems(path: str, toks, verified: bool) -> list[str]:
    """In a crate with a verified module: vstd and `verus!` only in that
    module, and no `extern crate` in any file."""
    found = []
    for i, (kind, word, line) in enumerate(toks):
        if kind != "ident":
            continue
        if word == "extern" and is_ident(toks, i + 1, "crate"):
            found.append(
                f"{path}:{line}: `extern crate` in a crate with a verified module,"
                " where it could rename a crate that a pinned text names"
            )
        uses_verus = word == "vstd" or (word == "verus" and is_punct(toks, i + 1, "!"))
        if uses_verus and not verified:
            found.append(
                f"{path}:{line}: `{word}` outside the verified module of its crate,"
                " which alone uses vstd: Verus could name this file's items"
            )
    return found
