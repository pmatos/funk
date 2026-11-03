"""The rules of scripts/check_unsafe_code.py on the crate of a verified
module (ADR-2026-11-03-0808).

The rest of a crate with a verified module neither uses vstd nor calls
`verus!`, so verified code can name none of its items, such as `CLOSED`,
and no item outside the module can write them under Verus's eye. No file
of that crate holds an `extern crate`, which could rename a crate, such as
`extern crate self as std;`, and retarget every `std::` path of a pinned
text; it costs nothing, since the 2018 and later editions do not need it.
"""

from rust_items import is_ident, is_punct


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
