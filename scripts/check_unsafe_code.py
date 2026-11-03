"""Fail on unsafe Rust that Verus does not prove, and on any assumption of a
proof outside the trusted base (ADR-2026-11-03-0808).

Unsafe code may live only in a verified module: a file of VERIFIED_MODULES,
in a crate that opts into Verus, so that the verus-proof hook proves it.
There, `unsafe` may appear only on the items of TRUSTED_BASE, which
ADR-2026-11-03-0808 lists, and the text of the trusted base, of #117's
specification, of `record` and of the file that mounts the module is pinned
(scripts/unsafe_pins.py). Outside `verus!` a verified module holds only
inner attributes, `use`, constants and trusted items; inside it, only
pinned items and new proof or spec functions with fresh names
(scripts/unsafe_items.py). It calls no macro but its `verus!` block and
renames no import, and the names that the proof rests on appear only where
CALLS and NAMES allow. The rest of its crate uses no vstd and no `extern
crate`. The check also fails on `unsafe_code` in an attribute that does
not forbid or deny it; an assumption (`assume`, `admit`, `axiom`,
`external_body`, `assume_specification` and their kin) or a `verifier`
attribute other than on a trusted item; code that Verus does not see when it
verifies; a trusted item that is gone; and a manifest, crate root or Cargo
configuration that would let code past rustc's lint or the check
(scripts/unsafe_manifests.py). It reads the Rust files, Cargo manifests and
Cargo configurations that git tracks, without comments.
"""

import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from rust_items import attributes, is_ident, is_punct, items, tokens
from unsafe_items import crate_problems, verus_item_problems
from unsafe_manifests import (
    config_problems,
    crate_of,
    is_cargo_config,
    is_verus_crate,
    manifest,
    manifest_problems,
    opts_in,
)
from unsafe_pins import pin_problems

ADR = "docs/adrs/2026-11-03-0808-unsafe-rust-needs-a-verus-proof-with-a-listed-trusted-base.md"

# Verified module -> the file whose `mod` item mounts it.
VERIFIED_MODULES = {
    "crates/funk-start-fds/src/record.rs": "crates/funk-start-fds/src/lib.rs",
}

# Item -> the marks it may carry. `<module>` is the file's inner attributes;
# an extern block is named after the functions it declares.
TRUSTED_BASE = {
    "crates/funk-start-fds/src/record.rs": {
        "<module>": {"unsafe_code"},
        "fcntl": {"unsafe"},
        "getfd": {"external_body", "unsafe"},
        "Slots": {"external_body"},
        "take_slots": {"axiom"},
        "store": {"external_body"},
        "RECORD": {"unsafe"},
    },
}

# Function -> the one item that names it, once, besides its own definition;
# a method call, after `.`, does not count. Only `record` takes the view of
# the slots and hands it to `finish`, only `record_slots` stores and asks
# `fcntl`, and `.init_array` holds `record` (ADR-2026-11-03-0808).
CALLS = {
    "crates/funk-start-fds/src/record.rs": {
        "take_slots": "record",
        "finish": "record",
        "record": "RECORD",
        "getfd": "record_slots",
        "store": "record_slots",
    },
}

# Name -> the items that may name it. No other item names `Slots`, so none
# can alias, copy or make the view of the slots.
NAMES = {
    "crates/funk-start-fds/src/record.rs": {
        "Slots": {"Slots", "take_slots", "store", "record_slots", "finish", "record"},
    },
}

# Words that make Verus assume instead of prove: they count in Verus crates.
ASSUMPTIONS = {"assume", "admit", "axiom", "external"}
ASSUMPTION_PREFIXES = ("assume_", "external_")
# The one `verifier` attribute that may stand, on a trusted item.
VERIFIER_ATTRIBUTES = {"external_body"}
# Words that `!(`, `![` or `!{` may follow without calling a macro.
NOT_MACROS = {"if", "while", "match", "return", "break", "in"}
NOT_MACROS |= {"requires", "ensures", "invariant", "decreases", "recommends"}
# The words that may stand in the `mod` item that mounts a verified module.
MOUNT_WORDS = {"mod", "cfg", "any", "target_os"}


def marks(toks, i: int, verus_crate: bool) -> str | None:
    word = toks[i][1]
    if word == "unsafe_code" and strict(toks, i):
        return None
    if word in ("unsafe", "unsafe_code", "cfg", "cfg_attr") or is_verus_cfg(word):
        return word
    if verus_crate and (word in ASSUMPTIONS or word.startswith(ASSUMPTION_PREFIXES)):
        return word
    return None


def strict(toks, i: int) -> bool:
    """toks[i] is a lint in `forbid(...)` or `deny(...)`, which only make
    the rule stricter. Each lint before it is a path, such as
    `clippy::all`."""
    while is_punct(toks, i - 1, ",") and i >= 2 and toks[i - 2][0] == "ident":
        i -= 2
        while is_punct(toks, i - 1, ":") and is_punct(toks, i - 2, ":"):
            if i < 3 or toks[i - 3][0] != "ident":
                return False
            i -= 3
    level = is_ident(toks, i - 2, "forbid") or is_ident(toks, i - 2, "deny")
    return is_punct(toks, i - 1, "(") and level


def is_verus_cfg(word: str) -> bool:
    """Verus sets configurations named `verus_*` that cargo does not."""
    return word.startswith("verus_")


def file_problems(
    path: str, text: str, verus_crate: bool, used: set, verified_crate: bool = False
) -> list[str]:
    toks = tokens(text)
    verified = path in VERIFIED_MODULES
    trusted = TRUSTED_BASE.get(path, {})
    in_attr = attributes(toks)
    found = []
    entries = list(items(toks, 0, len(toks)))
    for item, kind, lo, hi, in_verus in entries:
        for i in range(lo, hi):
            kind_i, word, line = toks[i]
            if kind_i != "ident":
                continue
            where = f"{path}:{line}: `{word}` in {item}"
            if word == "verus" and shadows(toks, i):
                found.append(
                    f"{where}: it shadows vstd's verus!, so Verus would not see the code"
                )
            if verus_crate and reads_a_file(toks, i, in_attr):
                found.append(
                    f"{where}: it takes code from a file that this check may not read"
                )
            if verus_crate and (setting := verifier_setting(toks, i, in_attr)):
                found.append(
                    f"{path}:{line}: `{word}::{setting}` in {item}: of Verus's"
                    " attributes, only `verifier::external_body` may stand, on a"
                    " trusted item"
                )
            top = kind == "verus!" and not in_verus and word == "verus"
            macro = is_macro_call(toks, i) and word not in NOT_MACROS
            if verified and macro and not top:
                found.append(
                    f"{path}:{line}: `{word}!` in {item}: a verified module"
                    " calls no macro but its verus! block"
                )
            mark = marks(toks, i, verus_crate)
            if mark is None or (mark in ("cfg", "cfg_attr") and not verified):
                continue
            if mark in trusted.get(item, ()):
                used.add((path, item, mark))
            else:
                found.append(f"{where}: {why(mark)}")
        if verified:
            found += layout_problems(path, toks, item, kind, lo, hi, in_verus)
    if verified:
        found += verus_item_problems(path, toks, entries)
    if verified_crate:
        found += crate_problems(path, toks, verified)
    found += call_problems(path, toks, entries)
    return found + name_problems(path, toks, entries)


def shadows(toks, i: int) -> bool:
    """`verus` at toks[i] names a macro other than vstd's: `as verus` or
    `macro_rules! verus`."""
    after_rules = is_punct(toks, i - 1, "!") and is_ident(toks, i - 2, "macro_rules")
    return is_ident(toks, i - 1, "as") or after_rules


def reads_a_file(toks, i: int, in_attr: set[int]) -> bool:
    """toks[i] is `include!`, or `path =` in an attribute, such as
    `#[path = "x.txt"] mod m;`."""
    word = toks[i][1]
    if word == "include":
        return is_punct(toks, i + 1, "!")
    return word == "path" and i in in_attr and is_punct(toks, i + 1, "=")


def verifier_setting(toks, i: int, in_attr: set[int]) -> str | None:
    """X, when toks[i] starts `verifier::X` or `verifier(X)` in an attribute,
    other than an allowed one, or Verus's own `verus::X`."""
    if i not in in_attr or toks[i][1] not in ("verifier", "verus"):
        return None
    if is_punct(toks, i + 1, ":") and is_punct(toks, i + 2, ":"):
        at = i + 3
    elif is_punct(toks, i + 1, "(") and toks[i][1] == "verifier":
        at = i + 2
    else:
        return None
    setting = toks[at][1] if at < len(toks) else "?"
    if toks[i][1] == "verifier" and setting in VERIFIER_ATTRIBUTES:
        return None
    return setting


def layout_problems(path, toks, item, kind, lo, hi, in_verus) -> list[str]:
    """Outside `verus!`, a verified module holds only inner attributes,
    `use`, constants and trusted items. It defines no macro, since Verus and
    this check do not see what one makes, and renames no import, so no macro
    passes for a keyword."""
    line = toks[lo][2]
    if kind == "macro_rules":
        return [
            f"{path}:{line}: `macro_rules` in {item}: no macro in a verified module"
        ]
    if kind == "use" and any(is_ident(toks, i, "as") for i in range(lo, hi)):
        return [f"{path}:{line}: `as` in {item}: a verified module renames no import"]
    if in_verus or kind in ("inner", "use", "const", "verus!"):
        return []
    if item in TRUSTED_BASE.get(path, {}):
        return []
    return [
        (
            f"{path}:{line}: {item} sits outside verus! in a verified module, where"
            " only inner attributes, `use`, constants and trusted items may"
        )
    ]


def is_macro_call(toks, i: int) -> bool:
    opens = any(is_punct(toks, i + 2, b) for b in "([{")
    return toks[i][0] == "ident" and is_punct(toks, i + 1, "!") and opens


def named(toks, entry, name: str) -> int:
    """How often `entry` names `name`, other than as a method after `.`."""
    return sum(
        1
        for i in range(entry.lo, entry.hi)
        if is_ident(toks, i, name) and not is_punct(toks, i - 1, ".")
    )


def call_problems(path: str, toks, entries) -> list[str]:
    found = []
    for callee, caller in CALLS.get(path, {}).items():
        counts: dict[str, int] = {}
        for entry in entries:
            counts[entry.path] = counts.get(entry.path, 0) + named(toks, entry, callee)
        if counts.pop(callee, 0) != 1:
            found.append(f"{path}: {callee} must be defined once, by that name")
        if (here := counts.pop(caller, 0)) != 1:
            found.append(f"{path}: {caller} names {callee} {here} times, not once")
        for item in sorted(i for i, n in counts.items() if n):
            found.append(
                f"{path}: `{callee}` in {item}: only {caller} may name it ({ADR})"
            )
    return found


def name_problems(path: str, toks, entries) -> list[str]:
    found = []
    for name, allowed in NAMES.get(path, {}).items():
        for entry in entries:
            if entry.path.split("::")[0] not in allowed and named(toks, entry, name):
                found.append(
                    f"{path}:{toks[entry.lo][2]}: `{name}` in {entry.path}: only"
                    f" {', '.join(sorted(allowed))} may name it ({ADR})"
                )
    return found


def mount_problems(root: Path, module: str, mount: str, rust_files: list[str]):
    """The verified module is mounted once, by `mod <name>;`, and only a
    `target_os` cfg may select it: Verus and cargo then build the same code."""
    name = Path(module).stem
    toks, mounts = [], []
    if mount in rust_files:
        toks = tokens((root / mount).read_text(encoding="utf-8"))
        mounts = [e for e in items(toks, 0, len(toks)) if e.kind == "mod"]
        mounts = [e for e in mounts if e.path == name]
    if len(mounts) != 1 or not is_punct(toks, mounts[0].hi - 1, ";"):
        return [
            f"{mount}: must mount the verified module {module} once, by `mod {name};`"
        ]
    lo, hi = mounts[0].lo, mounts[0].hi
    return [
        f"{mount}:{toks[i][2]}: `{toks[i][1]}` on `mod {name}`: only a target_os"
        " cfg may select a verified module"
        for i in range(lo, hi)
        if toks[i][0] == "ident" and toks[i][1] not in MOUNT_WORDS | {name}
    ]


def why(mark: str) -> str:
    if is_verus_cfg(mark) or mark in ("cfg", "cfg_attr"):
        return "Verus would not see the code that it selects"
    if mark in ("unsafe", "unsafe_code"):
        return "unsafe code only on a trusted item of a verified module"
    return "Verus would assume it without proof; only a trusted item may"


def problems(
    root: Path, rust_files: list[str], manifests: list[str], configs=()
) -> list[str]:
    """One message per violation in the given repository-relative files:
    Rust files, Cargo manifests and Cargo configurations."""
    found, used = [], set()
    data = {m: manifest(root, m) for m in manifests}
    verified_crates = {crate_of(m, manifests) for m in VERIFIED_MODULES}
    for path in sorted(rust_files):
        crate = crate_of(path, manifests)
        verus_crate = crate is not None and is_verus_crate(data[crate])
        in_verified = crate is not None and crate in verified_crates
        text = (root / path).read_text(encoding="utf-8")
        found += file_problems(path, text, verus_crate, used, in_verified)
        found += pin_problems(path, text, ADR)
    for module, mount in sorted(VERIFIED_MODULES.items()):
        if module not in rust_files:
            continue
        crate = crate_of(module, manifests)
        if crate is None or not opts_in(data[crate]):
            found.append(
                f"{module}: a verified module, but its crate does not opt into"
                " Verus with [package.metadata.verus] verify = true"
            )
        found += mount_problems(root, module, mount, rust_files)
    for path in sorted(manifests):
        verified = path in verified_crates
        found += manifest_problems(root, path, data[path], verified, rust_files)
    found += config_problems(sorted(configs))
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
    configs = [f for f in files if is_cargo_config(f)]
    found = problems(root, rust, manifests, configs)
    for message in found:
        print(message, file=sys.stderr)
    if found:
        print(f"\nUnsafe Rust needs a Verus proof; see {ADR}.", file=sys.stderr)
    return 1 if found else 0


if __name__ == "__main__":
    sys.exit(main())
