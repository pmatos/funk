"""Fail on unsafe Rust that Verus does not prove, and on any assumption of a
proof outside the trusted base (ADR-2026-11-03-0808).

Unsafe code may live only in a verified module: a file of VERIFIED_MODULES,
in a crate that opts into Verus, so that the verus-proof hook proves it.
There, `unsafe` may appear only on the items of TRUSTED_BASE, which
ADR-2026-11-03-0808 lists; outside `verus!` a verified module holds only
inner attributes, `use`, constants and trusted items, and it holds no macro
but its `verus!` block. The calls that the proof rests on are those of
CALLS. The check also fails on `unsafe_code` in an attribute other than a
trusted one; a manifest that lets a crate with no verified module use unsafe
code; an assumption (`assume`, `admit`, `axiom`, `external_body`,
`assume_specification` and their kin) other than on a trusted item; code
that Verus does not see when it verifies; and a trusted item that is gone.
It reads the Rust files and Cargo manifests that git tracks, without
comments and strings.
"""

import re
import subprocess
import sys
import tomllib
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from rust_items import attributes, is_ident, is_punct, items, tokens

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

# Function -> the one item that names it, once, besides its own definition.
# So one view of the slots exists, `record` ends by consuming it in
# `finish`, `.init_array` holds `record`, and each descriptor gets one
# `fcntl` call (ADR-2026-11-03-0808).
CALLS = {
    "crates/funk-start-fds/src/record.rs": {
        "take_slots": "record",
        "finish": "record",
        "record": "RECORD",
        "getfd": "record_slots",
    },
}

# Words that make Verus assume instead of prove: they count in Verus crates.
ASSUMPTIONS = {"assume", "admit", "axiom", "external"}
ASSUMPTION_PREFIXES = ("assume_", "external_")
# The words that may stand in the `mod` item that mounts a verified module.
MOUNT_WORDS = {"mod", "cfg", "any", "target_os"}


def marks(word: str, verus_crate: bool) -> str | None:
    if word in ("unsafe", "unsafe_code", "cfg", "cfg_attr") or is_verus_cfg(word):
        return word
    if verus_crate and (word in ASSUMPTIONS or word.startswith(ASSUMPTION_PREFIXES)):
        return word
    return None


def is_verus_cfg(word: str) -> bool:
    """Verus sets configurations named `verus_*` that cargo does not."""
    return word.startswith("verus_")


def file_problems(path: str, text: str, verus_crate: bool, used: set) -> list[str]:
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
            mark = marks(word, verus_crate)
            if mark is None or (mark in ("cfg", "cfg_attr") and not verified):
                continue
            if mark in trusted.get(item, ()):
                used.add((path, item, mark))
            else:
                found.append(f"{where}: {why(mark)}")
        if verified:
            found += layout_problems(path, toks, item, kind, lo, hi, in_verus)
    return found + call_problems(path, toks, entries)


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


def layout_problems(path, toks, item, kind, lo, hi, in_verus) -> list[str]:
    """Outside `verus!`, a verified module holds only inner attributes,
    `use`, constants and trusted items, and it holds no macro but its
    `verus!` block, since Verus and this check do not see what one makes."""
    line = toks[lo][2]
    macro = kind == "macro_rules" or (kind or "").endswith("!")
    if macro and (kind != "verus!" or in_verus):
        return [f"{path}:{line}: `{kind}` in {item}: no macro in a verified module"]
    trusted = TRUSTED_BASE.get(path, {})
    if in_verus or kind in ("inner", "use", "verus!") or item in trusted:
        return []
    if kind == "const" and not any(is_macro_call(toks, i) for i in range(lo, hi)):
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


def call_problems(path: str, toks, entries) -> list[str]:
    found = []
    for callee, caller in CALLS.get(path, {}).items():
        counts: dict[str, int] = {}
        for entry in entries:
            n = sum(1 for i in range(entry.lo, entry.hi) if is_ident(toks, i, callee))
            counts[entry.path] = counts.get(entry.path, 0) + n
        if counts.pop(callee, 0) != 1:
            found.append(f"{path}: {callee} must be defined once, by that name")
        if (here := counts.pop(caller, 0)) != 1:
            found.append(f"{path}: {caller} names {callee} {here} times, not once")
        for item in sorted(i for i, n in counts.items() if n):
            found.append(
                f"{path}: `{callee}` in {item}: only {caller} may name it ({ADR})"
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


def unsafe_level(lints: dict) -> str:
    level = lints.get("rust", {}).get("unsafe_code", "allow")
    return level.get("level", "allow") if isinstance(level, dict) else level


def manifest_problems(path: str, data: dict, verified: bool) -> list[str]:
    """The workspace forbids unsafe code; every crate inherits that or
    forbids it too, except a crate with a verified module, which denies it.
    No manifest declares a Verus configuration to rustc."""
    found = []
    lints = data.get("lints", {})
    shared = data.get("workspace", {}).get("lints", {})
    if "workspace" in data and (level := unsafe_level(shared)) != "forbid":
        found.append(f"{path}: unsafe_code is {level} in [workspace.lints], not forbid")
    if "package" in data:
        level = unsafe_level(lints)
        if verified and level != "deny":
            found.append(
                f"{path}: unsafe_code is {level}, not deny, in a crate with a"
                " verified module"
            )
        if not verified and lints.get("workspace") is not True and level != "forbid":
            found.append(
                f"{path}: unsafe_code is {level}, not forbid, in a crate with no"
                " verified module; inherit [workspace.lints] or forbid it"
            )
    for table in (lints, shared):
        cfgs = table.get("rust", {}).get("unexpected_cfgs", {})
        for entry in cfgs.get("check-cfg", []) if isinstance(cfgs, dict) else []:
            if re.search(r"\bverus_", entry):
                found.append(f"{path}: check-cfg declares {entry}, a Verus cfg")
    return found


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
        found += manifest_problems(path, data[path], path in verified_crates)
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
