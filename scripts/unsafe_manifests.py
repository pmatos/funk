"""The rules of scripts/check_unsafe_code.py on Cargo manifests and crate
roots (ADR-2026-11-03-0808): rustc's `unsafe_code` lint reaches every
crate and every doctest.

The workspace forbids unsafe code, and every crate inherits that or forbids
it too, except a crate with a verified module, which denies it. Cargo does
not pass those lints to doctests, so the root of each library forbids
unsafe code in its doctests itself. No manifest declares a Verus
configuration to rustc.
"""

import posixpath
import re
import tomllib
from pathlib import Path

from rust_items import items, tokens

DOCTESTS = "#![doc(test(attr(forbid(unsafe_code))))]"


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


def manifest_problems(
    root: Path, path: str, data: dict, verified: bool, rust_files: list[str]
) -> list[str]:
    found = lint_problems(path, data, verified)
    if "package" in data:
        found += doctest_problems(root, path, data, rust_files)
    return found


def lint_problems(path: str, data: dict, verified: bool) -> list[str]:
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


def doctest_problems(
    root: Path, path: str, data: dict, rust_files: list[str]
) -> list[str]:
    """Cargo passes [lints] to every target but doctests, so the root of a
    library forbids unsafe code in its doctests itself."""
    lib = data.get("lib", {})
    lib = lib.get("path", "src/lib.rs") if isinstance(lib, dict) else "src/lib.rs"
    root_file = posixpath.normpath(posixpath.join(posixpath.dirname(path), lib))
    if root_file not in rust_files:
        return []
    toks = tokens((root / root_file).read_text(encoding="utf-8"))
    want = [text for _, text, _ in tokens(DOCTESTS)]
    for entry in items(toks, 0, len(toks)):
        if (
            entry.path == "<module>"
            and [toks[i][1] for i in range(entry.lo, entry.hi)] == want
        ):
            return []
    return [
        (
            f"{root_file}: a library's root holds {DOCTESTS}, since cargo does"
            " not pass [lints] to doctests"
        )
    ]
