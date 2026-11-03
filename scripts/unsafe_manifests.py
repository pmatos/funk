"""The rules of scripts/check_unsafe_code.py on Cargo manifests, crate
roots and Cargo configurations (ADR-2026-11-03-0808): rustc's `unsafe_code`
lint reaches every line that cargo compiles, and nothing puts code in a
crate past the check.

The workspace forbids unsafe code, and every crate inherits that or forbids
it too, except a crate with a verified module, which denies it. Cargo does
not pass those lints to doctests, so the root of each library forbids
unsafe code in its doctests itself. Every crate and target is on the 2024
edition, where an extern block and an unsafe attribute must say `unsafe`.
A target's file is a tracked `.rs` file, which the check reads. No crate is
a proc macro, since rustc does not report the lint in a proc macro's
output, even at `forbid`. No crate has a build script or links a native
library, and no Cargo configuration is tracked, since each can link code
that no `.rs` file holds. A crate with a verified module keeps the default
layout and depends on vstd alone, from crates.io, so no macro from
elsewhere puts code in it.
"""

import posixpath
import re
import tomllib
from pathlib import Path

from rust_items import items, tokens

EDITION = "2024"
DOCTESTS = "#![doc(test(attr(forbid(unsafe_code))))]"
TARGETS = ("lib", "bin", "test", "bench", "example")
DEPENDENCIES = ("dependencies", "dev-dependencies", "build-dependencies")
# Cargo reads `.cargo/config.toml`, or `.cargo/config`, in the directory it
# runs in and in each one above it.
CARGO_CONFIG = re.compile(r"(^|/)\.cargo/config(\.toml)?$")


def is_cargo_config(path: str) -> bool:
    return CARGO_CONFIG.search(path) is not None


def config_problems(configs: list[str]) -> list[str]:
    """A Cargo configuration can set `rustflags`, a linker, a
    `rustc-wrapper` or a `[patch]`: code that no tracked `.rs` file holds."""
    return [
        f"{path}: a Cargo configuration can link code that the check never"
        " reads; keep its settings in the manifests"
        for path in configs
    ]


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
    found = lint_problems(path, data, verified) + edition_problems(path, data)
    found += patch_problems(path, data)
    if "package" in data:
        found += target_problems(path, data, verified, rust_files)
        found += native_problems(path, data, rust_files)
        found += doctest_problems(root, path, data, rust_files)
    if verified:
        found += dependency_problems(path, data)
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


def edition_problems(path: str, data: dict) -> list[str]:
    """In the 2024 edition an extern block must be `unsafe extern`, and an
    unsafe attribute must be written `unsafe(...)`, so the check sees both."""
    found = []
    if "workspace" in data:
        edition = data["workspace"].get("package", {}).get("edition")
        if edition != EDITION:
            found.append(f"{path}: the workspace's edition is {edition}, not {EDITION}")
    crate = data.get("package", {}).get("edition")
    if "package" in data and crate not in ({"workspace": True}, EDITION):
        found.append(
            f"{path}: the edition is not the workspace's {EDITION}, in which an"
            " extern block and an unsafe attribute say `unsafe`"
        )
    return found


def patch_problems(path: str, data: dict) -> list[str]:
    """vstd and the `verus_*` crates come from crates.io, as Cargo.lock
    pins them (ADR-2026-11-03-0809)."""
    patched = [name for table in data.get("patch", {}).values() for name in table]
    patched += [spec.split(":")[0] for spec in data.get("replace", {})]
    return [
        f"{path}: it patches or replaces {name}, which comes from crates.io only"
        for name in patched
        if name == "vstd" or name.startswith("verus_")
    ]


def target_problems(
    path: str, data: dict, verified: bool, rust_files: list[str]
) -> list[str]:
    """A target's file is a tracked `.rs` file, which the check reads, and
    its edition is the workspace's. A crate with a verified module keeps the
    default layout. No library is a proc macro."""
    here, found = posixpath.dirname(path), []
    for key in TARGETS:
        value = data.get(key, [])
        for table in value if isinstance(value, list) else [value]:
            if not isinstance(table, dict):
                continue
            if table.get("edition", EDITION) != EDITION:
                found.append(
                    f"{path}: [{key}] edition: a target is on the workspace's"
                    f" {EDITION} edition, in which an unsafe attribute says `unsafe`"
                )
            if "path" not in table:
                continue
            value = table["path"]
            target = posixpath.normpath(posixpath.join(here, str(value)))
            if verified:
                found.append(
                    f"{path}: [{key}] path in a crate with a verified module,"
                    " which keeps Cargo's default layout"
                )
            elif not (target.endswith(".rs") and target in rust_files):
                found.append(
                    f"{path}: [{key}] path = {value!r} is not a tracked .rs file,"
                    " which this check would read"
                )
    lib = data.get("lib", {})
    lib = lib if isinstance(lib, dict) else {}
    types = [t for k in ("crate-type", "crate_type") for t in lib.get(k) or []]
    if lib.get("proc-macro") or lib.get("proc_macro") or "proc-macro" in types:
        found.append(
            f"{path}: a proc macro: rustc does not report `unsafe_code` in its"
            " output, even where the lint is `forbid`"
        )
    return found


def native_problems(path: str, data: dict, rust_files: list[str]) -> list[str]:
    """No build script and no `links`: either can link code that no tracked
    `.rs` file holds, such as an `.init_array` entry assembled at build
    time."""
    found = []
    build = data["package"].get("build")
    if build is not None and build is not False:
        found.append(f"{path}: build = {build!r}: no crate has a build script")
    script = posixpath.join(posixpath.dirname(path), "build.rs")
    if script in rust_files:
        found.append(f"{script}: no crate has a build script")
    if "links" in data["package"]:
        found.append(f"{path}: links: no crate links a native library")
    return found


def dependency_problems(path: str, data: dict) -> list[str]:
    """A crate with a verified module depends on vstd alone, by its version
    on crates.io: no other crate's macro or build script puts code in it."""
    found = []
    tables = [(k, data.get(k, {})) for k in DEPENDENCIES]
    for target, table in data.get("target", {}).items():
        tables += [(f"target.{target}.{k}", table.get(k, {})) for k in DEPENDENCIES]
    for key, table in tables:
        for name, spec in table.items():
            if key != "dependencies" or name != "vstd":
                found.append(
                    f"{path}: [{key}] {name}: a crate with a verified module"
                    " depends on vstd alone"
                )
            elif not isinstance(spec, str):
                found.append(f"{path}: vstd is not a version from crates.io")
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
