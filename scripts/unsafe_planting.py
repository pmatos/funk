"""Helpers for the tests of scripts/check_unsafe_code.py, which plant a
violation in a copy of the workspace's real files and check that the check
fails on it. Run the tests: python -m unittest discover -s scripts -p
"test_*unsafe*.py"
"""

import tempfile
from pathlib import Path

from check_unsafe_code import problems

REPO = Path(__file__).resolve().parent.parent
RECORD = "crates/funk-start-fds/src/record.rs"
FDS = "crates/funk-start-fds/Cargo.toml"
FDS_LIB = "crates/funk-start-fds/src/lib.rs"
IR = "crates/funk-ir/src/lib.rs"
IR_TOML = "crates/funk-ir/Cargo.toml"
REAL = ["Cargo.toml", FDS, FDS_LIB, RECORD, IR_TOML]
# The attribute that a library's root holds for its doctests.
DOCTESTS = "#![doc(test(attr(forbid(unsafe_code))))]\n"

PATHS = {
    "ir": IR,
    "ir_toml": IR_TOML,
    "record": RECORD,
    "fds": FDS,
    "fds_lib": FDS_LIB,
    "root": "Cargo.toml",
}


def check(**files: str) -> list[str]:
    """problems() on a copy of the real files, with `files`, keyed by a
    repository path or a key of PATHS, replacing or adding to them."""
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        texts = {path: (REPO / path).read_text(encoding="utf-8") for path in REAL}
        texts[IR] = DOCTESTS + "pub fn f() {}\n"
        texts.update({PATHS.get(key, key): text for key, text in files.items()})
        for path, text in texts.items():
            (root / path).parent.mkdir(parents=True, exist_ok=True)
            (root / path).write_text(text, encoding="utf-8")
        rust = [p for p in texts if p.endswith(".rs")]
        manifests = [p for p in texts if p.endswith("Cargo.toml")]
        return problems(root, rust, manifests)


def real(path: str, old: str, new: str) -> str:
    """The real file at `path`, with its one `old` replaced by `new`."""
    text = (REPO / path).read_text(encoding="utf-8")
    assert text.count(old) == 1, old
    return text.replace(old, new)


def record(old: str, new: str) -> str:
    return real(RECORD, old, new)


def in_verus(code: str) -> str:
    return record("} // verus!", code + "\n} // verus!")


def after_verus(code: str) -> str:
    return record("} // verus!", "} // verus!\n" + code)
