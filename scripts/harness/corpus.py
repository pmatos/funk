"""The corpus of `tests/fir/` and its format (ADR-2026-10-30-2050).

- `canonical/NAME.fir` is a canonical, valid module; `canonical/NAME.toml`,
  if present, lists its tests.
- `noncanonical/NAME.fir` is an input whose canonical form is
  `canonical/NAME.fir`.
- `reject/*.toml` lists must-reject texts, each with the verdict that both
  tools must give and the rule it breaks.

Anything else in the corpus is a format error, as is a sidecar key that the
format does not have.
"""

import tomllib
from dataclasses import dataclass, field
from pathlib import Path

from refine import FUEL_EXHAUSTED, UB
from tools import PARSE_ERROR, VALIDATION_ERROR

DEFAULT_FUEL = 1_000_000
TOP = ("README.md", "canonical", "noncanonical", "reject")


@dataclass(frozen=True)
class Test:
    """One run of a function. `expect` is None for a differential test;
    an interpreter-only test expects a tuple of values, UB or fuel
    exhausted."""

    module: str
    func: str
    args: tuple[str, ...] = ()
    fuel: int = DEFAULT_FUEL
    expect: object = None

    def show(self) -> str:
        fuel = [] if self.fuel == DEFAULT_FUEL else ["--fuel", str(self.fuel)]
        text = " ".join([self.module, *fuel, self.func, *self.args])
        return text if self.expect is None else text + " (interpreter only)"


@dataclass(frozen=True)
class Reject:
    name: str
    verdict: str
    rule: str
    text: bytes


@dataclass
class Module:
    name: str
    path: Path
    tests: list[Test] = field(default_factory=list)


@dataclass
class Corpus:
    modules: list[Module] = field(default_factory=list)
    inputs: list[tuple[str, Path]] = field(default_factory=list)
    rejects: list[Reject] = field(default_factory=list)
    errors: list[str] = field(default_factory=list)


def files(directory: Path, suffixes: tuple[str, ...], errors: list[str]) -> list[Path]:
    """The files of `directory` with these suffixes, by name; anything else
    is an error."""
    if not directory.is_dir():
        return []
    found = []
    for p in sorted(directory.iterdir()):
        if p.is_file() and p.suffix in suffixes:
            found.append(p)
        else:
            errors.append(f"{p}: the corpus has no place for this")
    return found


def load(root: Path) -> Corpus:
    c = Corpus()
    for p in sorted(root.iterdir()):
        if p.name not in TOP:
            c.errors.append(f"{p}: the corpus has no place for this")
    canonical = files(root / "canonical", (".fir", ".toml"), c.errors)
    firs = {p.stem for p in canonical if p.suffix == ".fir"}
    tests = {}
    for p in canonical:
        if p.suffix == ".toml":
            if p.stem not in firs:
                c.errors.append(f"{p}: there is no {p.stem}.fir to test")
            else:
                tests[p.stem] = read_tests(p, f"canonical/{p.stem}.fir", c.errors)
    for p in canonical:
        if p.suffix == ".fir":
            c.modules.append(Module(f"canonical/{p.name}", p, tests.get(p.stem, [])))
    if not c.modules:
        c.errors.append(f"{root / 'canonical'}: the corpus has no canonical modules")
    for p in files(root / "noncanonical", (".fir",), c.errors):
        if p.stem not in firs:
            c.errors.append(f"{p}: there is no canonical/{p.name}")
        c.inputs.append((f"noncanonical/{p.name}", p))
    for p in files(root / "reject", (".toml",), c.errors):
        c.rejects += read_rejects(p, f"reject/{p.name}", c.errors)
    return c


def read_toml(path: Path, errors: list[str]) -> dict | None:
    try:
        with open(path, "rb") as f:
            return tomllib.load(f)
    except (OSError, tomllib.TOMLDecodeError) as e:
        errors.append(f"{path}: {e}")
        return None


def read_tests(path: Path, module: str, errors: list[str]) -> list[Test]:
    data = read_toml(path, errors)
    if data is None:
        return []
    found, problems = parse_tests(data, module)
    errors += [f"{path}: {p}" for p in problems]
    return found


def read_rejects(path: Path, name: str, errors: list[str]) -> list[Reject]:
    data = read_toml(path, errors)
    if data is None:
        return []
    found, problems = parse_rejects(data, name)
    errors += [f"{path}: {p}" for p in problems]
    return found


def unknown_keys(table: dict, allowed: tuple[str, ...]) -> list[str]:
    return [k for k in table if k not in allowed]


def is_strings(value) -> bool:
    return isinstance(value, list) and all(isinstance(v, str) for v in value)


def parse_tests(data: dict, module: str) -> tuple[list[Test], list[str]]:
    """The tests of a sidecar: `tests`, a list of tables with `func` and
    optionally `args`, `fuel` and `expect`."""
    problems = [f"unknown key {k}" for k in unknown_keys(data, ("tests",))]
    items = data.get("tests")
    if not isinstance(items, list):
        return [], problems + ["tests is a list of tests"]
    found = []
    for i, t in enumerate(items, 1):
        why = test_problem(t)
        if why:
            problems.append(f"test {i}: {why}")
            continue
        expect = t.get("expect")
        if isinstance(expect, list):
            expect = tuple(expect)
        found.append(
            Test(
                module,
                t["func"],
                tuple(t.get("args", [])),
                t.get("fuel", DEFAULT_FUEL),
                expect,
            )
        )
    return found, problems


def test_problem(t) -> str | None:
    if not isinstance(t, dict):
        return "a test is a table"
    keys = unknown_keys(t, ("func", "args", "fuel", "expect"))
    if keys:
        return f"unknown key {keys[0]}"
    func = t.get("func")
    if not isinstance(func, str) or not func.startswith("@"):
        return "func is the function's symbol, as text writes it, such as @add3"
    if not is_strings(t.get("args", [])):
        return "args is a list of strings, each a value spelled as a constant"
    fuel = t.get("fuel", DEFAULT_FUEL)
    if not isinstance(fuel, int) or isinstance(fuel, bool) or fuel < 0:
        return "fuel is a number of steps"
    expect = t.get("expect")
    if (
        expect is not None
        and not is_strings(expect)
        and expect
        not in (
            UB,
            FUEL_EXHAUSTED,
        )
    ):
        return f"expect is a list of values, {UB} or {FUEL_EXHAUSTED}"
    return None


def parse_rejects(data: dict, name: str) -> tuple[list[Reject], list[str]]:
    """The must-reject texts of a file: `reject`, a list of tables with
    `verdict`, `rule` and `text`."""
    problems = [f"unknown key {k}" for k in unknown_keys(data, ("reject",))]
    items = data.get("reject")
    if not isinstance(items, list):
        return [], problems + ["reject is a list of texts"]
    found = []
    for i, r in enumerate(items, 1):
        why = reject_problem(r)
        if why:
            problems.append(f"text {i}: {why}")
            continue
        found.append(
            Reject(f"{name} #{i}", r["verdict"], r["rule"], text_bytes(r["text"]))
        )
    return found, problems


def reject_problem(r) -> str | None:
    if not isinstance(r, dict):
        return "a must-reject text is a table"
    keys = unknown_keys(r, ("verdict", "rule", "text"))
    if keys:
        return f"unknown key {keys[0]}"
    if r.get("verdict") not in (PARSE_ERROR, VALIDATION_ERROR):
        return f"verdict is {PARSE_ERROR} or {VALIDATION_ERROR}"
    if not isinstance(r.get("rule"), str) or not r["rule"]:
        return "rule says which rule the text breaks"
    text = r.get("text")
    pieces = text if isinstance(text, list) else [text]
    if not all(isinstance(p, str) or is_byte(p) for p in pieces):
        return "text is a string, or a list of strings and bytes"
    return None


def is_byte(value) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and 0 <= value < 256


def text_bytes(text: str | list) -> bytes:
    """The bytes of a text: a string in UTF-8, or a list of strings in UTF-8
    and raw bytes, for a text that is not UTF-8."""
    pieces = text if isinstance(text, list) else [text]
    return b"".join(p.encode() if isinstance(p, str) else bytes([p]) for p in pieces)


def result_types(text: str) -> dict[str, list[str]]:
    """The result types of each function of a canonical module, by its
    symbol as text writes it. A canonical module writes each function's
    signature on one line: `func SYMBOL(PARAMS) -> TYPES {`."""
    found = {}
    for line in text.split("\n"):
        if not line.startswith("func @") or not line.endswith(" {"):
            continue
        rest = line[len("func ") : -len(" {")]
        end = symbol_end(rest)
        close = closing_paren(rest, end)
        if close is None:
            continue
        tail = rest[close + 1 :]
        found[rest[:end]] = split_types(tail[4:]) if tail.startswith(" -> ") else []
    return found


def symbol_end(s: str) -> int:
    """The index just past the symbol at the start of `s`."""
    if not s.startswith('@"'):
        return s.find("(") if "(" in s else len(s)
    i = 2
    while i < len(s) and s[i] != '"':
        i += 2 if s[i] == "\\" else 1
    return i + 1


def closing_paren(s: str, start: int) -> int | None:
    """The index of the `)` that closes the `(` at `start`."""
    if s[start : start + 1] != "(":
        return None
    depth = 0
    for i in range(start, len(s)):
        depth += {"(": 1, ")": -1}.get(s[i], 0)
        if depth == 0:
            return i
    return None


def split_types(s: str) -> list[str]:
    """Splits `T1, T2` at the commas outside parentheses."""
    out, depth, start = [], 0, 0
    for i, ch in enumerate(s):
        depth += {"(": 1, ")": -1}.get(ch, 0)
        if ch == "," and depth == 0:
            out.append(s[start:i].strip())
            start = i + 1
    out.append(s[start:].strip())
    return out
