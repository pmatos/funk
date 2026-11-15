"""The corpus of `tests/fir/` and its format (ADR-2026-10-30-2050).

- `canonical/NAME.fir` is a canonical, valid module; `canonical/NAME.toml`,
  if present, lists its tests.
- `noncanonical/NAME.fir` is an input whose canonical form is
  `canonical/NAME.fir`.
- `reject/*.toml` lists must-reject texts, each with the verdict that both
  tools must give and the rule it breaks.
- `llvm/NAME.fir` is a canonical, valid module ported from an LLVM test,
  and `llvm/NAME.toml` lists its tests, names the LLVM test it comes from
  and, for each test, the function, CHECK lines or RUN line of that test
  that the test runs. LLVM's
  licence, `llvm/LICENSE.TXT`, and a notice, `llvm/README.md`, are beside
  them (ADR-2026-11-03-0643), and the licence is the one of the pinned
  commit.

Anything else in the corpus is a format error, as is a sidecar key that the
format does not have.
"""

import hashlib
import re
import tomllib
from dataclasses import dataclass, field
from pathlib import Path

from refine import FUEL_EXHAUSTED, UB
from sets import Declared
from signatures import (  # noqa: F401 (the corpus's readers of signatures)
    closing_paren,
    param_types,
    result_types,
    split_types,
    symbol_end,
)
from tools import PARSE_ERROR, VALIDATION_ERROR

DEFAULT_FUEL = 1_000_000
TOP = ("README.md", "canonical", "noncanonical", "reject", "llvm")
# The files beside the modules ported from LLVM: its licence, and the
# notice that says where they come from.
NOTICES = ("LICENSE.TXT", "README.md")
# The SHA-256 of llvm/LICENSE.TXT at the pinned llvm-project commit, less
# the empty line that ends it, which the end-of-file-fixer hook removes.
LICENCE_SHA256 = "3340babe8ac7bc6ae294d93aa01c310a250d43d5b760e5c12954882d4e5c83c7"


# The keys of a test's `work_item`, each the `fir-ref run` option that gives
# it (docs/decisions/fir-ref-command-line.md#fir-ref-run).
WORK_ITEM = {
    "id": "--work-item-id",
    "group_id": "--work-group-id",
    "group_size": "--work-group-size",
    "num_groups": "--num-work-groups",
}


@dataclass(frozen=True)
class Test:
    """One run of a function. Each of its `args` is a value spelled as a
    constant, or `poison` (#123). `expect` is None for a differential test,
    which may declare its `results`; an interpreter-only test expects a
    tuple of values, UB or fuel exhausted, on the path that its `choices`
    name. `work_item` gives the work-item that the run runs, as pairs of a
    key of `WORK_ITEM` and its three numbers, for a kernel of a device
    module, which `func` names as `@dev::@k` (#212)."""

    module: str
    func: str
    args: tuple[str, ...] = ()
    fuel: int = DEFAULT_FUEL
    expect: object = None
    choices: tuple[str, ...] | None = None
    results: tuple[Declared, ...] = ()
    work_item: tuple[tuple[str, tuple[int, ...]], ...] = ()

    def work_item_options(self) -> list[str]:
        """The `fir-ref run` options that give the test's work-item."""
        return [
            o
            for key, xs in self.work_item
            for o in (WORK_ITEM[key], ",".join(map(str, xs)))
        ]

    def show(self) -> str:
        fuel = [] if self.fuel == DEFAULT_FUEL else ["--fuel", str(self.fuel)]
        if self.choices is not None:
            fuel += ["--choices", ",".join(self.choices)]
        fuel += self.work_item_options()
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


def files(
    directory: Path,
    suffixes: tuple[str, ...],
    errors: list[str],
    beside: tuple[str, ...] = (),
) -> list[Path]:
    """The files of `directory` with these suffixes, by name; anything else
    is an error, but for the files named `beside`."""
    if not directory.is_dir():
        return []
    found = []
    for p in sorted(directory.iterdir()):
        if p.is_file() and p.suffix in suffixes:
            found.append(p)
        elif not (p.is_file() and p.name in beside):
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
    if not c.rejects:
        c.errors.append(f"{root / 'reject'}: the corpus has no must-reject texts")
    load_ported(root / "llvm", c)
    return c


def load_ported(directory: Path, c: Corpus):
    """The modules ported from LLVM's tests, in `llvm/`: each with a
    sidecar that names its source, beside LLVM's licence and a notice, and
    all from one llvm-project commit (ADR-2026-11-03-0643)."""
    if not directory.is_dir():
        return
    for name in NOTICES:
        if not (directory / name).is_file():
            c.errors.append(
                f"{directory / name}: the modules ported from LLVM keep its"
                " licence and a notice beside them"
            )
    licence = directory / "LICENSE.TXT"
    if (
        licence.is_file()
        and hashlib.sha256(licence.read_bytes()).hexdigest() != LICENCE_SHA256
    ):
        c.errors.append(
            f"{licence}: is not LLVM's licence as the pinned llvm-project commit has it"
        )
    found = files(directory, (".fir", ".toml"), c.errors, NOTICES)
    firs = {p.stem for p in found if p.suffix == ".fir"}
    commits = set()
    for p in found:
        if p.suffix == ".toml" and p.stem not in firs:
            c.errors.append(f"{p}: there is no {p.stem}.fir to test")
    for p in found:
        if p.suffix != ".fir":
            continue
        sidecar = p.with_suffix(".toml")
        tests = []
        if sidecar.is_file():
            tests = read_tests(sidecar, f"llvm/{p.name}", c.errors, commits)
        else:
            c.errors.append(f"{p}: a ported module has a sidecar that names its source")
        c.modules.append(Module(f"llvm/{p.name}", p, tests))
    if len(commits) > 1:
        c.errors.append(
            f"{directory}: the ported modules come from one llvm-project"
            f" commit, not {len(commits)}: {', '.join(sorted(commits))}"
        )


def read_toml(path: Path, errors: list[str]) -> dict | None:
    try:
        with open(path, "rb") as f:
            return tomllib.load(f)
    except (OSError, tomllib.TOMLDecodeError) as e:
        errors.append(f"{path}: {e}")
        return None


def read_tests(
    path: Path, module: str, errors: list[str], commits: set[str] | None = None
) -> list[Test]:
    """The tests of a sidecar. With `commits`, the sidecar is a ported
    module's, and its source's commit joins `commits`."""
    data = read_toml(path, errors)
    if data is None:
        return []
    ported = commits is not None
    found, problems = parse_tests(data, module, ported)
    errors += [f"{path}: {p}" for p in problems]
    if ported and source_problem(data.get("source")) is None:
        commits.add(data["source"]["commit"])
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


def parse_tests(
    data: dict, module: str, ported: bool = False
) -> tuple[list[Test], list[str]]:
    """The tests of a sidecar: `tests`, a list of tables with `func` and
    optionally `args`, `fuel`, `expect`, `choices`, `results` and
    `work_item`. A ported
    module's sidecar also has `source`, and each of its tests `from`."""
    keys = ("tests", "source") if ported else ("tests",)
    problems = [f"unknown key {k}" for k in unknown_keys(data, keys)]
    if ported:
        why = source_problem(data.get("source"))
        if why:
            problems.append(why)
    items = data.get("tests")
    if not isinstance(items, list):
        return [], problems + ["tests is a list of tests"]
    found = []
    for i, t in enumerate(items, 1):
        why = test_problem(t, ported)
        if why:
            problems.append(f"test {i}: {why}")
            continue
        expect = t.get("expect")
        if isinstance(expect, list):
            expect = tuple(expect)
        choices = t.get("choices")
        results = tuple(
            Declared(tuple(r["values"]), tuple(r["witness"]))
            for r in t.get("results", [])
        )
        found.append(
            Test(
                module,
                t["func"],
                tuple(t.get("args", [])),
                t.get("fuel", DEFAULT_FUEL),
                expect,
                None if choices is None else tuple(choices),
                results,
                tuple(
                    (k, tuple(t["work_item"][k]))
                    for k in WORK_ITEM
                    if k in t.get("work_item", {})
                ),
            )
        )
    return found, problems


def source_problem(source) -> str | None:
    """Why `source` does not name the LLVM test that a ported module comes
    from, and the llvm-project commit it was read at, if it does not."""
    if not isinstance(source, dict):
        return (
            "source is a table: the file of the LLVM test that the module"
            " comes from, and the llvm-project commit it was read at"
        )
    keys = unknown_keys(source, ("file", "commit"))
    if keys:
        return f"source: unknown key {keys[0]}"
    file = source.get("file")
    if not (
        isinstance(file, str) and file.startswith("llvm/test/") and file.endswith(".ll")
    ):
        return (
            "source: file is the path of an LLVM test in llvm-project, such"
            " as llvm/test/Transforms/InstSimplify/shift.ll"
        )
    commit = source.get("commit")
    if not isinstance(commit, str) or re.fullmatch("[0-9a-f]{40}", commit) is None:
        return "source: commit is the full hash of an llvm-project commit"
    return None


def test_problem(t, ported: bool = False) -> str | None:
    if not isinstance(t, dict):
        return "a test is a table"
    allowed = ("func", "args", "fuel", "expect", "choices", "results", "work_item")
    keys = unknown_keys(t, allowed + (("from",) if ported else ()))
    if keys:
        return f"unknown key {keys[0]}"
    if ported and not (isinstance(t.get("from"), str) and t["from"]):
        return (
            "from names the function, or the CHECK lines, of the LLVM test"
            " that the test comes from"
        )
    func = t.get("func")
    if not isinstance(func, str) or not func.startswith("@"):
        return "func is the function's symbol, as text writes it, such as @add3"
    if not is_strings(t.get("args", [])):
        return (
            "args is a list of strings, each a value spelled as a constant, or poison"
        )
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
    why = work_item_problem(t)
    if why:
        return why
    if "choices" in t:
        if expect is None:
            return "choices go with expect: a differential test declares results"
        if not is_choices(t["choices"]):
            return "choices is a list of values, each spelled as a constant"
    if "results" in t:
        if expect is not None:
            return "results go with a differential test, not with expect"
        return results_problem(t["results"])
    return None


def nested(func: str) -> bool:
    """Whether `func` names a function of a nested module, as `@dev::@k`:
    its first symbol, as text writes it, is followed by `::`. A quoted
    symbol may hold `::` itself."""
    if func.startswith('@"'):
        end = symbol_end(func)
    else:
        end = 1
        while end < len(func) and (func[end].isalnum() or func[end] in "_."):
            end += 1
    return func[end:].startswith("::")


def work_item_problem(t: dict) -> str | None:
    """Why a test's `work_item`, or its function in a nested module, does not
    fit, if it does not. A function of a nested module, `@dev::@k`, runs on
    `fir-ref` alone, since `funk build` builds no nested module's functions,
    and so does a test that gives a work-item. Each key of `work_item` holds
    three numbers below 2^32, one per dimension."""
    item = t.get("work_item")
    if (nested(t["func"]) or item is not None) and t.get("expect") is None:
        return "a kernel's test is interpreter-only: it has expect"
    if item is None:
        return None
    if not isinstance(item, dict):
        return "work_item is a table of the work-item's ids and sizes"
    keys = unknown_keys(item, tuple(WORK_ITEM))
    if keys:
        return f"work_item: unknown key {keys[0]}"
    for key, xs in item.items():
        if not (
            isinstance(xs, list)
            and len(xs) == 3
            and all(
                isinstance(x, int) and not isinstance(x, bool) and 0 <= x < 2**32
                for x in xs
            )
        ):
            return f"work_item: {key} is three numbers below 2^32, one per dimension"
    one = [1, 1, 1]
    for d, name in enumerate("xyz"):
        for low, high in (("id", "group_size"), ("group_id", "num_groups")):
            if item.get(low, [0, 0, 0])[d] >= item.get(high, one)[d]:
                return f"work_item: {low} in {name} is not below {high}"
    return None


def is_choices(value) -> bool:
    """A choice sequence: values with no comma, which `--choices` joins."""
    return is_strings(value) and all(v and "," not in v for v in value)


def results_problem(results) -> str | None:
    """Why `results` is not a list of declared results, if it is not: each
    a table of `values` and a `witness`, no two with the same values."""
    if not isinstance(results, list) or not results:
        return "results is a list of declared results"
    seen = set()
    for i, r in enumerate(results, 1):
        if not isinstance(r, dict):
            return f"result {i} is a table of values and a witness"
        keys = unknown_keys(r, ("values", "witness"))
        if keys:
            return f"result {i}: unknown key {keys[0]}"
        if not is_strings(r.get("values")):
            return f"result {i}: values is a list of values, each a value or poison"
        if not is_choices(r.get("witness")):
            return (
                f"result {i}: witness is a list of choices, each spelled as a constant"
            )
        if tuple(r["values"]) in seen:
            return f"result {i} declares the values of an earlier result"
        seen.add(tuple(r["values"]))
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
