"""Checks `fir-ref`'s float arithmetic and comparisons against Berkeley
TestFloat's vectors (#229,
docs/decisions/testing-and-harness-floats.md#the-testfloat-check).

Usage: testfloat.py --fir-ref FIR_REF [--jobs N]

It fetches TestFloat and SoftFloat at the commits `PINS` names, builds
`testfloat_gen` once into a cache, and runs it at level 1, rounding to
nearest even, for each function of `testfloat_cases.functions()` at `f16`,
`f32`, `f64` and `f128`, and, from `f32`'s vectors, at `bf16`. Every vector
of level 1 is checked, but only every 131st of `mulAdd`'s at the four formats
of TestFloat, and at `bf16` every one whose operands are `bf16` values.
Batches of vectors run
on `fir-ref run --exhaustive --nans` with no NaN given, so that a NaN result
is the positive quiet NaN, at no cost to the choice budget. It prints one
line per format and function, and the first failures of each, and exits
with 1 when a vector fails, and with 2 when TestFloat cannot be built or
`fir-ref` gives no result for a batch. `scripts/check-harness.sh` runs it
after the harness.

The cache is `$FUNK_TESTFLOAT_CACHE`, or `funk/testfloat` under
`$XDG_CACHE_HOME` or `~/.cache`. Git checks each fetched commit's hash.
"""

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
from collections.abc import Iterator
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import testfloat_cases as tc

PINS = {
    "berkeley-softfloat-3": "a0c6494cdc11865811dec815d5c0049fba9d82a8",
    "berkeley-testfloat-3": "a9c849f1b0eb0264b626d9686ffae167d996e3be",
}
URL = "https://github.com/ucb-bar/{}.git"
PLATFORM = "Linux-x86_64-GCC"
BATCH = 1000
SHOWN = 5


def git_env() -> dict[str, str]:
    # A commit hook sets GIT_DIR, GIT_INDEX_FILE and others for this
    # repository; the fetches below must not see them.
    return {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}


def cache_root() -> Path:
    if "FUNK_TESTFLOAT_CACHE" in os.environ:
        return Path(os.environ["FUNK_TESTFLOAT_CACHE"])
    base = os.environ.get("XDG_CACHE_HOME") or Path.home() / ".cache"
    return Path(base) / "funk" / "testfloat"


def fetch(repo: str, commit: str, into: Path):
    run = ["git", "-C", str(into)]
    subprocess.run(["git", "init", "-q", str(into)], check=True, env=git_env())
    for attempt in range(5):
        fetched = subprocess.run(
            [*run, "fetch", "-q", "--depth", "1", URL.format(repo), commit],
            check=False,
            env=git_env(),
        )
        if fetched.returncode == 0:
            break
        if attempt == 4:
            raise RuntimeError(f"cannot fetch {repo} at {commit}")
    subprocess.run([*run, "checkout", "-q", commit], check=True, env=git_env())


def provision() -> Path:
    """The path of `testfloat_gen`, built at the pinned commits."""
    final = cache_root() / "-".join(c[:12] for c in PINS.values())
    gen = final / "testfloat_gen"
    if gen.is_file():
        return gen
    final.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=final.parent) as tmp:
        work = Path(tmp)
        for repo, commit in PINS.items():
            fetch(repo, commit, work / repo)
        soft = work / "berkeley-softfloat-3" / "build" / PLATFORM
        test = work / "berkeley-testfloat-3" / "build" / PLATFORM
        subprocess.run(["make", "-s", "-C", str(soft), "softfloat.a"], check=True)
        subprocess.run(
            ["make", "-s", "-C", str(test), "testfloat_gen"],
            check=True,
            env={**os.environ, "SOFTFLOAT_DIR": str(soft.parents[1])},
        )
        built = work / "out"
        built.mkdir()
        shutil.copy2(test / "testfloat_gen", built / "testfloat_gen")
        try:
            built.rename(final)
        except OSError:
            if not gen.is_file():
                raise
    return gen


def generate(gen: Path, name: str, rodd: bool) -> Iterator[str]:
    """The lines `testfloat_gen` writes at level 1 for function `name`."""
    cmd = [str(gen), "-level", "1", "-rodd" if rodd else "-rnear_even", name]
    with subprocess.Popen(cmd, stdout=subprocess.PIPE, text=True) as p:
        assert p.stdout is not None
        yield from p.stdout
    if p.returncode != 0:
        raise RuntimeError(f"{' '.join(cmd)} exited with {p.returncode}")


def vectors(gen: Path, fmt: str, function: str) -> list[tc.Vector]:
    source = "f32" if fmt == "bf16" else fmt
    rodd = fmt == "bf16" and function in tc.ARITHMETIC
    # bf16 keeps every vector whose operands are bf16 values.
    sampled = function == "mulAdd" and fmt != "bf16"
    out = []
    for i, line in enumerate(generate(gen, f"{source}_{function}", rodd)):
        if sampled and i % tc.MULADD_STRIDE:
            continue
        v = tc.parse(function, line)
        if fmt == "bf16":
            v = tc.to_bf16(function, v)
            if v is None:
                continue
        out.append(v)
    return out


def run_batch(fir_ref: str, fmt: str, function: str, batch: list[tc.Vector]):
    """The values `fir-ref` returns for one batch, or why it gave none."""
    e, m = tc.BF16 if fmt == "bf16" else tc.FORMATS[fmt]
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "testfloat.fir"
        path.write_text(tc.module(fmt, e, m, function, batch))
        valid = subprocess.run(
            [fir_ref, "validate", str(path)],
            check=False,
            capture_output=True,
            text=True,
        )
        if valid.returncode != 0:
            return f"fir-ref validate rejects the module: {valid.stdout}"
        ran = subprocess.run(
            [fir_ref, "run", "--exhaustive", "--nans", "", str(path), "@v"],
            check=False,
            capture_output=True,
            text=True,
        )
    try:
        result = json.loads(ran.stdout)
        (outcome,) = result["outcomes"]
        if outcome["kind"] == "return":
            return outcome["values"]
    except (ValueError, KeyError, TypeError):
        pass
    return f"fir-ref exited with {ran.returncode}: {ran.stdout}{ran.stderr}"


def check(fir_ref: str, pool, gen: Path, fmt: str, function: str):
    """Runs one function at one format: (vectors, failures, errors)."""
    e, m = tc.BF16 if fmt == "bf16" else tc.FORMATS[fmt]
    vs = vectors(gen, fmt, function)
    if not vs:
        return 0, [], ["TestFloat gave no vector"]
    batches = [vs[i : i + BATCH] for i in range(0, len(vs), BATCH)]
    ran = pool.map(lambda b: run_batch(fir_ref, fmt, function, b), batches)
    failures, errors = [], []
    for batch, values in zip(batches, ran):
        if isinstance(values, str):
            errors.append(values)
            continue
        cs = tc.checks(function, batch)
        if len(values) != len(cs):
            errors.append(f"{len(values)} values for {len(cs)} checks")
            continue
        failures += [(c, v) for c, v in zip(cs, values) if not tc.passes(e, m, c, v)]
    return len(vs), failures, errors


def describe(c: tc.Check, value: str) -> str:
    operands = " ".join(f"{a:x}" for a in c.vector.operands)
    want = c.expected if c.predicate else f"{c.expected:x}"
    op = f"{c.predicate} " if c.predicate else ""
    return f"    {op}{operands}: TestFloat {want}, fir-ref {value}"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--fir-ref", required=True)
    parser.add_argument("--jobs", type=int, default=os.cpu_count() or 1)
    args = parser.parse_args()
    try:
        gen = provision()
    except (OSError, RuntimeError, subprocess.CalledProcessError) as err:
        print(f"testfloat: cannot build TestFloat: {err}", file=sys.stderr)
        return 2
    status = 0
    with ThreadPoolExecutor(args.jobs) as pool:
        for fmt in [*tc.FORMATS, "bf16"]:
            for function in tc.functions():
                try:
                    n, failures, errors = check(args.fir_ref, pool, gen, fmt, function)
                except RuntimeError as err:
                    n, failures, errors = 0, [], [str(err)]
                print(f"{fmt} {function}: {n} vectors, {len(failures)} failed")
                for c, v in failures[:SHOWN]:
                    print(describe(c, v))
                for err in errors[:SHOWN]:
                    print(f"    no result: {err.strip()}")
                if errors:
                    status = 2
                elif failures and status == 0:
                    status = 1
    return status


if __name__ == "__main__":
    sys.exit(main())
