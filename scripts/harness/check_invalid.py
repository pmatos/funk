"""Checks the harness's invalid verdicts on the real tools (#18, #172,
ADR-2026-10-31-0208, ADR-2026-11-09-1602).

Usage: check_invalid.py --funk FUNK --fir-ref FIR_REF

It runs the harness, main.py, on each fixture corpus of fixtures/, whose
one test the harness must report invalid: in fixtures/invalid/ a division
by a frozen value that can be zero, and in fixtures/out-of-stack/ a
recursion deeper than native code's stack. It passes only when `funk build`
builds the module, the harness reports that test invalid for its reason,
passes every other check, and so exits with 1.
`scripts/check-harness.sh` runs it after the main run of the harness.
"""

import argparse
import resource
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

from refine import FAILED, INVALID

HERE = Path(__file__).resolve().parent
# The default stack limit, so that a run recurses out of the same stack
# whatever `ulimit -s` the harness starts under.
STACK = 8 << 20


@dataclass(frozen=True)
class Fixture:
    directory: str
    test: str
    reason: str


DIVISION = Fixture(
    "invalid",
    "canonical/div-frozen.fir @sdiv_frozen 7 127",
    "the set holds UB (sdiv by zero)",
)
OUT_OF_STACK = Fixture(
    "out-of-stack",
    "canonical/down.fir --fuel 9000000 @down 1000000",
    f"native code outgrew its {STACK} bytes of stack",
)
FIXTURES = (DIVISION, OUT_OF_STACK)


def problem(status: int, out: str, fixture: Fixture = DIVISION) -> str | None:
    """Why the harness's run on `fixture`, which exited with `status` and
    printed `out`, does not show the invalid verdict, if it does not."""
    test, reason = fixture.test, fixture.reason
    lines = out.splitlines()
    mine = [line for line in lines if line.startswith(f"{INVALID:<8}{test}: ")]
    if len(mine) != 1:
        said = next((line for line in lines if test in line), "no line names it")
        return f"the harness does not report {test} invalid: {said}"
    if reason not in mine[0]:
        return f"the harness reports {test} invalid, but not because {reason}"
    if "funk build gives" in mine[0]:
        return f"the harness reports {test} invalid, but funk build fails: {mine[0]}"
    rest = [line for line in lines if line.startswith((FAILED, INVALID))]
    if rest != mine:
        other = next(line for line in rest if line != mine[0])
        return f"another check does not pass: {other}"
    if status != 1:
        return f"the harness exits with {status}, not 1"
    return None


def default_stack():
    """Sets this process's soft stack limit to STACK, or to its hard limit
    when that is lower. Runs in the child, before the harness starts."""
    _, hard = resource.getrlimit(resource.RLIMIT_STACK)
    soft = STACK if hard == resource.RLIM_INFINITY else min(STACK, hard)
    resource.setrlimit(resource.RLIMIT_STACK, (soft, hard))


def check(fixture: Fixture, funk: str, fir_ref: str) -> str | None:
    """Runs the harness on `fixture`, prints what it reports, and returns
    why that does not show the invalid verdict, if it does not."""
    root = HERE / "fixtures" / fixture.directory
    with tempfile.TemporaryDirectory(prefix="fir-invalid.") as generated:
        # The harness also checks the modules that Rust printed, and fails
        # when there are none. A fixture has none of its own, so its module
        # stands in.
        for module in (root / "canonical").glob("*.fir"):
            shutil.copy(module, generated)
        cmd = [sys.executable, str(HERE / "main.py"), "--funk", funk]
        cmd += ["--fir-ref", fir_ref, "--generated", generated, str(root)]
        ran = subprocess.run(
            cmd,
            capture_output=True,
            check=False,
            encoding="utf-8",
            errors="replace",
            preexec_fn=default_stack,
        )
    print(f"The harness on {root.relative_to(HERE.parent.parent)}:")
    print(ran.stdout, end="", flush=True)
    print(ran.stderr, end="", file=sys.stderr)
    return problem(ran.returncode, ran.stdout, fixture)


def main(argv: list[str]) -> int:
    p = argparse.ArgumentParser(
        prog="check_invalid", description=__doc__.split("\n")[0]
    )
    p.add_argument("--funk", required=True, help="the funk executable")
    p.add_argument("--fir-ref", required=True, help="the fir-ref executable")
    args = p.parse_args(argv)
    status = 0
    for fixture in FIXTURES:
        why = check(fixture, args.funk, args.fir_ref)
        if why is None:
            print(
                f"check_invalid: the harness reports {fixture.test} invalid:"
                f" {fixture.reason}"
            )
        else:
            print(f"check_invalid: {why}", file=sys.stderr)
            status = 1
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
