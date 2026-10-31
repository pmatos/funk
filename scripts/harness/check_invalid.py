"""Checks the harness's invalid verdict on the real tools (#18,
ADR-2026-10-31-0208).

Usage: check_invalid.py --funk FUNK --fir-ref FIR_REF

It runs the harness, main.py, on the fixture corpus of fixtures/invalid/,
whose one test divides by a frozen value that can be zero. It passes only
when `funk build` builds the module, the harness reports that test invalid
because the set holds UB that names a zero divisor, `the set holds UB
(sdiv by zero)`, passes every other check, and so exits with 1.
`scripts/check-harness.sh` runs it after the main run of the harness.
"""

import argparse
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

from refine import FAILED, INVALID

HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixtures" / "invalid"
TEST = "canonical/div-frozen.fir @sdiv_frozen 7 127"
REASON = "the set holds UB (sdiv by zero)"


def problem(status: int, out: str) -> str | None:
    """Why the harness's run on the fixture, which exited with `status` and
    printed `out`, does not show the invalid verdict, if it does not."""
    lines = out.splitlines()
    mine = [line for line in lines if line.startswith(f"{INVALID:<8}{TEST}: ")]
    if len(mine) != 1:
        said = next((line for line in lines if TEST in line), "no line names it")
        return f"the harness does not report {TEST} invalid: {said}"
    if REASON not in mine[0]:
        return f"the harness reports {TEST} invalid, but not because {REASON}"
    if "funk build gives" in mine[0]:
        return f"the harness reports {TEST} invalid, but funk build fails: {mine[0]}"
    rest = [line for line in lines if line.startswith((FAILED, INVALID))]
    if rest != mine:
        other = next(line for line in rest if line != mine[0])
        return f"another check does not pass: {other}"
    if status != 1:
        return f"the harness exits with {status}, not 1"
    return None


def main(argv: list[str]) -> int:
    p = argparse.ArgumentParser(
        prog="check_invalid", description=__doc__.split("\n")[0]
    )
    p.add_argument("--funk", required=True, help="the funk executable")
    p.add_argument("--fir-ref", required=True, help="the fir-ref executable")
    args = p.parse_args(argv)
    with tempfile.TemporaryDirectory(prefix="fir-invalid.") as generated:
        # The harness also checks the modules that Rust printed, and fails
        # when there are none. The fixture has none of its own, so its
        # module stands in.
        for module in (FIXTURE / "canonical").glob("*.fir"):
            shutil.copy(module, generated)
        cmd = [sys.executable, str(HERE / "main.py"), "--funk", args.funk]
        cmd += ["--fir-ref", args.fir_ref, "--generated", generated, str(FIXTURE)]
        ran = subprocess.run(
            cmd,
            capture_output=True,
            check=False,
            encoding="utf-8",
            errors="replace",
        )
    print(f"The harness on {FIXTURE.relative_to(HERE.parent.parent)}:")
    print(ran.stdout, end="", flush=True)
    print(ran.stderr, end="", file=sys.stderr)
    why = problem(ran.returncode, ran.stdout)
    if why is not None:
        print(f"check_invalid: {why}", file=sys.stderr)
        return 1
    print(f"check_invalid: the harness reports {TEST} invalid: {REASON}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
