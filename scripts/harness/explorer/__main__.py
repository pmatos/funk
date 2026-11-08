"""Starts the explorer: `python3 -m explorer --funk FUNK --fir-ref FIR_REF`.

`scripts/explorer.sh` builds the tools and runs this.
"""

import argparse
import os
import shutil
import sys
from pathlib import Path

import tools

from .server import LOOPBACK, Explorer
from .toolchain import Toolchain

ROOT = Path(__file__).resolve().parents[3]


def missing(funk: str, fir_ref: str) -> list[str]:
    found = []
    for name, path in (("funk", funk), ("fir-ref", fir_ref)):
        if not os.access(path, os.X_OK):
            found.append(f"{name} is not an executable at {path}")
    for tool in ("as", "ld"):
        if shutil.which(tool) is None:
            found.append(f"{tool}, from GNU binutils, is not on PATH")
    return found


def main() -> int:
    parser = argparse.ArgumentParser(prog="explorer", description=__doc__)
    parser.add_argument("--funk", required=True)
    parser.add_argument("--fir-ref", required=True)
    parser.add_argument("--port", type=int, default=8017)
    parser.add_argument(
        "--timeout",
        type=int,
        default=10,
        help="seconds that any one tool or native program may run",
    )
    args = parser.parse_args()
    problems = missing(args.funk, args.fir_ref)
    if problems:
        print("The explorer cannot start:", *problems, sep="\n  ", file=sys.stderr)
        return 1
    tools.TIMEOUT = args.timeout
    try:
        server = Explorer(
            args.port, Toolchain(args.funk, args.fir_ref), ROOT / "tests" / "fir"
        )
    except OSError as e:
        print(f"The explorer cannot use port {args.port}: {e}", file=sys.stderr)
        return 1
    print(f"fir explorer: http://{LOOPBACK}:{server.server_address[1]}/", flush=True)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    return 0


if __name__ == "__main__":
    sys.exit(main())
