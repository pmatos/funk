"""Keeps an input that crashed a fuzzer, once the bug is fixed (#165,
ADR-2026-11-08-2117).

Usage: fuzz_to_corpus.py --funk FUNK [--rule RULE] [--corpus DIR] ARTIFACT

`funk verify` decides where ARTIFACT goes in the corpus. A text that it
rejects joins `reject/fuzz.toml`, with RULE saying which rule it breaks. A
valid module's canonical form becomes `canonical/fuzz-HASH.fir`. A crash
that still happens exits with 2: fix the bug first. `funk verify` cannot see
the `parse` fuzzer's round trip, so a text that parses must also format to
a text that formats to itself.

ARTIFACT and DIR must be inside the working directory.
"""

import argparse
import hashlib
import os
import re
import sys
import tempfile
from itertools import groupby
from pathlib import Path

import tools

PRINTABLE = range(0x20, 0x7F)


def toml_text(data: bytes) -> str:
    """`data` as the `text` of a must-reject table: a list of basic strings
    for its printable runs and of numbers for its other bytes."""
    pieces = []
    for printable, run in groupby(data, key=lambda b: b in PRINTABLE):
        if printable:
            pieces.append(basic_string(bytes(run).decode("ascii")))
        else:
            pieces.extend(f"0x{b:02x}" for b in run)
    return "[" + ", ".join(pieces) + "]"


def basic_string(text: str) -> str:
    """`text` as a TOML basic string."""
    quoted = text.replace("\\", "\\\\").replace('"', '\\"')
    return (
        '"' + re.sub(r"[\x00-\x1f\x7f]", lambda m: f"\\u{ord(m[0]):04x}", quoted) + '"'
    )


def reject_table(verdict: str, rule: str, data: bytes) -> str:
    return (
        f'[[reject]]\nverdict = "{verdict}"\nrule = {basic_string(rule)}\n'
        f"text = {toml_text(data)}\n"
    )


def round_trip(funk: str, artifact: Path) -> tuple[str, str | None]:
    """What `funk fmt` prints of `artifact`, and why that does not format to
    itself, if it does not."""
    first = tools.run([funk, "fmt", str(artifact)])
    if first.status != 0:
        return "", tools.failure(first)
    with tempfile.TemporaryDirectory(prefix="fuzz-to-corpus.") as work:
        printed = Path(work) / "printed.fir"
        printed.write_text(first.stdout, encoding="utf-8")
        again = tools.run([funk, "fmt", str(printed)])
    if again.status != 0:
        return "", f"what it prints does not parse: {tools.failure(again)}"
    if again.stdout != first.stdout:
        return "", "what it prints does not format to itself"
    return first.stdout, None


def keep(funk: str, artifact: Path, corpus: Path, rule: str | None) -> tuple[int, str]:
    """Adds `artifact` to `corpus`: the exit status, and what happened."""
    v = tools.verdict(tools.run([funk, "verify", "--json", str(artifact)]))
    if not isinstance(v, tools.Verdict):
        return 2, f"funk verify still fails on {artifact}: {v}"
    if v.verdict not in (tools.ACCEPTED, tools.PARSE_ERROR, tools.VALIDATION_ERROR):
        return 2, f"funk verify gives {v.verdict} on {artifact}"
    canonical = ""
    if v.verdict != tools.PARSE_ERROR:
        canonical, why = round_trip(funk, artifact)
        if why:
            return 2, f"funk fmt still fails on {artifact}: {why}"
    if v.verdict == tools.ACCEPTED:
        name = hashlib.sha256(artifact.read_bytes()).hexdigest()[:16]
        path = corpus / "canonical" / f"fuzz-{name}.fir"
        path.write_text(canonical, encoding="utf-8")
        return 0, f"wrote {path}"
    if not rule:
        return 2, f"{artifact} is a {v.verdict}: say which rule it breaks with --rule"
    path = corpus / "reject" / "fuzz.toml"
    table = reject_table(v.verdict, rule, artifact.read_bytes())
    old = path.read_text(encoding="utf-8") if path.exists() else ""
    path.write_text(old + ("\n" if old else "") + table, encoding="utf-8")
    return 0, f"added a {v.verdict} to {path}"


def inside_working_directory(path: Path) -> Path:
    """`path`, with its links resolved, if that is inside the working
    directory. Agents run this tool, and it must not reach other files."""
    resolved = os.path.realpath(path)
    base = os.path.realpath(os.getcwd())
    if resolved != base and not resolved.startswith(base + os.sep):
        raise ValueError(f"{path} is outside the working directory")
    return Path(resolved)


def main(argv: list[str]) -> int:
    p = argparse.ArgumentParser(
        prog="fuzz_to_corpus", description=__doc__.split("\n")[0]
    )
    p.add_argument("--funk", required=True, help="the funk executable")
    p.add_argument("--rule", help="the rule that a rejected text breaks")
    p.add_argument("--corpus", type=Path, default=Path("tests/fir"), help="the corpus")
    p.add_argument("artifact", type=Path, help="the input that crashed a fuzzer")
    args = p.parse_args(argv)
    try:
        artifact = inside_working_directory(args.artifact)
        corpus = inside_working_directory(args.corpus)
    except ValueError as e:
        p.error(str(e))
    status, what = keep(args.funk, artifact, corpus, args.rule)
    print(what, file=sys.stderr if status else sys.stdout)
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
