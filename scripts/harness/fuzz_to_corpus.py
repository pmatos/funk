"""Keeps an input that crashed a fuzzer, once the bug is fixed (#165,
ADR-2026-11-08-2117).

Usage: fuzz_to_corpus.py --funk FUNK [--rule RULE] [--corpus DIR] ARTIFACT

`funk verify` decides where ARTIFACT goes in the corpus. A text that it
rejects joins `reject/fuzz.toml`, with RULE saying which rule it breaks. A
valid module's canonical form becomes `canonical/fuzz-HASH.fir`. A crash
that still happens exits with 2: fix the bug first.
"""

import argparse
import hashlib
import sys
from pathlib import Path

import tools

PRINTABLE = range(0x20, 0x7F)


def toml_text(data: bytes) -> str:
    """`data` as the `text` of a must-reject table: a list of basic strings
    for its printable runs and of numbers for its other bytes."""
    pieces, run = [], ""
    for b in data:
        if b in PRINTABLE:
            run += {0x22: '\\"', 0x5C: "\\\\"}.get(b, chr(b))
            continue
        if run:
            pieces.append(f'"{run}"')
            run = ""
        pieces.append(f"0x{b:02x}")
    if run:
        pieces.append(f'"{run}"')
    return "[" + ", ".join(pieces) + "]"


def reject_table(verdict: str, rule: str, data: bytes) -> str:
    quoted = rule.replace("\\", "\\\\").replace('"', '\\"')
    return (
        f'[[reject]]\nverdict = "{verdict}"\nrule = "{quoted}"\n'
        f"text = {toml_text(data)}\n"
    )


def keep(funk: str, artifact: Path, corpus: Path, rule: str | None) -> tuple[int, str]:
    """Adds `artifact` to `corpus`: the exit status, and what happened."""
    v = tools.verdict(tools.run([funk, "verify", "--json", str(artifact)]))
    if not isinstance(v, tools.Verdict):
        return 2, f"funk verify still fails on {artifact}: {v}"
    if v.verdict == tools.ACCEPTED:
        ran = tools.run([funk, "fmt", str(artifact)])
        if ran.status != 0:
            return 2, f"funk fmt fails on {artifact}: {tools.failure(ran)}"
        name = hashlib.sha256(artifact.read_bytes()).hexdigest()[:16]
        path = corpus / "canonical" / f"fuzz-{name}.fir"
        path.write_text(ran.stdout, encoding="utf-8")
        return 0, f"wrote {path}"
    if v.verdict not in (tools.PARSE_ERROR, tools.VALIDATION_ERROR):
        return 2, f"funk verify gives {v.verdict} on {artifact}"
    if not rule:
        return 2, f"{artifact} is a {v.verdict}: say which rule it breaks with --rule"
    path = corpus / "reject" / "fuzz.toml"
    table = reject_table(v.verdict, rule, artifact.read_bytes())
    old = path.read_text(encoding="utf-8") if path.exists() else ""
    path.write_text(old + ("\n" if old else "") + table, encoding="utf-8")
    return 0, f"added a {v.verdict} to {path}"


def main(argv: list[str]) -> int:
    p = argparse.ArgumentParser(
        prog="fuzz_to_corpus", description=__doc__.split("\n")[0]
    )
    p.add_argument("--funk", required=True, help="the funk executable")
    p.add_argument("--rule", help="the rule that a rejected text breaks")
    p.add_argument("--corpus", type=Path, default=Path("tests/fir"), help="the corpus")
    p.add_argument("artifact", type=Path, help="the input that crashed a fuzzer")
    args = p.parse_args(argv)
    status, what = keep(args.funk, args.artifact, args.corpus, args.rule)
    print(what, file=sys.stderr if status else sys.stdout)
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
