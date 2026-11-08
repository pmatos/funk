"""The corpus's texts, offered as examples."""

from pathlib import Path

import corpus

GROUPS = ("canonical", "llvm")
MOST_RUNS = 16


def _saved_runs(path: Path, group: str) -> list[dict]:
    if not path.exists():
        return []
    ported = set() if group == "llvm" else None
    return [
        {"func": t.func, "args": t.args, "fuel": t.fuel, "choices": t.choices}
        for t in corpus.read_tests(path, path.stem, [], ported)[:MOST_RUNS]
    ]


def _example(fir: Path, group: str) -> dict:
    return {
        "text": fir.read_text(encoding="utf-8"),
        "runs": _saved_runs(fir.with_suffix(".toml"), group),
    }


def load(corpus_root: Path) -> dict[str, dict[str, dict]]:
    """Every example, by group and name, read once at start-up so that a
    request only ever picks from what is already in memory."""
    return {
        group: {
            fir.stem: _example(fir, group)
            for fir in sorted((corpus_root / group).glob("*.fir"))
        }
        for group in GROUPS
    }
