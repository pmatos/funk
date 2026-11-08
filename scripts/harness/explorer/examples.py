"""The corpus's texts, offered as examples."""

from pathlib import Path

import corpus

GROUPS = ("canonical", "llvm")
MOST_RUNS = 16


def catalogue(corpus_root: Path) -> dict[str, list[str]]:
    return {
        group: sorted(p.stem for p in (corpus_root / group).glob("*.fir"))
        for group in GROUPS
    }


def _saved_runs(path: Path, group: str) -> list[dict]:
    if not path.exists():
        return []
    ported = set() if group == "llvm" else None
    return [
        {"func": t.func, "args": t.args, "fuel": t.fuel, "choices": t.choices}
        for t in corpus.read_tests(path, path.stem, [], ported)[:MOST_RUNS]
    ]


def example(corpus_root: Path, group: str, name: str) -> dict | None:
    """One example, or None unless the catalogue lists it."""
    if group not in GROUPS or name not in catalogue(corpus_root)[group]:
        return None
    base = corpus_root / group / name
    return {
        "text": base.with_suffix(".fir").read_text(encoding="utf-8"),
        "runs": _saved_runs(base.with_suffix(".toml"), group),
    }
