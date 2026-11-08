"""The corpus's texts, offered as examples."""

import tomllib
from pathlib import Path

GROUPS = ("canonical", "llvm")
MOST_RUNS = 16


def catalogue(corpus_root: Path) -> dict[str, list[str]]:
    return {
        group: sorted(p.stem for p in (corpus_root / group).glob("*.fir"))
        for group in GROUPS
    }


def _saved_runs(path: Path) -> list[dict]:
    if not path.exists():
        return []
    tests = tomllib.loads(path.read_text(encoding="utf-8")).get("tests", [])
    return [
        {
            "func": t["func"],
            "args": t.get("args", []),
            "fuel": t.get("fuel"),
            "choices": t.get("choices"),
        }
        for t in tests[:MOST_RUNS]
        if isinstance(t, dict) and "func" in t
    ]


def example(corpus_root: Path, group: str, name: str) -> dict | None:
    """One example, or None unless the catalogue lists it."""
    if group not in GROUPS or name not in catalogue(corpus_root)[group]:
        return None
    base = corpus_root / group / name
    return {
        "text": base.with_suffix(".fir").read_text(encoding="utf-8"),
        "runs": _saved_runs(base.with_suffix(".toml")),
    }
