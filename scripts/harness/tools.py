"""Running funk, fir-ref and native code, and reading what they print.

Each reader takes what a process did, a `Ran`, and returns its result or a
string that says why there is none, so the readers are tested without
running anything.
"""

import json
import subprocess
from dataclasses import dataclass

from refine import FUEL_EXHAUSTED, RETURN, STUCK, UB, Outcome
from sets import BudgetExceeded, Outcomes, Path

TIMEOUT = 120

ACCEPTED = "accepted"
PARSE_ERROR = "parse-error"
VALIDATION_ERROR = "validation-error"
# The exit status that goes with each verdict on one file
# (ADR-2026-10-30-1032, ADR-2026-10-30-1741).
STATUS = {ACCEPTED: 0, PARSE_ERROR: 1, VALIDATION_ERROR: 1, "io-error": 2}
# The kinds of what `fir-ref run --exhaustive` prints (ADR-2026-10-30-2218).
OUTCOMES = "outcomes"
BUDGET_EXCEEDED = "choice-budget-exceeded"


@dataclass(frozen=True)
class Ran:
    """How a process ended: its exit status (negative for a signal, None
    when it timed out) and what it printed."""

    status: int | None
    stdout: str
    stderr: str


@dataclass(frozen=True)
class Verdict:
    """One file's verdict, and for a parse error its position."""

    verdict: str
    position: tuple[int, int] | None = None
    message: str = ""

    def show(self) -> str:
        if self.position is None:
            return self.verdict
        return f"{self.verdict} at {self.position[0]}:{self.position[1]}"


def run(cmd: list[str]) -> Ran:
    """Runs `cmd`. Raises OSError when it cannot be started."""
    try:
        p = subprocess.run(
            cmd,
            capture_output=True,
            check=False,
            stdin=subprocess.DEVNULL,
            timeout=TIMEOUT,
        )
    except subprocess.TimeoutExpired as e:
        return Ran(None, decode(e.stdout), decode(e.stderr))
    return Ran(p.returncode, decode(p.stdout), decode(p.stderr))


def decode(b: bytes | None) -> str:
    return (b or b"").decode("utf-8", errors="backslashreplace")


def ending(ran: Ran) -> str:
    if ran.status is None:
        return f"does not end within {TIMEOUT} seconds"
    if ran.status < 0:
        return f"is killed by signal {-ran.status}"
    return f"exits with {ran.status}"


def with_stderr(text: str, ran: Ran) -> str:
    lines = ran.stderr.strip().splitlines()
    return f"{text}: {lines[0]}" if lines else text


def failure(ran: Ran) -> str:
    """How a process failed, in one line."""
    return with_stderr(ending(ran), ran)


def no_report(ran: Ran) -> str:
    """How a process failed that ends as it should, but does not print one
    JSON object on one line: what it printed instead."""
    lines = ran.stdout.strip().splitlines()
    if not lines:
        printed = "nothing"
    elif len(lines) == 1:
        printed = lines[0]
    else:
        printed = f"{len(lines)} lines, the first {lines[0]}"
    return with_stderr(f"{ending(ran)} and prints {printed}, not one JSON report", ran)


def one_json_line(text: str):
    """The JSON object that `text` holds on one line, or None."""
    lines = text.splitlines()
    if len(lines) != 1:
        return None
    try:
        value = json.loads(lines[0])
    except json.JSONDecodeError:
        return None
    return value if isinstance(value, dict) else None


def strings(value) -> tuple[str, ...] | None:
    if isinstance(value, list) and all(isinstance(v, str) for v in value):
        return tuple(value)
    return None


def read_outcome(obj: dict) -> Outcome | None:
    """One outcome, as `fir-ref run` writes it (ADR-2026-10-30-1856):
    `return` with its values, `ub` or `stuck` with a reason, or
    `fuel-exhausted`."""
    kind = obj.get("kind")
    if kind == RETURN:
        values = strings(obj.get("values"))
        return None if values is None else Outcome(RETURN, values)
    if kind in (UB, STUCK) and isinstance(obj.get("reason"), str):
        return Outcome(kind, reason=obj["reason"])
    if kind == FUEL_EXHAUSTED:
        return Outcome(FUEL_EXHAUSTED)
    return None


def count(value) -> int | None:
    if isinstance(value, int) and not isinstance(value, bool) and value >= 0:
        return value
    return None


def path(ran: Ran) -> Path | str:
    """What `fir-ref run` reports in scripted or sampled mode
    (ADR-2026-10-30-2218, ADR-2026-10-31-0002): one outcome, with the number
    of `choices` the path made and, in sampled mode, the `sequence` it drew.
    The exit status is 1 for `stuck`, and 0 otherwise."""
    if ran.status not in (0, 1):
        return failure(ran)
    obj = one_json_line(ran.stdout)
    if obj is None:
        return no_report(ran)
    o = read_outcome(obj)
    choices = count(obj.get("choices"))
    sequence = strings(obj.get("sequence")) if "sequence" in obj else None
    status = 1 if obj.get("kind") == STUCK else 0
    bad_sequence = "sequence" in obj and sequence is None
    if o is None or choices is None or bad_sequence or ran.status != status:
        return f"exits with {ran.status} and prints {ran.stdout.strip()}"
    return Path(o, choices, sequence)


def outcomes(ran: Ran) -> Outcomes | BudgetExceeded | str:
    """What `fir-ref run --exhaustive` reports (ADR-2026-10-30-2218): every
    outcome of the run and the most `choices` that one path made, with exit
    status 1 when one is `stuck` and 0 otherwise; or that a path would
    choose more bits than the `budget`, with exit status 0."""
    if ran.status not in (0, 1):
        return failure(ran)
    obj = one_json_line(ran.stdout)
    if obj is None:
        return no_report(ran)
    kind = obj.get("kind")
    bad = f"exits with {ran.status} and prints {ran.stdout.strip()}"
    if kind == BUDGET_EXCEEDED:
        budget = count(obj.get("budget"))
        return bad if budget is None or ran.status != 0 else BudgetExceeded(budget)
    items = obj.get("outcomes")
    choices = count(obj.get("choices"))
    if kind != OUTCOMES or choices is None or not isinstance(items, list):
        return bad
    found = [read_outcome(i) if isinstance(i, dict) else None for i in items]
    if not found or None in found:
        return bad
    status = 1 if any(o.kind == STUCK for o in found) else 0
    return bad if ran.status != status else Outcomes(choices, tuple(found))


def native_values(ran: Ran) -> tuple[str, ...] | str:
    """The values that a built executable prints (ADR-2026-10-30-1233):
    `{"values":[...]}` and exit status 0, and nothing on standard error."""
    if ran.status != 0:
        return failure(ran)
    obj = one_json_line(ran.stdout)
    if obj is None:
        return no_report(ran)
    values = strings(obj.get("values"))
    if values is None or list(obj) != ["values"] or ran.stderr:
        return f"exits with 0 and prints {ran.stdout.strip()} {ran.stderr.strip()}"
    return values


def verdict(ran: Ran) -> Verdict | str:
    """The verdict on one file of `funk verify --json` or `fir-ref
    validate` (ADR-2026-10-30-1032, ADR-2026-10-30-1741)."""
    if ran.status not in (0, 1, 2):
        return failure(ran)
    obj = one_json_line(ran.stdout)
    if obj is None:
        return no_report(ran)
    v = obj.get("verdict")
    diags = obj.get("diagnostics")
    if v not in STATUS or not isinstance(diags, list):
        return f"prints {ran.stdout.strip()}"
    if ran.status != STATUS[v]:
        return f"exits with {ran.status} but reports {v}"
    first = diags[0] if diags and isinstance(diags[0], dict) else {}
    message = first.get("message", "")
    if v != PARSE_ERROR:
        return Verdict(v, message=message)
    line, col = first.get("line"), first.get("column")
    if not isinstance(line, int) or not isinstance(col, int):
        return f"reports a parse error without its position: {ran.stdout.strip()}"
    return Verdict(v, (line, col), message)


def build_failure(ran: Ran) -> str | None:
    """Why `funk build --json` built nothing, or None when it built
    (ADR-2026-10-30-1326)."""
    obj = one_json_line(ran.stdout)
    if obj is None:
        return no_report(ran) if ran.status in (0, 1, 2) else failure(ran)
    if obj.get("verdict") == ACCEPTED and ran.status == 0:
        return None
    diags = obj.get("diagnostics") or []
    why = "; ".join(d.get("message", "") for d in diags[:3] if isinstance(d, dict))
    more = f" and {len(diags) - 3} more" if len(diags) > 3 else ""
    return f"{obj.get('verdict')}: {why}{more}"
