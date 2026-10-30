"""Running funk, fir-ref and native code, and reading what they print.

Each reader takes what a process did, a `Ran`, and returns its result or a
string that says why there is none, so the readers are tested without
running anything.
"""

import json
import subprocess
from dataclasses import dataclass

from refine import FUEL_EXHAUSTED, RETURN, STUCK, UB, Outcome

TIMEOUT = 120

ACCEPTED = "accepted"
PARSE_ERROR = "parse-error"
VALIDATION_ERROR = "validation-error"
VERDICTS = (ACCEPTED, PARSE_ERROR, VALIDATION_ERROR, "io-error")


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


def failure(ran: Ran) -> str:
    """How a process failed, in one line."""
    if ran.status is None:
        how = f"does not end within {TIMEOUT} seconds"
    elif ran.status < 0:
        how = f"is killed by signal {-ran.status}"
    else:
        how = f"exits with {ran.status}"
    lines = ran.stderr.strip().splitlines()
    return f"{how}: {lines[0]}" if lines else how


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


def outcome(ran: Ran) -> Outcome | str:
    """What `fir-ref run` reports (ADR-2026-10-30-1856): exit status 0 with
    `return`, `ub` or `fuel-exhausted`, or 1 with `stuck`."""
    obj = one_json_line(ran.stdout)
    if obj is None or ran.status not in (0, 1):
        return failure(ran)
    kind = obj.get("kind")
    want_status = 1 if kind == STUCK else 0
    if kind == RETURN:
        values = strings(obj.get("values"))
        if values is not None and ran.status == 0:
            return Outcome(RETURN, values)
    elif kind in (UB, STUCK) and isinstance(obj.get("reason"), str):
        if ran.status == want_status:
            return Outcome(kind, reason=obj["reason"])
    elif kind == FUEL_EXHAUSTED and ran.status == 0:
        return Outcome(FUEL_EXHAUSTED)
    return f"exits with {ran.status} and prints {ran.stdout.strip()}"


def native_values(ran: Ran) -> tuple[str, ...] | str:
    """The values that a built executable prints (ADR-2026-10-30-1233):
    `{"values":[...]}` and exit status 0, and nothing on standard error."""
    obj = one_json_line(ran.stdout)
    if ran.status != 0 or obj is None:
        return failure(ran)
    values = strings(obj.get("values"))
    if values is None or list(obj) != ["values"] or ran.stderr:
        return f"exits with 0 and prints {ran.stdout.strip()} {ran.stderr.strip()}"
    return values


def verdict(ran: Ran) -> Verdict | str:
    """The verdict on one file of `funk verify --json` or `fir-ref
    validate` (ADR-2026-10-30-1032, ADR-2026-10-30-1741)."""
    obj = one_json_line(ran.stdout)
    if obj is None or ran.status not in (0, 1, 2):
        return failure(ran)
    v = obj.get("verdict")
    diags = obj.get("diagnostics")
    if v not in VERDICTS or not isinstance(diags, list):
        return f"prints {ran.stdout.strip()}"
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
        return failure(ran)
    if obj.get("verdict") == ACCEPTED and ran.status == 0:
        return None
    diags = obj.get("diagnostics") or []
    why = "; ".join(d.get("message", "") for d in diags[:3] if isinstance(d, dict))
    more = f" and {len(diags) - 3} more" if len(diags) > 3 else ""
    return f"{obj.get('verdict')}: {why}{more}"
