"""What the explorer asks of `funk` and `fir-ref`, as JSON-ready values."""

import tempfile
from contextlib import contextmanager
from pathlib import Path

import corpus
import differential
import sets
import tools
from execution import ProcessRuns

MODULE = "module.fir"
ACCEPTED = tools.ACCEPTED
SKIPPED = "skipped"


class Runs(ProcessRuns):
    """The harness's process adapter, which also records every native run."""

    def __init__(self, fir_ref: str, path: Path, test: corpus.Test, exe: Path | str):
        super().__init__(fir_ref, path, test, exe)
        self.native_runs = []
        self.reference_error = None

    def exhaustive(self, args: tuple[str, ...]):
        result = super().exhaustive(args)
        if isinstance(result, str) and self.reference_error is None:
            self.reference_error = result
        return result

    def native(self, args: tuple[str, ...]):
        result = super().native(args)
        self.native_runs.append({"args": list(args), "result": _values(result)})
        return result

    def exhaustive_within(self, args: tuple[str, ...], bits: int | None):
        if bits is None:
            return self.exhaustive(args)
        options = ("--exhaustive", "--choice-bits", str(bits))
        return tools.outcomes(self._reference(args, *options))


def _values(result):
    if isinstance(result, str):
        return {"error": result}
    return {"values": list(result)}


def outcome(o) -> dict:
    return {
        "kind": o.kind,
        "values": list(o.values),
        "reason": o.reason,
        "shown": o.show(),
    }


def encode_run(result) -> dict:
    """A decoded `fir-ref run` result."""
    if isinstance(result, str):
        return {"kind": "error", "message": result}
    if isinstance(result, sets.BudgetExceeded):
        return {"kind": "budget", "budget": result.budget}
    if isinstance(result, sets.Outcomes):
        found = [outcome(o) for o in result.outcomes]
        return {"kind": "outcomes", "choices": result.choices, "outcomes": found}
    drawn = None if result.sequence is None else list(result.sequence)
    return {
        "kind": "path",
        "outcome": outcome(result.outcome),
        "choices": result.choices,
        "sequence": drawn,
    }


@contextmanager
def workspace(text: str):
    """A private directory that holds `text` as the module to work on."""
    with tempfile.TemporaryDirectory(prefix="fir-explorer-") as d:
        root = Path(d)
        (root / MODULE).write_bytes(text.encode("utf-8"))
        yield root


def report(cmd: list[str]) -> tuple[tools.Ran, dict]:
    """What a tool's one JSON line says, or a report of why there is none."""
    ran = tools.run(cmd)
    obj = tools.one_json_line(ran.stdout)
    if obj is None or "verdict" not in obj:
        return ran, {"verdict": "tool-error", "message": tools.no_report(ran)}
    obj.pop("file", None)
    obj.setdefault("diagnostics", [])
    return ran, obj


def agreement(rust_ran: tools.Ran, lean_ran: tools.Ran) -> dict:
    """Whether the two validators give one verdict, and for a parse error one
    position, as the harness requires of a must-reject text."""
    rust, lean = tools.verdict(rust_ran), tools.verdict(lean_ran)
    if isinstance(rust, str) or isinstance(lean, str):
        why = "; ".join(
            f"{tool} {v}"
            for tool, v in (("funk verify", rust), ("fir-ref validate", lean))
            if isinstance(v, str)
        )
        return {"agree": None, "why": why}
    if rust.verdict == lean.verdict and rust.position == lean.position:
        return {"agree": True, "why": ""}
    why = f"funk verify gives {rust.show()}, and fir-ref validate gives {lean.show()}"
    return {"agree": False, "why": why}


def functions(canonical: str) -> list[dict]:
    params = corpus.param_types(canonical)
    return [
        {"name": name, "params": params.get(name, []), "results": results}
        for name, results in corpus.result_types(canonical).items()
    ]


class Toolchain:
    def __init__(self, funk: str, fir_ref: str):
        self.funk = funk
        self.fir_ref = fir_ref

    def analyze(self, text: str) -> dict:
        """Everything that needs no choice of function."""
        with workspace(text) as root:
            path = str(root / MODULE)
            _, fmt = report([self.funk, "fmt", "--json", path])
            rust_ran, rust = report([self.funk, "verify", "--json", path])
            lean_ran, lean = report([self.fir_ref, "validate", path])
            canonical = fmt.get("text") if fmt["verdict"] == ACCEPTED else None
            return {
                "format": fmt,
                "rust": rust,
                "lean": lean,
                "agreement": agreement(rust_ran, lean_ran),
                "roundTrip": self._round_trip(root, canonical),
                "assembly": self._assembly(path, rust),
                "functions": [] if canonical is None else functions(canonical),
            }

    def _round_trip(self, root: Path, canonical: str | None) -> dict:
        if canonical is None:
            return {"status": SKIPPED, "why": "the module does not parse"}
        printed = root / "printed.fir"
        printed.write_bytes(canonical.encode("utf-8"))
        ran = tools.run([self.fir_ref, "fmt", str(printed)])
        if ran.status != 0:
            return {"status": "rejected", "why": tools.failure(ran)}
        if ran.stdout != canonical:
            return {
                "status": "differs",
                "why": "fir-ref does not reprint funk's text byte for byte",
                "rust": canonical,
                "lean": ran.stdout,
            }
        return {"status": "same", "why": ""}

    def _assembly(self, path: str, rust: dict) -> dict:
        if rust["verdict"] != ACCEPTED:
            return {"verdict": SKIPPED, "why": "the module is not valid"}
        return report([self.funk, "asm", "--json", path])[1]

    def _rejection(self, path: str) -> str | None:
        got = tools.verdict(tools.run([self.fir_ref, "validate", path]))
        if isinstance(got, str):
            return f"fir-ref validate {got}"
        if got.verdict != ACCEPTED:
            return f"fir-ref runs only valid modules, and this one gives {got.show()}"
        return None

    def run(self, text: str, req: dict) -> dict:
        """One `fir-ref run`, in the mode that `req` names."""
        with workspace(text) as root:
            path = root / MODULE
            why = self._rejection(str(path))
            if why is not None:
                return {"kind": "error", "message": why}
            test = corpus.Test("editor", req["func"], tuple(req["args"]), req["fuel"])
            runs = Runs(self.fir_ref, path, test, "not built")
            mode = req["mode"]
            if mode == "exhaustive":
                return encode_run(runs.exhaustive_within(test.args, req["bits"]))
            if mode == "seed":
                return encode_run(runs.sampled(test.args, req["seed"]))
            return encode_run(runs.scripted(test.args, tuple(req["choices"])))

    def compare(self, text: str, req: dict) -> dict:
        """Builds the module, runs the function as native code, and has the
        harness judge whether the result refines `fir-ref`'s."""
        with workspace(text) as root:
            path = root / MODULE
            why = self._rejection(str(path))
            if why is not None:
                return {"status": "unavailable", "detail": why, "why": "", "native": []}
            _, fmt = report([self.funk, "fmt", "--json", str(path)])
            canonical = fmt.get("text", "")
            exe = self._build(root, path)
            if isinstance(exe, str):
                return {"status": "unavailable", "detail": exe, "why": "", "native": []}
            test = corpus.Test("editor", req["func"], tuple(req["args"]), req["fuel"])
            runs = Runs(self.fir_ref, path, test, exe)
            found = differential.evaluate(
                test,
                corpus.result_types(canonical).get(test.func),
                corpus.param_types(canonical).get(test.func),
                runs,
            )
            if runs.reference_error is not None:
                detail = f"fir-ref {runs.reference_error}"
                return {
                    "status": "unavailable",
                    "detail": detail,
                    "why": "",
                    "native": [],
                }
            return {
                "status": found.judgement.status,
                "why": found.judgement.why,
                "detail": found.detail,
                "native": runs.native_runs,
            }

    def _build(self, root: Path, path: Path) -> Path | str:
        exe = root / "exe"
        cmd = [self.funk, "build", "--json", "-o", str(exe), str(path)]
        why = tools.build_failure(tools.run(cmd))
        return exe if why is None else f"is not built: funk build gives {why}"
