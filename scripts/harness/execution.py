"""Process adapter for the judgement module's decoded tool runs.

Timeouts, native-only resource limits and JSON checks remain in `tools`.
This adapter owns command spelling, file/function selection and fuel.
Every run of fir-ref is at the empty scripted world, so that it reports
the end of each return (docs/decisions/fir-ref-run-end.md).
"""

import os
from pathlib import Path

import tools
from corpus import Test
from differential import Runs


class ProcessRuns(Runs):
    def __init__(
        self,
        fir_ref: str,
        path: Path,
        test: Test,
        exe: Path | str,
        bits: int | None = None,
    ):
        self.fir_ref = fir_ref
        self.path = path
        self.test = test
        self.exe = exe
        self.bits = bits
        self.unavailable = None if isinstance(exe, Path) else exe

    def _reference(self, args: tuple[str, ...], *options: str) -> tools.Ran:
        return tools.run(
            [
                self.fir_ref,
                "run",
                "--fuel",
                str(self.test.fuel),
                *self.test.work_item_options(),
                *options,
                "--world",
                os.devnull,
                "--",
                str(self.path),
                self.test.func,
                *args,
            ]
        )

    def exhaustive(self, args: tuple[str, ...], nans: tuple[str, ...] | None = None):
        budget = [] if self.bits is None else ["--choice-bits", str(self.bits)]
        if nans is not None:
            budget += ["--nans", ",".join(nans)]
        ran = self._reference(args, "--exhaustive", *budget)
        return tools.outcomes(ran, world=True)

    def scripted(self, args: tuple[str, ...], choices: tuple[str, ...] | None):
        options = [] if choices is None else ["--choices", ",".join(choices)]
        return tools.path(self._reference(args, *options), world=True)

    def sampled(self, args: tuple[str, ...], seed: int):
        return tools.path(self._reference(args, "--seed", str(seed)), world=True)

    def native(self, args: tuple[str, ...]):
        return tools.native_values(
            tools.run_native([str(self.exe), self.test.func, *args])
        )
