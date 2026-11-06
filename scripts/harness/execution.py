"""Process adapter for the judgement module's decoded tool runs.

Timeouts, native-only resource limits and JSON checks remain in `tools`.
This adapter owns command spelling, file/function selection and fuel.
"""

from pathlib import Path

import tools
from corpus import Test
from differential import Runs


class ProcessRuns(Runs):
    def __init__(self, fir_ref: str, path: Path, test: Test, exe: Path | str):
        self.fir_ref = fir_ref
        self.path = path
        self.test = test
        self.exe = exe
        self.unavailable = None if isinstance(exe, Path) else exe

    def _reference(self, args: tuple[str, ...], *options: str) -> tools.Ran:
        return tools.run(
            [
                self.fir_ref,
                "run",
                "--fuel",
                str(self.test.fuel),
                *options,
                "--",
                str(self.path),
                self.test.func,
                *args,
            ]
        )

    def exhaustive(self, args: tuple[str, ...]):
        return tools.outcomes(self._reference(args, "--exhaustive"))

    def scripted(self, args: tuple[str, ...], choices: tuple[str, ...] | None):
        options = [] if choices is None else ["--choices", ",".join(choices)]
        return tools.path(self._reference(args, *options))

    def sampled(self, args: tuple[str, ...], seed: int):
        return tools.path(self._reference(args, "--seed", str(seed)))

    def native(self, args: tuple[str, ...]):
        return tools.native_values(
            tools.run_native([str(self.exe), self.test.func, *args])
        )
