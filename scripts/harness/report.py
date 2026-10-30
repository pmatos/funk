"""The harness's report: one line per check, then the counts."""

from refine import FAILED, INVALID, PASSED


class Report:
    def __init__(self, out):
        self.out = out
        self.counts = {PASSED: 0, FAILED: 0, INVALID: 0}

    def add(self, status: str, what: str, detail: str, quiet: bool = False):
        """Counts one check, and prints it unless it passed quietly."""
        self.counts[status] += 1
        if not (quiet and status == PASSED):
            print(f"{status:<8}{what}: {detail}", file=self.out)

    def note(self, text: str):
        print(f"{'':<8}{text}", file=self.out)

    def ok(self) -> bool:
        return self.counts[FAILED] == 0 and self.counts[INVALID] == 0

    def summary(self) -> str:
        total = sum(self.counts.values())
        parts = ", ".join(f"{n} {s}" for s, n in self.counts.items())
        return f"{total} checks: {parts}"
