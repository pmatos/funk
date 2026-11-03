"""Tests for scripts/verus_report.py, which reads what Verus printed for
scripts/check-verus.sh. Run:
python -m unittest discover -s scripts -p "test_verus_report.py"
"""

import json
import tomllib
import unittest
from pathlib import Path

from verus_report import REQUIRED, problems

REPO = Path(__file__).resolve().parent.parent

NOTES = {"obligation_proof_notes": [], "failed_proof_notes": []}
CRATE = "funk-start-fds"


def report(functions, verified=4, errors=0, success=True) -> str:
    return json.dumps(
        {
            "verification-results": {
                "success": success,
                "verified": verified,
                "errors": errors,
            },
            "func-details": {f: dict(NOTES) for f in functions},
        },
        indent=2,
    )


VSTD = report(["vstd::function::axiom_fn_mut_call_requires"], verified=900)
RECORD = [
    "funk_start_fds::record::record_slots",
    "funk_start_fds::record::record",
    "funk_start_fds::record::getfd",
]


class Report(unittest.TestCase):
    def test_the_proof_passes(self):
        self.assertEqual(problems(VSTD + "\n" + report(RECORD), [CRATE]), [])

    def test_a_hidden_module(self):
        """m35: `mod record`'s cfg leaves out Linux, and a stray `verus!`
        item in lib.rs keeps the count at one."""
        text = VSTD + report(["funk_start_fds::keep"], verified=1)
        found = problems(text, [CRATE])
        for name in ("record::record", "record::record_slots"):
            self.assertTrue(any(f"funk_start_fds::{name}" in m for m in found), found)

    def test_nothing_verified(self):
        found = problems(VSTD, [CRATE])
        self.assertEqual(found, [f"Verus verified nothing in {CRATE}"])

    def test_a_failed_proof(self):
        text = report(RECORD, errors=1, success=False)
        self.assertTrue(any("Verus failed" in m for m in problems(text, [CRATE])))
        details = json.loads(report(RECORD))
        details["func-details"][RECORD[0]]["failed_proof_notes"] = ["x"]
        found = problems(json.dumps(details), [CRATE])
        self.assertTrue(any("did not prove" in m for m in found), found)

    def test_a_crate_with_nothing_required(self):
        found = problems(report(["other::f"]), ["other"])
        self.assertTrue(any("names no function" in m for m in found), found)

    def test_every_crate_that_opts_in_is_listed(self):
        opted = set()
        for path in REPO.glob("crates/*/Cargo.toml"):
            package = tomllib.loads(path.read_text(encoding="utf-8"))["package"]
            if package.get("metadata", {}).get("verus", {}).get("verify") is True:
                opted.add(package["name"])
        self.assertEqual(set(REQUIRED), opted)


if __name__ == "__main__":
    unittest.main()
