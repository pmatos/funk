"""The whole harness, run on a small corpus with stand-ins for funk and
fir-ref, so that each kind of failure shows in its report."""

import io
import os
import sys
import tempfile
import textwrap
import unittest
from contextlib import redirect_stdout
from pathlib import Path

import main

# Both stand-ins accept a text, unless it holds PARSE (a parse error at 2:3)
# or VALIDATE (a validation error). fir-ref takes DISAGREE for VALIDATE.
VERDICT = """
import json, sys
text = open(sys.argv[-1], encoding="utf-8").read()
verdict, diags = "accepted", []
if "PARSE" in text or (FIR_REF and "DISAGREE" in text):
    verdict = "parse-error"
    diags = [{"kind": verdict, "message": "m", "line": 2, "column": 3}]
elif "VALIDATE" in text or "DISAGREE" in text:
    verdict = "validation-error"
    diags = [{"kind": verdict, "message": "m"}]
print(json.dumps({"file": sys.argv[-1], "verdict": verdict, "diagnostics": diags}))
sys.exit(0 if verdict == "accepted" else 1)
"""

FUNK = """
if sys.argv[1] == "build":
    out = sys.argv[sys.argv.index("-o") + 1]
    with open(out, "w") as f:
        f.write("#!/bin/sh\\necho '{\\"values\\":[\\"7\\"]}'\\n")
    os.chmod(out, 0o755)
    print(json.dumps({"file": sys.argv[-1], "verdict": "accepted", "diagnostics": []}))
    sys.exit(0)
"""

FIR_REF = """
if sys.argv[1] == "run":
    func = sys.argv[sys.argv.index("--") + 2]
    print({
        "@seven": '{"kind":"return","values":["7"]}',
        "@eight": '{"kind":"return","values":["8"]}',
        "@ub": '{"kind":"ub","reason":"why"}',
        "@fuel": '{"kind":"fuel-exhausted"}',
    }[func])
    sys.exit(0)
"""

MODULE = (
    "".join(
        f"func @{f}() -> i32 {{\n^entry:\n  %c: i32 = const 7 @0\n  ret %c @0\n}}\n\n"
        for f in ["seven", "eight", "ub", "fuel"]
    )
    + "locs {\n  @0 = unknown\n}\n"
)

TESTS = """
tests = [
  { func = "@seven" },
  { func = "@eight" },
  { func = "@ub" },
  { func = "@fuel" },
  { func = "@ub", expect = "ub" },
  { func = "@eight", expect = ["7"] },
]
"""

REJECTS = """
[[reject]]
verdict = "parse-error"
rule = "both agree"
text = "PARSE"
[[reject]]
verdict = "validation-error"
rule = "both reject, at different stages"
text = "DISAGREE"
[[reject]]
verdict = "parse-error"
rule = "both reject, at the stage the corpus does not name"
text = "VALIDATE"
"""


# The report's lines that show each kind of check.
EXPECTED = [
    "passed  canonical/m.fir: funk verify: accepted; fir-ref validate: accepted",
    (
        "passed  reject/r.toml #1: funk verify: parse-error at 2:3;"
        " fir-ref validate: parse-error at 2:3 (both agree)"
    ),
    (
        "failed  reject/r.toml #2: funk verify: validation-error;"
        " fir-ref validate: parse-error at 2:3"
    ),
    (
        "failed  reject/r.toml #3: funk verify: validation-error;"
        " fir-ref validate: validation-error"
    ),
    (
        'passed  canonical/m.fir @seven: fir-ref returns ["7"];'
        ' native code returns ["7"]'
    ),
    (
        'failed  canonical/m.fir @eight: fir-ref returns ["8"];'
        ' native code returns ["7"]: value 1 is 7, not 8'
    ),
    ('invalid canonical/m.fir @ub: fir-ref hits UB (why); native code returns ["7"]'),
    (
        "invalid canonical/m.fir @fuel: fir-ref runs out of fuel;"
        ' native code returns ["7"]'
    ),
    "passed  canonical/m.fir @ub (interpreter only): fir-ref hits UB (why)",
    (
        "failed  canonical/m.fir @eight (interpreter only): fir-ref returns"
        ' ["8"]: the test expects ["7"]'
    ),
    "11 checks: 5 passed, 4 failed, 2 invalid",
]


def tool(path: Path, body: str, fir_ref: bool):
    """Writes a stand-in: a shell script that runs its Python program."""
    head = f"import json, os, sys\nFIR_REF = {fir_ref}\n"
    script = path.with_suffix(".py")
    script.write_text(head + textwrap.dedent(body) + textwrap.dedent(VERDICT))
    path.write_text(f'#!/bin/sh\nexec "{sys.executable}" "{script}" "$@"\n')
    os.chmod(path, 0o755)


class Harness(unittest.TestCase):
    def test_each_check_is_reported(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            for name, text in [
                ("corpus/canonical/m.fir", MODULE),
                ("corpus/canonical/m.toml", TESTS),
                ("corpus/reject/r.toml", REJECTS),
                ("generated/generated-0.fir", MODULE),
            ]:
                (root / name).parent.mkdir(parents=True, exist_ok=True)
                (root / name).write_text(text)
            tool(root / "funk", FUNK, False)
            tool(root / "fir-ref", FIR_REF, True)
            out = io.StringIO()
            with redirect_stdout(out):
                status = main.main(
                    [
                        "--funk",
                        str(root / "funk"),
                        "--fir-ref",
                        str(root / "fir-ref"),
                        "--generated",
                        str(root / "generated"),
                        str(root / "corpus"),
                    ]
                )
        report = out.getvalue()
        self.assertEqual(status, 1, report)
        for line in EXPECTED:
            self.assertIn(line, report)


if __name__ == "__main__":
    unittest.main()
