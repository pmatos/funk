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
R = '{"kind":"return","values":["%s"]}'
WHY = '{"kind":"ub","reason":"why"}'
FUEL = '{"kind":"fuel-exhausted"}'
# What exhaustive mode prints for each function: the most choices on one
# path and every outcome, or None past the budget.
SETS = {
    "@seven": (0, [R % 7]),
    "@eight": (0, [R % 8]),
    "@ub": (0, [WHY]),
    "@fuel": (0, [FUEL]),
    "@set": (1, [R % 6, R % 7]),
    "@miss": (1, [R % 5, R % 6]),
    "@setub": (1, [R % 7, WHY]),
    "@undeclared": (1, [R % 7, R % 8]),
    "@pick": (1, [R % 3]),
}
# The one path of scripted mode, by function and choices; any other
# choices do not fit the run.
PATHS = {
    ("@wide", "3"): (R % 7, 1),
    ("@drift", "3"): (R % 7, 1),
    ("@undeclared", "1"): (R % 7, 1),
    ("@pick", "3"): (R % 3, 1),
}
if sys.argv[1] == "run":
    dash = sys.argv.index("--")
    options, func = sys.argv[2:dash], sys.argv[dash + 2]
    value = lambda o: options[options.index(o) + 1] if o in options else None
    choices, seed = value("--choices") or "", value("--seed")
    if "--exhaustive" in options:
        if func not in SETS:
            print('{"kind":"choice-budget-exceeded","budget":16}')
        else:
            made, outs = SETS[func]
            print('{"kind":"outcomes","choices":%d,"outcomes":[%s]}' % (made, ",".join(outs)))
        sys.exit(0)
    if seed is not None:
        n = 8 if func == "@drift" and seed == "5" else 7
        print((R % n)[:-1] + ',"choices":1,"sequence":["%s"]}' % seed)
        sys.exit(0)
    if (func, choices) in PATHS:
        out, made = PATHS[(func, choices)]
    elif choices == "" and SETS.get(func, (1,))[0] == 0:
        out, made = SETS[func][1][0], 0
    else:
        print(f"fir-ref: {func}: the choices do not fit the run: they are {choices}", file=sys.stderr)
        sys.exit(2)
    print(out[:-1] + ',"choices":%d}' % made)
    sys.exit(0)
"""

NAMES = ["seven", "eight", "ub", "fuel", "set", "miss", "setub", "wide"]
NAMES += ["stale", "drift", "undeclared", "pick"]

MODULE = (
    "".join(
        f"func @{f}() -> i32 {{\n^entry:\n  %c: i32 = const 7 @0\n  ret %c @0\n}}\n\n"
        for f in NAMES
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
  { func = "@set" },
  { func = "@miss" },
  { func = "@setub" },
  { func = "@wide" },
  { func = "@wide", results = [{ values = ["7"], witness = ["3"] }] },
  { func = "@stale", results = [{ values = ["7"], witness = ["3"] }] },
  { func = "@drift", results = [{ values = ["7"], witness = ["3"] }] },
  { func = "@undeclared", results = [{ values = ["7"], witness = ["1"] }] },
  { func = "@pick", choices = ["3"], expect = ["3"] },
  { func = "@pick", expect = ["3"] },
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
SET = "fir-ref makes 1 choice and gives 2 outcomes"
WIDE = "fir-ref chooses more than its budget of 16 bits"
DECLARES = ", and the test declares 1 result"
NATIVE = '; native code returns ["7"]'
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
    'passed  canonical/m.fir @seven: fir-ref returns ["7"]' + NATIVE + "\n",
    (
        'failed  canonical/m.fir @eight: fir-ref returns ["8"]'
        + NATIVE
        + ": value 1 is 7, not 8"
    ),
    "invalid canonical/m.fir @ub: fir-ref hits UB (why)" + NATIVE,
    "invalid canonical/m.fir @fuel: fir-ref runs out of fuel" + NATIVE,
    "passed  canonical/m.fir @ub (interpreter only): fir-ref hits UB (why)",
    (
        "failed  canonical/m.fir @eight (interpreter only): fir-ref returns"
        ' ["8"]: the test expects ["7"]'
    ),
    "passed  canonical/m.fir @set: " + SET + NATIVE + "\n",
    (
        "failed  canonical/m.fir @miss: "
        + SET
        + NATIVE
        + ': the native result refines none of the 2 outcomes: ["5"], ["6"]'
    ),
    (
        "invalid canonical/m.fir @setub: "
        + SET
        + NATIVE
        + ": the set holds UB (why), which allows any result"
    ),
    (
        "invalid canonical/m.fir @wide: "
        + WIDE
        + NATIVE
        + ": with no set to judge by, the test proves nothing unless it"
        " declares its results, each with a witness"
    ),
    (
        "passed  canonical/m.fir @wide: "
        + WIDE
        + DECLARES
        + NATIVE
        + ": each witness gives its result, and 32 seeded runs give declared"
        " results\n"
    ),
    (
        "failed  canonical/m.fir @stale: "
        + WIDE
        + DECLARES
        + NATIVE
        + ': the witness ["3"] of result 1 does not give it: fir-ref exits'
        " with 2: fir-ref: @stale: the choices do not fit the run"
    ),
    (
        "failed  canonical/m.fir @drift: "
        + WIDE
        + DECLARES
        + NATIVE
        + ': seed 5 draws ["5"] and returns ["8"], which the test does not declare'
    ),
    (
        "failed  canonical/m.fir @undeclared: "
        + SET
        + DECLARES
        + NATIVE
        + ': the test does not declare ["8"], which the set holds'
    ),
    (
        "passed  canonical/m.fir --choices 3 @pick (interpreter only):"
        ' fir-ref returns ["3"]\n'
    ),
    (
        "failed  canonical/m.fir @pick (interpreter only): fir-ref exits with 2:"
        " fir-ref: @pick: the choices do not fit the run"
    ),
    "21 checks: 8 passed, 9 failed, 4 invalid",
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
