"""The whole harness, run on a small corpus with stand-ins for funk and
fir-ref, so that each kind of failure shows in its report."""

import io
import os
import resource
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

LIMITS = (resource.RLIMIT_DATA, resource.RLIMIT_AS)
# Each stand-in fails unless it runs under the limits on data and address
# space that the harness itself has: only native code runs under the limit.
GUARD = """
kinds = (resource.RLIMIT_DATA, resource.RLIMIT_AS)
limits = [list(resource.getrlimit(r)) for r in kinds]
if limits != OWN:
    sys.exit(f"{sys.argv[1]} runs under the limits {limits}, not {OWN}")
"""

# The executable that the stand-in for funk builds prints its values only
# when it runs under a limit on data and address space.
FUNK = """
if sys.argv[1] == "build":
    out = sys.argv[sys.argv.index("-o") + 1]
    with open(out, "w") as f:
        f.write("#!/bin/sh\\n")
        f.write('[ "$(ulimit -d)" != unlimited ] && [ "$(ulimit -v)" != unlimited ] || exit 3\\n')
        # Native code takes no poison, and gives 8 on the i32 minimum.
        f.write('case " $* " in *" poison "*) exit 4;; esac\\n')
        f.write('case " $* " in *" -2147483648 "*) echo \\'{"values":["8"]}\\'; exit;; esac\\n')
        f.write("echo '{\\"values\\":[\\"7\\"]}'\\n")
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
    "@poisoned": (0, [R % "poison"]),
    "@poisonkept": (0, [R % 7]),
    "@poisonub": (0, [WHY]),
    "@poisonptr": (0, [R % "poison"]),
}
# The one path of scripted mode, by function and choices; any other
# choices do not fit the run.
PATHS = {
    ("@wide", "3"): (R % 7, 1),
    ("@drift", "3"): (R % 7, 1),
    ("@undeclared", "1"): (R % 7, 1),
    ("@pick", "3"): (R % 3, 1),
    ("@poisonwide", "3"): (R % 7, 1),
}
if sys.argv[1] == "run":
    dash = sys.argv.index("--")
    options, func = sys.argv[2:dash], sys.argv[dash + 2]
    # fir-ref gets each poison argument as it is.
    if func.startswith("@poison") and "poison" not in sys.argv[dash + 3:]:
        print(f"fir-ref: {func} is run with no poison", file=sys.stderr)
        sys.exit(2)
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

# Functions that take arguments, which tests give as poison.
PARAMS = {
    "poisoned": "%a: i32, %c: i1",
    "poisonkept": "%a: i32, %c: i1",
    "poisonub": "%a: i32, %c: i1",
    "poisonwide": "%a: i32, %c: i1",
    "poisonptr": "%p: ptr",
}

MODULE = (
    "".join(
        f"func @{f}({PARAMS.get(f, '')}) -> i32 {{\n^entry:\n"
        "  %c: i32 = const 7 @0\n  ret %c @0\n}\n\n"
        for f in NAMES + list(PARAMS)
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
  { func = "@poisoned", args = ["poison", "true"] },
  { func = "@poisonkept", args = ["poison", "true"] },
  { func = "@poisonub", args = ["poison", "poison"] },
  { func = "@poisonptr", args = ["poison"] },
  { func = "@poisoned", args = ["poison", "true"], expect = ["poison"] },
  { func = "@poisonwide", args = ["poison", "true"], results = [{ values = ["7"], witness = ["3"] }] },
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
    (
        'passed  canonical/m.fir @poisoned poison true: fir-ref returns ["poison"];'
        ' native code returns ["7"] on 0 true, and passes on all 5 argument'
        " vectors with stand-ins for poison\n"
    ),
    (
        'failed  canonical/m.fir @poisonkept poison true: fir-ref returns ["7"];'
        ' native code returns ["8"] on -2147483648 true, one of 5 argument'
        " vectors with stand-ins for poison: value 1 is 8, not 7"
    ),
    (
        "invalid canonical/m.fir @poisonub poison poison: fir-ref hits UB (why);"
        ' native code returns ["7"] on 0 false, one of 10 argument vectors with'
        " stand-ins for poison: UB allows any result, so the test proves nothing"
    ),
    (
        'failed  canonical/m.fir @poisonptr poison: fir-ref returns ["poison"];'
        " native code is not run: argument 1 is poison, and ptr has no stand-in"
        " for it: native code fails where fir-ref returns"
    ),
    (
        "passed  canonical/m.fir @poisoned poison true (interpreter only):"
        ' fir-ref returns ["poison"]\n'
    ),
    (
        "failed  canonical/m.fir @poisonwide poison true: "
        + WIDE
        + DECLARES
        + '; native code returns ["8"] on -2147483648 true, one of 5 argument'
        " vectors with stand-ins for poison: the native result refines none of"
        ' the 1 declared results: ["7"]'
    ),
    "27 checks: 10 passed, 12 failed, 5 invalid",
]


def tool(path: Path, body: str, fir_ref: bool):
    """Writes a stand-in: a shell script that runs its Python program."""
    own = [list(resource.getrlimit(r)) for r in LIMITS]
    head = f"import json, os, resource, sys\nFIR_REF = {fir_ref}\nOWN = {own}\n"
    program = head + GUARD + textwrap.dedent(body) + textwrap.dedent(VERDICT)
    script = path.with_suffix(".py")
    script.write_text(program)
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
