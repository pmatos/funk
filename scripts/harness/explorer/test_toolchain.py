"""The explorer against stand-in tools, so that each disagreement is planted."""

import json
import os
import stat
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path
from unittest import mock

import tools

from explorer.toolchain import Toolchain

TEXT = "func @f(%a: i8) -> i8 {\n^entry:\n  ret %a @0\n}\n\nlocs {\n  @0 = unknown\n}\n"
CALL = {"func": "@f", "args": ["1"], "fuel": 1000}


def accepted(**extra) -> str:
    return json.dumps({"file": "x", "verdict": "accepted", "diagnostics": [], **extra})


class Stand(unittest.TestCase):
    def setUp(self):
        d = tempfile.TemporaryDirectory()
        self.addCleanup(d.cleanup)
        self.dir = Path(d.name)
        self.funk_script()
        self.lean_script()

    def script(self, name: str, body: str) -> str:
        path = self.dir / name
        path.write_text(f"#!{sys.executable}\n" + textwrap.dedent(body))
        path.chmod(path.stat().st_mode | stat.S_IEXEC)
        return str(path)

    def funk_script(
        self, verify=None, native='print(\'{"values":["2"]}\')', build=True
    ):
        verify = verify or accepted()
        reply = {
            "fmt": accepted(canonical=True, text=TEXT),
            "verify": verify,
            "asm": accepted(text="f:\n\tret\n"),
        }
        self.funk = self.script(
            "funk",
            f"""
            import os, sys
            cmd = sys.argv[1]
            if cmd == "build":
                if not {build!r}:
                    print('{{"verdict":"unsupported","diagnostics":[{{"message":"not i7"}}]}}')
                    sys.exit(1)
                exe = sys.argv[sys.argv.index("-o") + 1]
                with open(exe, "w") as f:
                    f.write("#!" + sys.executable + "\\n" + {native!r} + "\\n")
                os.chmod(exe, 0o755)
                print('{{"verdict":"accepted","diagnostics":[]}}')
            else:
                print({reply!r}[cmd])
                sys.exit(0 if {verify!r} == {accepted()!r} or cmd != "verify" else 1)
            """,
        )

    def lean_script(self, validate=None, reprint=TEXT):
        validate = validate or accepted()
        self.lean = self.script(
            "fir-ref",
            f"""
            import sys
            cmd = sys.argv[1]
            if cmd == "validate":
                print({validate!r})
                sys.exit(0 if {validate!r} == {accepted()!r} else 1)
            if cmd == "fmt":
                sys.stdout.write({reprint!r})
            if cmd == "run":
                if "--exhaustive" in sys.argv:
                    print('{{"kind":"outcomes","choices":0,"outcomes":[{{"kind":"return","values":["2"]}}]}}')
                elif "--seed" in sys.argv:
                    print('{{"kind":"return","values":["2"],"choices":1,"sequence":["7"]}}')
                else:
                    print('{{"kind":"return","values":["2"],"choices":0}}')
            """,
        )

    def chain(self) -> Toolchain:
        return Toolchain(self.funk, self.lean)


class AnalyzeTest(Stand):
    def test_agreeing_tools_report_every_pane(self):
        a = self.chain().analyze(TEXT)
        self.assertEqual(a["agreement"]["agree"], True)
        self.assertEqual(a["roundTrip"]["status"], "same")
        self.assertEqual(a["assembly"]["text"], "f:\n\tret\n")
        self.assertEqual(
            a["functions"], [{"name": "@f", "params": ["i8"], "results": ["i8"]}]
        )

    def test_rust_and_lean_disagreeing_is_reported(self):
        rejected = json.dumps(
            {
                "verdict": "validation-error",
                "diagnostics": [{"kind": "validation", "message": "no"}],
            }
        )
        self.lean_script(validate=rejected)
        a = self.chain().analyze(TEXT)
        self.assertIs(a["agreement"]["agree"], False)
        self.assertIn("validation-error", a["agreement"]["why"])

    def test_lean_reprinting_other_bytes_is_reported(self):
        self.lean_script(reprint=TEXT + "\n")
        a = self.chain().analyze(TEXT)
        self.assertEqual(a["roundTrip"]["status"], "differs")

    def test_an_invalid_module_has_no_assembly(self):
        rejected = json.dumps(
            {
                "verdict": "parse-error",
                "diagnostics": [{"message": "no", "line": 1, "column": 1}],
            }
        )
        self.funk_script(verify=rejected)
        self.lean_script(validate=rejected)
        a = self.chain().analyze("nope")
        self.assertEqual(a["assembly"]["verdict"], "skipped")
        self.assertIs(a["agreement"]["agree"], True)


class RunTest(Stand):
    def test_each_mode_decodes(self):
        chain = self.chain()
        every = chain.run(TEXT, {**CALL, "mode": "exhaustive", "bits": 8})
        self.assertEqual(every["kind"], "outcomes")
        self.assertEqual(every["outcomes"][0]["values"], ["2"])
        one = chain.run(TEXT, {**CALL, "mode": "seed", "seed": 3})
        self.assertEqual(one["sequence"], ["7"])
        path = chain.run(TEXT, {**CALL, "mode": "scripted", "choices": []})
        self.assertEqual(path["outcome"]["kind"], "return")

    def test_an_invalid_module_is_not_run(self):
        rejected = json.dumps({"verdict": "parse-error", "diagnostics": []})
        self.lean_script(validate=rejected)
        got = self.chain().run(TEXT, {**CALL, "mode": "seed", "seed": 1})
        self.assertEqual(got["kind"], "error")


class CompareTest(Stand):
    def test_a_native_result_in_the_set_refines(self):
        got = self.chain().compare(TEXT, CALL)
        self.assertEqual(got["status"], "passed")
        self.assertEqual(got["native"][0]["result"], {"values": ["2"]})

    def test_a_planted_wrong_native_result_does_not_refine(self):
        self.funk_script(native='print(\'{"values":["9"]}\')')
        got = self.chain().compare(TEXT, CALL)
        self.assertEqual(got["status"], "failed")
        self.assertIn("9", got["detail"])

    def test_a_module_the_backend_cannot_lower_says_why(self):
        self.funk_script(build=False)
        got = self.chain().compare(TEXT, CALL)
        self.assertEqual(got["status"], "unavailable")
        self.assertEqual(got["native"], [])
        self.assertIn("not i7", got["detail"])

    def test_a_reference_run_that_fails_is_not_called_a_refinement_failure(self):
        self.lean = self.script(
            "fir-ref-bad",
            """
            import sys
            if sys.argv[1] == "validate":
                print('{"verdict":"accepted","diagnostics":[]}')
            else:
                print("fir-ref: bad argument", file=sys.stderr)
                sys.exit(2)
            """,
        )
        got = self.chain().compare(TEXT, {**CALL, "args": ["nope"]})
        self.assertEqual(got["status"], "unavailable")
        self.assertIn("bad argument", got["detail"])

    def test_a_program_that_never_ends_is_stopped_and_reported(self):
        self.funk_script(native="import time; time.sleep(60)")
        with mock.patch.object(tools, "TIMEOUT", 1):
            got = self.chain().compare(TEXT, CALL)
        self.assertEqual(got["status"], "failed")
        self.assertIn("does not end within 1 seconds", got["detail"])

    def test_no_temporary_directory_is_left_behind(self):
        with (
            tempfile.TemporaryDirectory() as d,
            mock.patch.dict(os.environ, {"TMPDIR": d}),
        ):
            tempfile.tempdir = None
            self.addCleanup(setattr, tempfile, "tempdir", None)
            self.chain().compare(TEXT, CALL)
            self.assertEqual(os.listdir(d), [])
