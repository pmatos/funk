"""Tests of the corpus of #242's fast-math flags: the committed files of
`tests/fir/canonical/` hold exactly what `float_flag_cases.py` writes, each
expected result follows the flag's rule on `float_ref.py`'s result, and each
flag's cell has a case that the flag decides."""

import tomllib
import unittest

import float_flag_cases as cases
from float_arith_cases import CANONICAL, FORMATS
from float_ref import Format
from float_text import decode


def wrong_expectations(t: str, text: str) -> list[str]:
    """The tests of a committed test file at the type `t` whose expected
    result breaks the flag's rule: poison only when an operand, or the
    result without flags, is a NaN under `nnan` or an infinity under
    `ninf`; a zero under `nsz` with its sign flipped by the choice `true`;
    and otherwise the result without flags."""
    e, m = FORMATS[t]
    f = Format(e, m)
    wrong = []
    for test in tomllib.loads(text)["tests"]:
        if "expect" not in test:
            continue
        [want] = test["expect"]
        op, flag = test["func"][1:].split("_")
        bits = [decode(e, m, a) for a in test["args"]]
        r = cases.plain(f, op, flag, bits)
        kinds = [f.decode(b)[0] for b in bits]
        if op != "fcmp":
            kinds.append(f.decode(r)[0])
        breaks = {"nnan": "nan", "ninf": "inf", "nsz": None}[flag] in kinds
        if breaks:
            ok = want == "poison"
        elif op == "fcmp":
            ok = want == ("true" if r else "false")
        else:
            flip = test.get("choices") == ["true"]
            if "choices" in test and not (flag == "nsz" and kinds[-1] == "zero"):
                ok = False
            else:
                ok = want != "poison" and decode(e, m, want) == r ^ (
                    f.sign_bit if flip else 0
                )
        if not ok:
            wrong.append(str(test))
    return wrong


class Tests(unittest.TestCase):
    def test_the_committed_corpus_is_what_the_generator_writes(self):
        for path, text in cases.files().items():
            with self.subTest(path=path):
                committed = (CANONICAL / path).read_text(encoding="utf-8")
                self.assertEqual(committed, text)

    def test_each_expected_result_follows_the_flag_s_rule(self):
        for t in FORMATS:
            path = CANONICAL / f"float-flags-{t}.toml"
            with self.subTest(path=path.name):
                text = path.read_text(encoding="utf-8")
                self.assertEqual(wrong_expectations(t, text), [])

    def test_a_wrong_expected_result_is_found(self):
        text = (CANONICAL / "float-flags-f32.toml").read_text(encoding="utf-8")
        for old, new in [
            ('args = ["1.0", "2.0"], expect = ["3.0"]', 'expect = ["poison"]'),
            ('args = ["0x7fc00000", "1.0"], expect = ["poison"]', 'expect = ["1.0"]'),
            ('choices = ["true"], expect = ["0.0"]', 'expect = ["-0.0"]'),
        ]:
            with self.subTest(old=old):
                planted = text.replace(old, old.split("expect")[0] + new, 1)
                self.assertNotEqual(planted, text)
                self.assertEqual(len(wrong_expectations("f32", planted)), 1)

    def test_each_flag_decides_a_case_of_each_op(self):
        for t, (e, m) in FORMATS.items():
            f = Format(e, m)
            named = cases.values(f)
            for flag in cases.FLAGS:
                for op, _ in cases.OPS:
                    with self.subTest(t=t, op=op, flag=flag):
                        decided = [
                            case
                            for case in cases.CASES[flag][op]
                            if cases.flagged(
                                f, op, flag, bits := [named[a] for a in case]
                            )
                            != [cases.plain(f, op, flag, bits)]
                        ]
                        if op == "fcmp" and flag == "nsz":
                            self.assertEqual(decided, [])
                        else:
                            self.assertTrue(decided)
                            self.assertLess(len(decided), len(cases.CASES[flag][op]))

    def test_every_op_with_every_flag_is_a_function(self):
        text = (CANONICAL / "float-flags-f64.fir").read_text(encoding="utf-8")
        for flag in cases.FLAGS:
            for op, _ in cases.OPS:
                self.assertIn(f"func @{op}_{flag}(", text)
                self.assertIn(f"= {op} {flag} ", text)


if __name__ == "__main__":
    unittest.main()
