"""Tests of how the harness reads the corpus and its format."""

import tempfile
import tomllib
import unittest
from pathlib import Path

from corpus import DEFAULT_FUEL, Test, load, parse_rejects, parse_tests, result_types
from sets import Declared

SEVEN = "func @seven() -> i32 {\n^entry:\n  %c: i32 = const 7 @0\n  ret %c @0\n}\n"
REJECT = '[[reject]]\nverdict = "parse-error"\nrule = "r"\ntext = "x"\n'


class Tests(unittest.TestCase):
    def parse(self, toml: str):
        return parse_tests(tomllib.loads(toml), "canonical/m.fir")

    def test_differential_and_interpreter_only_tests(self):
        tests, problems = self.parse(
            "tests = [\n"
            '  { func = "@add3", args = ["1", "2", "3"] },\n'
            "  { func = '@\"a b\"', fuel = 2 },\n"
            '  { func = "@odd", args = ["1"], expect = ["-63", "poison"] },\n'
            '  { func = "@f", expect = "ub" },\n'
            '  { func = "@g", fuel = 1, expect = "fuel-exhausted" },\n'
            '  { func = "@none", expect = [] },\n'
            "]\n"
        )
        self.assertEqual(problems, [])
        m = "canonical/m.fir"
        self.assertEqual(
            tests,
            [
                Test(m, "@add3", ("1", "2", "3")),
                Test(m, '@"a b"', (), 2),
                Test(m, "@odd", ("1",), DEFAULT_FUEL, ("-63", "poison")),
                Test(m, "@f", (), DEFAULT_FUEL, "ub"),
                Test(m, "@g", (), 1, "fuel-exhausted"),
                Test(m, "@none", (), DEFAULT_FUEL, ()),
            ],
        )
        self.assertEqual(tests[0].show(), "canonical/m.fir @add3 1 2 3")
        self.assertEqual(tests[1].show(), 'canonical/m.fir --fuel 2 @"a b"')
        self.assertTrue(tests[2].show().endswith("(interpreter only)"))

    def test_choices_and_declared_results(self):
        tests, problems = self.parse(
            "tests = [\n"
            '  { func = "@f", args = ["1"], choices = ["-1", "true"], expect = ["0"] },\n'
            '  { func = "@g", args = ["1"], results = [\n'
            '    { values = ["0"], witness = ["5"] },\n'
            '    { values = ["poison"], witness = [] },\n'
            "  ] },\n"
            "]\n"
        )
        self.assertEqual(problems, [])
        m = "canonical/m.fir"
        self.assertEqual(
            tests,
            [
                Test(m, "@f", ("1",), DEFAULT_FUEL, ("0",), ("-1", "true")),
                Test(
                    m,
                    "@g",
                    ("1",),
                    results=(Declared(("0",), ("5",)), Declared(("poison",), ())),
                ),
            ],
        )
        self.assertEqual(
            tests[0].show(), "canonical/m.fir --choices -1,true @f 1 (interpreter only)"
        )
        self.assertEqual(tests[1].show(), "canonical/m.fir @g 1")

    def test_format_errors(self):
        for toml, needle in [
            ('test = [{ func = "@f" }]', "unknown key test"),
            ('tests = [{ func = "@f", choices = ["1"] }]', "choices go with expect"),
            (
                'tests = [{ func = "@f", choices = ["1,2"], expect = [] }]',
                "choices is a list of values",
            ),
            (
                'tests = [{ func = "@f", choices = [""], expect = [] }]',
                "choices is a list of values",
            ),
            (
                'tests = [{ func = "@f", choices = 1, expect = [] }]',
                "choices is a list of values",
            ),
            (
                'tests = [{ func = "@f", expect = [], results = [] }]',
                "results go with a differential test",
            ),
            ('tests = [{ func = "@f", results = [] }]', "results is a list"),
            ('tests = [{ func = "@f", results = ["0"] }]', "result 1 is a table"),
            (
                'tests = [{ func = "@f", results = [{ values = ["0"] }] }]',
                "result 1: witness is a list",
            ),
            (
                'tests = [{ func = "@f", results = [{ witness = [] }] }]',
                "result 1: values is a list",
            ),
            (
                'tests = [{ func = "@f", results = [{ values = [0], witness = [] }] }]',
                "result 1: values is a list",
            ),
            (
                'tests = [{ func = "@f", results = [{ values = [], witness = ["a,b"] }] }]',
                "result 1: witness is a list",
            ),
            (
                'tests = [{ func = "@f", results = [{ values = [], witness = [], w = 1 }] }]',
                "result 1: unknown key w",
            ),
            (
                (
                    'tests = [{ func = "@f", results = [{ values = ["0"], witness = ["1"] },'
                    ' { values = ["0"], witness = ["2"] }] }]'
                ),
                "result 2 declares the values of an earlier result",
            ),
            ('tests = [{ fun = "@f" }]', "test 1: unknown key fun"),
            ('tests = [{ func = "f" }]', "func is the function's symbol"),
            ('tests = [{ func = "@f", args = [1] }]', "args is a list of strings"),
            ('tests = [{ func = "@f", fuel = -1 }]', "fuel is a number"),
            ('tests = [{ func = "@f", fuel = true }]', "fuel is a number"),
            ('tests = [{ func = "@f", expect = "stuck" }]', "expect is a list"),
            ('tests = [{ func = "@f", expect = [1] }]', "expect is a list"),
            ('tests = ["@f"]', "a test is a table"),
            ("tests = 1", "tests is a list"),
        ]:
            tests, problems = self.parse(toml)
            self.assertEqual(tests, [], toml)
            self.assertTrue(any(needle in p for p in problems), (toml, problems))


class Rejects(unittest.TestCase):
    def test_texts(self):
        data = tomllib.loads(
            "[[reject]]\n"
            'verdict = "parse-error"\n'
            'rule = "a carriage return is not allowed"\n'
            'text = "locs {\\r\\n}\\r\\n"\n'
            "[[reject]]\n"
            'verdict = "validation-error"\n'
            'rule = "symbols are unique"\n'
            "text = '''\nlocs {\n}\n'''\n"
            "[[reject]]\n"
            'verdict = "parse-error"\n'
            'rule = "a text is UTF-8"\n'
            'text = ["locs {\\n  @0 = name(\\"a", 0xff, "b\\")\\n}\\n"]\n'
        )
        rejects, problems = parse_rejects(data, "reject/r.toml")
        self.assertEqual(problems, [])
        self.assertEqual(rejects[0].name, "reject/r.toml #1")
        self.assertEqual(rejects[0].text, b"locs {\r\n}\r\n")
        self.assertEqual(rejects[1].verdict, "validation-error")
        self.assertEqual(rejects[1].text, b"locs {\n}\n")
        self.assertEqual(rejects[2].text, b'locs {\n  @0 = name("a\xffb")\n}\n')

    def test_format_errors(self):
        for toml, needle in [
            ('[[reject]]\nverdict = "accepted"\nrule = "r"\ntext = ""', "verdict is"),
            ('[[reject]]\nverdict = "parse-error"\ntext = ""', "rule says"),
            ('[[reject]]\nverdict = "parse-error"\nrule = "r"', "text is"),
            (
                '[[reject]]\nverdict = "parse-error"\nrule = "r"\ntext = ""\nx = 1',
                "unknown key x",
            ),
            (
                '[[reject]]\nverdict = "parse-error"\nrule = "r"\ntext = ["a", 256]',
                "text is a string, or a list",
            ),
            (
                '[[reject]]\nverdict = "parse-error"\nrule = "r"\ntext = [true]',
                "text is a string, or a list",
            ),
            ("rejects = 1", "unknown key rejects"),
        ]:
            rejects, problems = parse_rejects(tomllib.loads(toml), "reject/r.toml")
            self.assertEqual(rejects, [], toml)
            self.assertTrue(any(needle in p for p in problems), (toml, problems))


class ResultTypes(unittest.TestCase):
    def test_signatures(self):
        text = (
            "func @none() {\n^e:\n  ret @0\n}\n\n"
            + SEVEN
            + '\nfunc @"a) -> b \\" {"(%x: i8, %y: i16) -> i16, i8, i8 {\n'
            "^e:\n  ret %y, %x, %x @0\n}\n\n"
            "func @t(%x: toy.t(i8, 2)) -> toy.t(i8, 2), i1 {\n^e:\n  ret @0\n}\n"
        )
        self.assertEqual(
            result_types(text),
            {
                "@none": [],
                "@seven": ["i32"],
                '@"a) -> b \\" {"': ["i16", "i8", "i8"],
                "@t": ["toy.t(i8, 2)", "i1"],
            },
        )


class Layout(unittest.TestCase):
    def test_the_corpus_has_a_place_for_each_file(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            for name, text in [
                ("README.md", ""),
                ("canonical/seven.fir", SEVEN),
                ("canonical/seven.toml", 'tests = [{ func = "@seven" }]\n'),
                ("canonical/lost.toml", "tests = []\n"),
                ("canonical/notes.txt", ""),
                ("noncanonical/seven.fir", SEVEN),
                ("noncanonical/orphan.fir", SEVEN),
                ("reject/r.toml", "reject = []\n"),
                ("reject/r.fir", ""),
                ("other/x.fir", ""),
            ]:
                (root / name).parent.mkdir(exist_ok=True)
                (root / name).write_text(text)
            c = load(root)
        self.assertEqual([m.name for m in c.modules], ["canonical/seven.fir"])
        self.assertEqual(c.modules[0].tests, [Test("canonical/seven.fir", "@seven")])
        self.assertEqual(
            [n for n, _ in c.inputs],
            ["noncanonical/orphan.fir", "noncanonical/seven.fir"],
        )
        errors = "\n".join(c.errors)
        for needle in [
            "lost.toml: there is no lost.fir",
            "notes.txt: the corpus has no place",
            "orphan.fir: there is no canonical/orphan.fir",
            "r.fir: the corpus has no place",
            "other: the corpus has no place",
            "reject: the corpus has no must-reject texts",
        ]:
            self.assertIn(needle, errors)
        self.assertEqual(len(c.errors), 6, errors)

    def test_a_corpus_has_canonical_modules_and_must_reject_texts(self):
        with tempfile.TemporaryDirectory() as d:
            (Path(d) / "README.md").write_text("")
            c = load(Path(d))
        self.assertEqual(len(c.errors), 2, c.errors)
        self.assertIn("the corpus has no canonical modules", c.errors[0])
        self.assertIn("the corpus has no must-reject texts", c.errors[1])

    def test_a_corpus_with_must_reject_texts(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            for name, text in [
                ("canonical/seven.fir", SEVEN),
                ("reject/r.toml", REJECT),
            ]:
                (root / name).parent.mkdir(exist_ok=True)
                (root / name).write_text(text)
            c = load(root)
        self.assertEqual(c.errors, [])
        self.assertEqual([r.name for r in c.rejects], ["reject/r.toml #1"])


if __name__ == "__main__":
    unittest.main()
