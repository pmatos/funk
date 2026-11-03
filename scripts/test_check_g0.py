"""Tests for scripts/check_g0.py. Run: python scripts/test_check_g0.py"""

import tempfile
import unittest
from pathlib import Path

from check_g0 import (
    CORE_POISON,
    CORE_TEXT,
    ROOT,
    core_words,
    generic_files,
    poison_problems,
    problems,
    tokens,
)

CORE_OPS = [
    "const", "add", "sub", "mul", "sdiv", "udiv", "srem", "urem", "and", "or", "xor",
    "shl", "lshr", "ashr", "icmp", "select", "zext", "sext", "trunc", "freeze", "poison",
    "br", "cond_br", "ret", "call",
]  # fmt: skip

CORE_TEXT_SAMPLE = """
/-- Names: "a comment's words are not code". -/
def Op.name : Op → String
  | .add .. => "add" | .ret _ => "ret"
def flags : List Attr := [.word "nsw"]
#guard Op.decode "add" [] [] [] == none
"""

CORE_POISON_SAMPLE = """
/-- The poison class of each core op. -/
def Op.poisonClass : Op → PoisonClass
  | .add .. | .ret _ => .propagates
  | .br => .exception

instance : DialectPoison CoreDialect := ⟨Core.Op.poisonClass⟩
"""


def tree(case: unittest.TestCase, files: dict[str, str]) -> Path:
    """Return a temporary repository root holding these files, removed when
    the test ends."""
    tmp = tempfile.TemporaryDirectory()
    case.addCleanup(tmp.cleanup)
    root = Path(tmp.name)
    samples = {CORE_TEXT: CORE_TEXT_SAMPLE, CORE_POISON: CORE_POISON_SAMPLE}
    for rel, text in {**samples, **files}.items():
        path = root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
    return root


def strings(text: str) -> list[str]:
    return [s for kind, s, _ in tokens(text) if kind == "str"]


class Lexer(unittest.TestCase):
    def test_comments_guards_and_chars_are_not_code(self):
        text = (
            '-- "add" in a line comment\n'
            '/- "sub" /- nested "mul" -/ still "xor" -/\n'
            '/-- "and" in a doc comment -/\n'
            "def f (c : Char) : String :=\n"
            '  if c = \'"\' then "\\\\\\"" else if c = \'\\\'\' then "q" else s!"{c}"\n'
            '#guard isWord "icmp" &&\n'
            '  isWord "ret"\n'
            'def g := "kept"\n'
        )
        self.assertEqual(strings(text), ['\\\\\\"', "q", "kept"])

    def test_names_keep_their_dotted_parts(self):
        names = [s for kind, s, _ in tokens("import Fir.Core.Ops\nopen Core in x'.y₁")]
        self.assertEqual(
            names, ["import", "Fir.Core.Ops", "open", "Core", "in", "x'.y₁"]
        )

    def test_a_quote_after_a_number_is_not_a_char_literal(self):
        self.assertEqual(strings('h.1\' x "ret" \'\\u{e9}\' "y"'), ["ret", "y"])

    def test_lines_are_counted_through_comments_and_strings(self):
        text = '/- one\ntwo -/\n"a\nb"\nr#"c\nd"#\nfoo'
        self.assertEqual([line for _, _, line in tokens(text)], [3, 5, 7])

    def test_raw_strings_have_no_escapes(self):
        text = 'r"\\" "add" r#"a"b"# "ret" r##"x"#y"## r x'
        self.assertEqual(strings(text), ["\\", "add", 'a"b', "ret", 'x"#y'])

    def test_an_interpolation_is_code(self):
        text = 's!"op {f "add" {x := 1}} \\{y} done" ++ m! "{g}" ++ "{z}"'
        self.assertEqual(strings(text), ["op ", "add", " \\{y} done", "{z}"])
        names = [s for kind, s, _ in tokens(text) if kind == "name"]
        self.assertEqual(names, ["s!", "f", "x", "m!", "g"])

    def test_an_indented_command_is_not_code(self):
        text = (
            'section\n  #guard isWord "icmp" &&\n    isWord "ret"\n'
            '  def g := "kept"\n  #v["vec"]\nend\n'
        )
        self.assertEqual(strings(text), ["kept", "vec"])

    def test_a_name_may_quote_its_parts(self):
        names = [s for kind, s, _ in tokens("Fir.«Core».x «fir-ref»")]
        self.assertEqual(names, ["Fir.«Core».x", "«fir-ref»"])


class Rules(unittest.TestCase):
    def test_the_words_are_those_of_the_core_text_code(self):
        self.assertEqual(core_words(tree(self, {})), {"add", "ret", "nsw"})

    def test_generic_files_leave_out_the_core_dialect_and_the_command_line(self):
        root = tree(
            self,
            {
                "lean/Fir/Text/Print.lean": "",
                "lean/Fir/Text/Example.lean": "",
                "lean/Fir/Core/Ops.lean": "",
                "lean/FirRef.lean": "",
                "lean/FirRef/Parse.lean": "",
                "lean/FirRef/Main.lean": "",
                "lean/FirRef/Run.lean": "",
                "lean/FirRef/RunArgs.lean": "",
                "lean/FirRef/Sample.lean": "",
                "lean/FirRef/Decode/Run.lean": "",
                "lean/FirTest/G0.lean": "",
                "lean/FirTest/Run.lean": "",
            },
        )
        self.assertEqual(
            generic_files(root),
            [
                "lean/Fir/Text/Print.lean",
                "lean/FirRef.lean",
                "lean/FirRef/Decode/Run.lean",
                "lean/FirRef/Parse.lean",
                "lean/FirRef/Sample.lean",
                "lean/FirTest/G0.lean",
            ],
        )

    def test_clean_generic_code_passes(self):
        text = 'def kind := "func"\ndef ret : Exit := .ret\n#guard isWord "icmp"\n'
        self.assertEqual(problems(tree(self, {"lean/Fir/Text/Read.lean": text})), [])

    def test_naming_or_importing_the_core_dialect_fails(self):
        text = (
            "import Fir.Core.Ops\nimport Fir.Text.Example\nimport FirRef.Run\n"
            "import Fir.Text.Print\n\ndef f : Dialect := CoreDialect\n"
            "def g := Fir.«Core».x\ndef h := Lean.Core.checkSystem\n"
        )
        self.assertEqual(
            problems(tree(self, {"lean/Fir/Execution/Run.lean": text})),
            [
                "lean/Fir/Execution/Run.lean:1: imports the core dialect: Fir.Core.Ops",
                "lean/Fir/Execution/Run.lean:2: imports the core dialect: Fir.Text.Example",
                "lean/Fir/Execution/Run.lean:3: imports the core dialect: FirRef.Run",
                "lean/Fir/Execution/Run.lean:6: names the core dialect: CoreDialect",
                "lean/Fir/Execution/Run.lean:7: names the core dialect: Fir.«Core».x",
            ],
        )

    def test_g0s_test_may_not_narrow_a_statement_to_the_core_dialect(self):
        text = (
            "import Fir\n\ntheorem t (M : Module CoreDialect) : True := trivial\n"
            '#guard (Core.samples.map Core.Op.name).length == 24 && "add" != ""\n'
        )
        self.assertEqual(
            problems(tree(self, {"lean/FirTest/G0.lean": text})),
            ["lean/FirTest/G0.lean:3: names the core dialect: CoreDialect"],
        )

    def test_writing_a_core_word_fails(self):
        text = 'def isRet (n : String) : Bool := n == "ret" || n == "i32"\n'
        self.assertEqual(
            problems(tree(self, {"lean/FirRef/Parse.lean": text})),
            [
                'lean/FirRef/Parse.lean:1: writes the core dialect\'s word "ret"',
                'lean/FirRef/Parse.lean:1: writes the core dialect\'s word "i32"',
            ],
        )

    def test_a_word_that_names_a_core_op_and_a_generic_term_is_a_core_word(self):
        # `poison` names a core op and S1's deferred-UB value. Generic code
        # may not write it alone as a string, whatever it means there, but
        # may write a sentence that holds it (ADR-2026-11-03-1617).
        core = CORE_TEXT_SAMPLE.replace('"ret"', '"ret" | .poison _ => "poison"')
        generic = (
            'def kind : String := "poison"\n'
            'def why : String := "a poison divisor"\n'
            'def how : String := s!"{kind}: deferred UB"\n'
        )
        root = tree(self, {CORE_TEXT: core, "lean/Fir/Execution/Report.lean": generic})
        self.assertIn("poison", core_words(root))
        self.assertEqual(
            problems(root),
            [
                'lean/Fir/Execution/Report.lean:1: writes the core dialect\'s word "poison"'
            ],
        )
        moved = {CORE_TEXT: core, "lean/Fir/Core/Report.lean": generic}
        self.assertEqual(problems(tree(self, moved)), [])

    def test_corollary_files_may_name_the_core_dialect_but_not_write_its_words(self):
        text = 'import Fir.Core.TextLaws\ntheorem Core.x : "add" = "add" := rfl\n'
        found = problems(tree(self, {"lean/Fir/Text/PrintParse.lean": text}))
        self.assertEqual(
            found,
            [
                'lean/Fir/Text/PrintParse.lean:2: writes the core dialect\'s word "add"',
                'lean/Fir/Text/PrintParse.lean:2: writes the core dialect\'s word "add"',
            ],
        )

    def test_no_words_fails(self):
        root = tree(self, {})
        (root / CORE_TEXT).write_text("", encoding="utf-8")
        self.assertEqual(len(problems(root)), 1)


class PoisonClasses(unittest.TestCase):
    def poison(self, text: str) -> list[str]:
        return poison_problems(tree(self, {CORE_POISON: text}))

    def test_each_op_listed_by_its_constructor_passes(self):
        self.assertEqual(self.poison(CORE_POISON_SAMPLE), [])

    def test_a_case_for_the_rest_fails(self):
        for rest in ["_", "op", "(_)"]:
            text = CORE_POISON_SAMPLE.replace("| .br =>", f"| {rest} =>")
            self.assertEqual(
                self.poison(text),
                [
                    f"{CORE_POISON}:5: Op.poisonClass has a case that is not one op's constructor"
                ],
                rest,
            )

    def test_main_before_this_check_fails(self):
        text = (
            "def Op.poisonClass : Op → PoisonClass\n"
            "  | .select _ | .freeze _ | .br | .condBr | .ret _ | .call .. => .exception\n"
            "  | _ => .propagates\n"
        )
        self.assertEqual(len(self.poison(text)), 1)

    def test_no_class_or_no_case_fails(self):
        self.assertEqual(
            self.poison("def other := 1\n"),
            [f"{CORE_POISON}: no `def Op.poisonClass`, so no op's class is checked"],
        )
        self.assertEqual(
            self.poison(
                "def Op.poisonClass : Op → PoisonClass := fun _ => .exception\n"
            ),
            [f"{CORE_POISON}:1: Op.poisonClass lists no op"],
        )


class Repository(unittest.TestCase):
    def test_the_repository_passes(self):
        self.assertEqual(problems(), [])
        self.assertIn("lean/FirTest/G0.lean", generic_files())

    def test_the_core_words_hold_every_core_op(self):
        self.assertLessEqual(set(CORE_OPS), core_words())
        self.assertLessEqual(
            {"nsw", "nuw", "exact", "slt", "true", "false", "ptr"}, core_words()
        )

    def test_the_parser_printer_validation_and_interpreter_are_checked(self):
        files = generic_files()
        for want in [
            "lean/Fir/Syntax/Module.lean",
            "lean/Fir/Text/Print.lean",
            "lean/Fir/Text/Decode.lean",
            "lean/Fir/Text/ReadOps.lean",
            "lean/Fir/Validation/Rules.lean",
            "lean/Fir/Execution/Interpreter.lean",
            "lean/Fir/Execution/Propagation.lean",
            "lean/FirRef/Parse.lean",
            "lean/FirRef/PrintModule.lean",
        ]:
            self.assertIn(want, files)
        self.assertTrue((ROOT / CORE_TEXT).is_file())


if __name__ == "__main__":
    unittest.main()
