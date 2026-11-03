"""Tests for scripts/check_g0.py. Run: python scripts/test_check_g0.py"""

import tempfile
import unittest
from pathlib import Path

from check_g0 import CORE_TEXT, ROOT, core_words, generic_files, problems, tokens

CORE_OPS = [
    "const", "add", "sub", "mul", "sdiv", "udiv", "srem", "urem", "and", "or", "xor",
    "shl", "lshr", "ashr", "icmp", "select", "zext", "sext", "trunc", "freeze", "br",
    "cond_br", "ret", "call",
]  # fmt: skip

CORE_TEXT_SAMPLE = """
/-- Names: "a comment's words are not code". -/
def Op.name : Op → String
  | .add .. => "add" | .ret _ => "ret"
def flags : List Attr := [.word "nsw"]
#guard Op.decode "add" [] [] [] == none
"""


def tree(files: dict[str, str]) -> Path:
    """Return a temporary repository root holding these files."""
    root = Path(tempfile.mkdtemp())
    for rel, text in {CORE_TEXT: CORE_TEXT_SAMPLE, **files}.items():
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
        self.assertEqual(strings(text), ['\\\\\\"', "q", "{c}", "kept"])

    def test_names_keep_their_dotted_parts(self):
        names = [s for kind, s, _ in tokens("import Fir.Core.Ops\nopen Core in x'.y₁")]
        self.assertEqual(
            names, ["import", "Fir.Core.Ops", "open", "Core", "in", "x'.y₁"]
        )

    def test_a_quote_after_a_number_is_not_a_char_literal(self):
        self.assertEqual(strings('h.1\' x "ret" \'\\u{e9}\' "y"'), ["ret", "y"])

    def test_lines_are_counted_through_comments_and_strings(self):
        text = '/- one\ntwo -/\n"a\nb"\nfoo'
        self.assertEqual([line for _, _, line in tokens(text)], [4, 5])


class Rules(unittest.TestCase):
    def test_the_words_are_those_of_the_core_text_code(self):
        self.assertEqual(core_words(tree({})), {"add", "ret", "nsw"})

    def test_generic_files_leave_out_the_core_dialect_and_the_command_line(self):
        root = tree(
            {
                "lean/Fir/Text/Print.lean": "",
                "lean/Fir/Text/Example.lean": "",
                "lean/Fir/Core/Ops.lean": "",
                "lean/FirRef.lean": "",
                "lean/FirRef/Parse.lean": "",
                "lean/FirRef/Run.lean": "",
                "lean/FirRef/Decode/Run.lean": "",
                "lean/FirTest/G0.lean": "",
            }
        )
        self.assertEqual(
            generic_files(root),
            [
                "lean/Fir/Text/Print.lean",
                "lean/FirRef.lean",
                "lean/FirRef/Decode/Run.lean",
                "lean/FirRef/Parse.lean",
            ],
        )

    def test_clean_generic_code_passes(self):
        text = 'def kind := "func"\ndef ret : Exit := .ret\n#guard isWord "icmp"\n'
        self.assertEqual(problems(tree({"lean/Fir/Text/Read.lean": text})), [])

    def test_naming_or_importing_the_core_dialect_fails(self):
        text = "import Fir.Core.Ops\n\ndef f : Dialect := CoreDialect\n"
        self.assertEqual(
            problems(tree({"lean/Fir/Execution/Run.lean": text})),
            [
                "lean/Fir/Execution/Run.lean:1: imports the core dialect: Fir.Core.Ops",
                "lean/Fir/Execution/Run.lean:3: names the core dialect: CoreDialect",
            ],
        )

    def test_writing_a_core_word_fails(self):
        text = 'def isRet (n : String) : Bool := n == "ret" || n == "i32"\n'
        self.assertEqual(
            problems(tree({"lean/FirRef/Parse.lean": text})),
            [
                'lean/FirRef/Parse.lean:1: writes the core dialect\'s word "ret"',
                'lean/FirRef/Parse.lean:1: writes the core dialect\'s word "i32"',
            ],
        )

    def test_corollary_files_may_name_the_core_dialect_but_not_write_its_words(self):
        text = 'import Fir.Core.TextLaws\ntheorem Core.x : "add" = "add" := rfl\n'
        found = problems(tree({"lean/Fir/Text/PrintParse.lean": text}))
        self.assertEqual(
            found,
            [
                'lean/Fir/Text/PrintParse.lean:2: writes the core dialect\'s word "add"',
                'lean/Fir/Text/PrintParse.lean:2: writes the core dialect\'s word "add"',
            ],
        )

    def test_no_words_fails(self):
        root = tree({})
        (root / CORE_TEXT).write_text("", encoding="utf-8")
        self.assertEqual(len(problems(root)), 1)


class Repository(unittest.TestCase):
    def test_the_repository_passes(self):
        self.assertEqual(problems(), [])

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
