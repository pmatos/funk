"""Tests of how an input that crashed a fuzzer joins the corpus."""

import tempfile
import tomllib
import unittest
from pathlib import Path
from unittest import mock

import corpus
import fuzz_to_corpus
import tools

VALID = '{"verdict":"accepted","diagnostics":[]}'
REJECT = '{"verdict":"validation-error","diagnostics":[{"message":"no"}]}'


def ran(stdout, status=0):
    return tools.Ran(status, stdout, "")


class Text(unittest.TestCase):
    def test_every_byte_survives_the_toml(self):
        data = bytes(range(256)) + b'"quoted\\'
        table = fuzz_to_corpus.reject_table("parse-error", 'a "rule"', data)
        parsed = tomllib.loads(table)["reject"][0]
        self.assertEqual(parsed["rule"], 'a "rule"')
        self.assertIsNone(corpus.reject_problem(parsed))
        self.assertEqual(corpus.text_bytes(parsed["text"]), data)


class Keep(unittest.TestCase):
    def setUp(self):
        d = tempfile.TemporaryDirectory()
        self.addCleanup(d.cleanup)
        self.corpus = Path(d.name)
        (self.corpus / "canonical").mkdir()
        (self.corpus / "reject").mkdir()
        self.artifact = self.corpus / "crash"
        self.artifact.write_bytes(b"\xffbad")

    def keep(self, runs, rule="breaks it"):
        with mock.patch.object(tools, "run", side_effect=runs):
            return fuzz_to_corpus.keep("funk", self.artifact, self.corpus, rule)

    def test_a_rejected_text_joins_the_must_reject_file(self):
        status, _ = self.keep([ran(REJECT, 1)])
        self.assertEqual(status, 0)
        data = tomllib.loads((self.corpus / "reject/fuzz.toml").read_text())
        self.assertEqual(corpus.text_bytes(data["reject"][0]["text"]), b"\xffbad")

    def test_a_second_text_keeps_the_first(self):
        self.keep([ran(REJECT, 1)])
        self.keep([ran(REJECT, 1)])
        data = tomllib.loads((self.corpus / "reject/fuzz.toml").read_text())
        self.assertEqual(len(data["reject"]), 2)

    def test_a_valid_module_joins_the_canonical_texts(self):
        status, _ = self.keep([ran(VALID), ran("canonical text\n")])
        self.assertEqual(status, 0)
        written = list((self.corpus / "canonical").glob("fuzz-*.fir"))
        self.assertEqual([p.read_text() for p in written], ["canonical text\n"])

    def test_a_rejected_text_needs_its_rule(self):
        status, what = self.keep([ran(REJECT, 1)], rule=None)
        self.assertEqual(status, 2)
        self.assertIn("--rule", what)

    def test_a_crash_that_still_happens_is_not_kept(self):
        status, what = self.keep([tools.Ran(-6, "", "panicked")])
        self.assertEqual(status, 2)
        self.assertIn("still fails", what)
        self.assertFalse((self.corpus / "reject/fuzz.toml").exists())


if __name__ == "__main__":
    unittest.main()
