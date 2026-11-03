"""Tests for the crate-root rule of scripts/check_unsafe_code.py
(scripts/unsafe_manifests.py). The tests of the lint levels in the
manifests are in test_check_unsafe_code.py. Run:
python -m unittest discover -s scripts -p "test_*unsafe*.py"
"""

import unittest

from unsafe_planting import DOCTESTS, FDS_LIB, IR, check, real


class Case(unittest.TestCase):
    def assert_fails(self, text: str, **files: str):
        found = check(**files)
        self.assertTrue(any(text in m for m in found), found)


class PlantedDoctests(Case):
    def test_a_library_whose_doctests_may_use_unsafe_code(self):
        ir = "//! ```\n//! unsafe { std::hint::unreachable_unchecked() }\n//! ```\n"
        self.assert_fails(f"{IR}: a library's root holds", ir=ir)
        lib = real(FDS_LIB, DOCTESTS, "")
        self.assert_fails(f"{FDS_LIB}: a library's root holds", fds_lib=lib)
        ir = "#![cfg_attr(test, doc(test(attr(forbid(unsafe_code)))))]\n"
        self.assert_fails(f"{IR}: a library's root holds", ir=ir)


if __name__ == "__main__":
    unittest.main()
