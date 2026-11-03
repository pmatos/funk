"""Tests for the rules on the crate of a verified module
(scripts/unsafe_items.py): the rest of the crate cannot reach Verus, and
no file renames a crate. Run:
python -m unittest discover -s scripts -p "test_*unsafe*.py"
"""

import unittest

from unsafe_planting import FDS_LIB, REPO, check, in_verus, real


class Case(unittest.TestCase):
    def assert_fails(self, text: str, **files: str):
        found = check(**files)
        self.assertTrue(any(text in m for m in found), found)


class PlantedCrate(Case):
    """vstd and verus! only in the verified module; no extern crate."""

    def test_a_verus_block_in_lib(self):
        """A verified writer of `CLOSED` that `record_slots` could call."""
        code = "use vstd::prelude::*;\nverus! {\npub(crate) fn poke() no_unwind {}\n}\n"
        lib = (REPO / FDS_LIB).read_text() + code
        found = check(fds_lib=lib)
        for word in ("vstd", "verus"):
            self.assertTrue(
                any(
                    "lib.rs:" in m and f"`{word}` outside the verified" in m
                    for m in found
                ),
                found,
            )

    def test_vstd_by_path_in_lib(self):
        lib = (REPO / FDS_LIB).read_text() + "pub fn f() { vstd::prelude::verus!{} }\n"
        self.assert_fails("`vstd` outside the verified module", fds_lib=lib)

    def test_an_extern_crate(self):
        """`extern crate self as std;` retargets every `std::` path of
        record.rs, and so what the pinned `store` writes."""
        lib = real(FDS_LIB, "use std::io;", "extern crate self as std;\nuse std::io;")
        self.assert_fails(
            "`extern crate` in a crate with a verified module", fds_lib=lib
        )
        self.assert_fails(
            "`extern crate` in a crate with a verified module",
            record=in_verus("extern crate core as int;"),
        )


if __name__ == "__main__":
    unittest.main()
