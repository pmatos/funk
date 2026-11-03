"""Tests for what may be added to a verified module and its crate
(scripts/unsafe_items.py): a new item cannot take a name that a pinned
text uses, and the rest of the crate cannot reach Verus. Run:
python -m unittest discover -s scripts -p "test_*unsafe*.py"
"""

import unittest

from unsafe_planting import FDS_LIB, REPO, check, in_verus, real

NOT_GHOST = "a verified module adds only proof or spec functions"
TAKEN = "a pinned text holds the name"


class Case(unittest.TestCase):
    def assert_fails(self, text: str, **files: str):
        found = check(**files)
        self.assertTrue(any(text in m for m in found), found)


class PlantedNewItems(Case):
    """Inside verus!, only pinned items and proof or spec functions whose
    names no pinned text holds."""

    def test_a_type_that_shadows_vstds_int(self):
        """`type int = u8;` makes `getfd_result(fd as int)` mean
        `getfd_result(fd as u8)`, and every digest stays the same."""
        code = "#[allow(non_camel_case_types, dead_code)]\npub type int = u8;"
        self.assert_fails(f": int: inside verus! {NOT_GHOST}", record=in_verus(code))

    def test_items_that_shadow_names_of_the_pinned_texts(self):
        for code, name in (
            ("type int = nat;", "int"),
            ("const None: Option<i32> = Some(9);", "None"),
            ("type Option<T> = core::option::Option<T>;", "Option"),
            ("pub struct Tracked<T>(T);", "Tracked"),
            ("use std::primitive::u8;", "std"),
            ("static CLOSED: u8 = 0;", "CLOSED"),
        ):
            self.assert_fails(
                f": {name}: inside verus! {NOT_GHOST}", record=in_verus(code)
            )

    def test_a_module_that_shadows_core(self):
        """A local `core` with a `Copy` `Cell` would make `Slots` `Copy`
        without changing its text, if its field did not say `::core`."""
        code = (
            "pub mod core { pub mod cell {\n"
            "#[derive(Clone, Copy)] pub struct Cell<T>(pub T);\n} }"
        )
        found = check(record=in_verus(code))
        for path in ("core", "core::cell", "core::cell::Cell"):
            self.assertTrue(any(f": {path}: inside verus!" in m for m in found), found)

    def test_an_exec_function(self):
        self.assert_fails(
            f"helper: inside verus! {NOT_GHOST}", record=in_verus("fn helper() {}")
        )
        code = "pub const fn helper() -> u8 { 0 }"
        self.assert_fails(f"helper: inside verus! {NOT_GHOST}", record=in_verus(code))

    def test_a_ghost_function_with_a_taken_name(self):
        for code, name in (
            ("pub open spec fn int(x: u8) -> u8 { x }", "int"),
            ("proof fn old() {}", "old"),
            ("pub closed spec fn c_int() -> bool { true }", "c_int"),
        ):
            self.assert_fails(f"{TAKEN} `{name}`", record=in_verus(code))

    def test_a_broadcast_group(self):
        code = "broadcast group lemmas { lemma }"
        self.assert_fails(
            f"<unnamed>: inside verus! {NOT_GHOST}", record=in_verus(code)
        )


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
