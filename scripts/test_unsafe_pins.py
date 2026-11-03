"""Tests for the pins of scripts/check_unsafe_code.py (scripts/
unsafe_pins.py): an edit to the trusted base, to #117's specification, to
`record` or to the file that mounts the verified module fails the check,
even where Verus would still pass. Run:
python -m unittest discover -s scripts -p "test_*unsafe*.py"
"""

import unittest

from unsafe_pins import OUTSIDE, WHOLE
from unsafe_planting import (
    FDS_LIB,
    check,
    in_verus,
    real,
    record,
    with_record_slots_body,
)

# A body for `record_slots` that Verus proves too, in other words.
BODY = """    let mut fd: usize = 0;
    while fd < 3
        invariant
            fd <= 3,
            forall|i: int| 0 <= i < fd ==> #[trigger] slots.holds(i) == recorded(i),
        decreases 3 - fd,
    {
        let (result, error) = getfd(fd as c_int);
        let code = match error { Some(c) if result == -1 => c, _ => 0 };
        store(fd, code, Tracked(slots));
        fd += 1;
    }
"""


class Case(unittest.TestCase):
    def assert_pinned(self, item: str, *edits: tuple[str, str]):
        for old, new in edits:
            found = check(record=record(old, new))
            self.assertTrue(
                any(f"record.rs: {item} is not the text" in m for m in found),
                (old, new, found),
            )


class PlantedTrustedBase(Case):
    """Each trusted item's specification, body and attributes."""

    def test_the_text_outside_verus(self):
        self.assert_pinned(
            OUTSIDE,
            ("    fn fcntl(", '    #[link_name = "dup2"]\n    fn fcntl('),
            ('".init_array"', '".fini_array"'),
            ("fn() = record;", "fn() = super::record;"),
            ("const F_GETFD: c_int = 1;", "const F_GETFD: c_int = 2;"),
            ("#![allow(unsafe_code)]", "#![allow(unsafe_code, dead_code)]"),
            ("use std::ffi::c_int;", "use std::os::raw::c_int;"),
            ("} // verus!", "} // verus!\nconst WRAP: u8 = { 1 };"),
        )

    def test_trusted_names_inside_verus(self):
        """A second item of a trusted item's name, which could carry its
        marks: `unsafe trait RECORD`, `unsafe impl RECORD for fcntl`."""
        self.assert_pinned("RECORD", ("} // verus!", "pub unsafe trait RECORD {}\n}"))
        self.assert_pinned("fcntl", ("} // verus!", "pub struct fcntl {}\n}"))
        self.assert_pinned(
            "<module>", ("} // verus!", "mod m {}\n#![allow(unsafe_code)]\n}")
        )

    def test_getfd(self):
        self.assert_pinned(
            "getfd",
            ("        0 <= fd < 3,\n", "        0 <= fd,\n"),
            (
                "        result.0 == getfd_result(fd as int),\n",
                "        result.0 == getfd_result(fd as int),\n        result.0 != -1,\n",
            ),
            (
                "    let result = unsafe { fcntl(fd, F_GETFD) };\n",
                (
                    "    let result = unsafe { fcntl(fd, F_GETFD) };\n"
                    "    unsafe { fcntl(fd, 2, 1) };\n"
                ),
            ),
            ("        result.0 == -1 ==> result.1", "        result.1"),
        )

    def test_store(self):
        self.assert_pinned(
            "store",
            (
                "        fd < 3,\n    ensures\n",
                "        fd < 3,\n    ensures\n false,\n",
            ),
            ("closed[fd].store(code,", "closed[0].store(99,"),
            ("let closed: &[AtomicI32; 3] =", "let closed: &[AtomicI32] ="),
        )

    def test_slots(self):
        self.assert_pinned(
            "Slots",
            (
                "pub tracked struct Slots {",
                "#[derive(Clone, Copy)]\npub tracked struct Slots {",
            ),
            ("_private: ::core::cell::Cell<()>,", "_private: (),"),
            ("_private: ::core::cell::Cell<()>,", "_private: core::cell::Cell<()>,"),
            (
                "impl Slots {",
                (
                    "impl Clone for Slots { fn clone(&self) -> Self { *self } }\n"
                    "impl Copy for Slots {}\nimpl Slots {"
                ),
            ),
        )

    def test_take_slots(self):
        self.assert_pinned(
            "take_slots",
            (
                "axiom fn take_slots() -> (tracked slots: Slots);",
                (
                    "axiom fn take_slots() -> (tracked slots: Slots)\n"
                    "    ensures forall|fd: int| slots.holds(fd) == recorded(fd);"
                ),
            ),
        )


class PlantedSpecification(Case):
    """#117's specification and the names that the trusted items rest on."""

    def test_an_uninterpreted_function_given_a_body(self):
        self.assert_pinned(
            "getfd_error",
            (
                "pub uninterp spec fn getfd_error(fd: int) -> Option<i32>;",
                "pub open spec fn getfd_error(fd: int) -> Option<i32> { None }",
            ),
        )
        self.assert_pinned(
            "getfd_result",
            (
                "pub uninterp spec fn getfd_result(fd: int) -> c_int;",
                "pub open spec fn getfd_result(fd: int) -> c_int { 0 }",
            ),
        )
        self.assert_pinned(
            "Slots",
            (
                "pub uninterp spec fn holds(&self, fd: int) -> i32;",
                "pub open spec fn holds(&self, fd: int) -> i32 { recorded(fd) }",
            ),
        )

    def test_recorded(self):
        self.assert_pinned(
            "recorded", ("            None => 0,", "            None => 1,")
        )

    def test_finish(self):
        self.assert_pinned(
            "finish",
            (
                "        forall|fd: int| 0 <= fd < 3 ==> #[trigger] slots",
                "        true || slots",
            ),
        )

    def test_record_slots_signature(self):
        self.assert_pinned(
            "record_slots",
            (
                "        forall|fd: int| 0 <= fd < 3 ==> #[trigger] final",
                "        forall|fd: int| 0 <= fd < 2 ==> #[trigger] final",
            ),
            (
                "fn record_slots(",
                "#[verifier::exec_allows_no_decreases_clause]\nfn record_slots(",
            ),
        )


class PlantedRecord(Case):
    def test_a_loop_that_takes_a_second_view(self):
        body = """    let tracked mut slots = take_slots();
    record_slots(Tracked(&mut slots));
    proof {
        finish(slots);
    }"""
        loop = """    let mut i: usize = 0;
    while i < 2 invariant i <= 2, decreases 2 - i {
        let tracked mut slots = take_slots();
        if i == 0 {
            record_slots(Tracked(&mut slots));
            proof { finish(slots); }
        }
        i += 1;
    }"""
        self.assert_pinned("record", (body, loop))


class PlantedLib(unittest.TestCase):
    """lib.rs is pinned whole: it defines the `CLOSED` that `store` writes,
    and mounts the verified module."""

    def assert_pinned(self, old: str, new: str):
        found = check(fds_lib=real(FDS_LIB, old, new))
        self.assertTrue(
            any(f"lib.rs: {WHOLE} is not the text" in m for m in found), found
        )

    def test_closed(self):
        self.assert_pinned(
            "static CLOSED: [AtomicI32; 3]",
            "static CLOSED: &[AtomicI32; 3] = &DECOY;\nstatic DECOY: [AtomicI32; 3]",
        )
        self.assert_pinned(
            "    Stdin = 0,\n    Stdout = 1,", "    Stdin = 1,\n    Stdout = 0,"
        )
        self.assert_pinned("        0 => None,", "        9 => None,")

    def test_the_mount(self):
        self.assert_pinned('    target_os = "linux",\n', "")
        self.assert_pinned("#[cfg(any(\n", "#[cfg(any(all(), \n")

    def test_a_crate_renamed_in_the_root(self):
        """`extern crate self as std;` would retarget record.rs's `std::`."""
        self.assert_pinned("use std::io;", "extern crate self as std;\nuse std::io;")


class Unpinned(unittest.TestCase):
    def test_comments_layout_and_the_proved_body_are_free(self):
        planted = record(
            "    let result = unsafe { fcntl(fd, F_GETFD) };",
            "    // a comment\n    let   result =\n unsafe { fcntl( fd, F_GETFD ) } ;",
        )
        self.assertEqual(check(record=planted), [])
        self.assertEqual(check(record=with_record_slots_body(BODY)), [])
        lemma = "proof fn lemma(x: int) ensures x + 0 == x {}"
        self.assertEqual(check(record=in_verus(lemma)), [])
        spec = "pub open spec fn twice(x: int) -> int { 2 * x }"
        self.assertEqual(check(record=in_verus(spec)), [])


if __name__ == "__main__":
    unittest.main()
