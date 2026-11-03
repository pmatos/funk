"""Tests for the pins of scripts/check_unsafe_code.py (scripts/
unsafe_pins.py): an edit to the trusted base, to #117's specification or to
`record` fails the check, even where Verus would still pass. Run:
python -m unittest discover -s scripts -p "test_*unsafe*.py"
"""

import unittest

from unsafe_pins import OUTSIDE
from unsafe_planting import check, in_verus, record

LOOP = """        let code = if result == -1 {
            error.unwrap_or(0)
        } else {
            0
        };"""


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

    def test_getfd(self):
        self.assert_pinned(
            "getfd",
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
            ("_private: core::cell::Cell<()>,", "_private: (),"),
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


class Unpinned(unittest.TestCase):
    def test_comments_layout_and_the_proved_body_are_free(self):
        planted = record(
            "    let result = unsafe { fcntl(fd, F_GETFD) };",
            "    // a comment\n    let   result =\n unsafe { fcntl( fd, F_GETFD ) } ;",
        )
        self.assertEqual(check(record=planted), [])
        code = (
            "        let code = match error { Some(c) if result == -1 => c, _ => 0 };"
        )
        self.assertEqual(check(record=record(LOOP, code)), [])
        lemma = "proof fn lemma(x: int) ensures x + 0 == x {}"
        self.assertEqual(check(record=in_verus(lemma)), [])


if __name__ == "__main__":
    unittest.main()
