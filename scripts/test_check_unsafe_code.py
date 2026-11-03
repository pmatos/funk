"""Tests for scripts/check_unsafe_code.py: unsafe code, assumptions and the
ADR. The other test_*unsafe*.py files test its other rules. Run them all:
python -m unittest discover -s scripts -p "test_*unsafe*.py"

Each test plants one kind of violation in a copy of the workspace's real
files and checks that the check fails on it, naming the word it found.
"""

import unittest

from check_unsafe_code import ADR, TRUSTED_BASE
from unsafe_pins import PINS
from unsafe_planting import (
    DOCTESTS,
    FDS,
    IR_TOML,
    REPO,
    check,
    in_record_slots,
    in_verus,
    real,
    record,
    with_record_slots_body,
)


class Clean(unittest.TestCase):
    def test_the_workspace_passes(self):
        self.assertEqual(check(), [])

    def test_words_in_comments_strings_and_lifetimes_do_not_count(self):
        ir = (
            "// unsafe { assume(false) }\n/* unsafe /* nested */ unsafe */\n"
            '/// allow(unsafe_code)\npub const A: &str = "unsafe";\n'
            'pub const B: &str = r#"unsafe " external_body"#;\n'
            "pub const C: char = '\\'';\npub fn f<'unsafe_a>(x: &'unsafe_a u8)"
            " -> &'unsafe_a u8 { x }\npub fn r#unsafe() {}\n"
        )
        self.assertEqual(check(ir=DOCTESTS + ir), [])

    def test_verus_words_outside_a_verus_crate_do_not_count(self):
        ir = "pub fn assume(external: bool) -> bool { admit(external) }\n"
        ir += "fn admit(axiom: bool) -> bool { axiom }\n#[cfg(test)]\nmod t {}\n"
        ir += '#[path = "t.rs"]\nmod u;\n'
        self.assertEqual(check(ir=DOCTESTS + ir), [])

    def test_a_path_that_is_not_an_attribute_does_not_count(self):
        code = "    let path = 0u8;\n    let _ = path;\n"
        self.assertEqual(check(record=in_record_slots(code)), [])

    def test_forbid_and_deny_of_unsafe_code_do_not_count(self):
        ir = "#![forbid(unsafe_code)]\n#[deny(dead_code, unsafe_code)]\nmod m {}\n"
        self.assertEqual(check(ir=DOCTESTS + ir), [])
        ir = "#![deny(clippy::all, unsafe_code)]\n#[forbid(a::b::c, unsafe_code)]\n"
        self.assertEqual(check(ir=DOCTESTS + ir + "mod m {}\n"), [])


class PlantedUnsafe(unittest.TestCase):
    def assert_fails(self, word: str, **files: str):
        found = check(**files)
        self.assertTrue(found, f"no problem for {word}")
        self.assertTrue(any(f"`{word}`" in m for m in found), found)

    def test_unsafe_block(self):
        self.assert_fails("unsafe", ir="pub fn f() -> u8 { unsafe { g() } }\n")

    def test_unsafe_function(self):
        self.assert_fails("unsafe", ir="pub unsafe fn f() {}\n")

    def test_unsafe_trait(self):
        self.assert_fails("unsafe", ir="pub unsafe trait T {}\n")

    def test_unsafe_impl(self):
        self.assert_fails("unsafe", ir="pub struct S;\nunsafe impl Send for S {}\n")

    def test_unsafe_extern_block(self):
        self.assert_fails(
            "unsafe", ir='unsafe extern "C" {\n    fn abs(x: i32) -> i32;\n}\n'
        )

    def test_unsafe_attribute(self):
        self.assert_fails(
            "unsafe", ir='#[unsafe(no_mangle)]\npub extern "C" fn f() {}\n'
        )

    def test_allow_unsafe_code(self):
        self.assert_fails("unsafe_code", ir="#![allow(unsafe_code)]\npub fn f() {}\n")
        self.assert_fails("unsafe_code", ir="#[allow(unsafe_code)]\nmod m {}\n")
        self.assert_fails("unsafe_code", ir="#[warn(dead_code, unsafe_code)]\nmod m {}")
        ir = "#[allow(clippy::all, unsafe_code)]\nmod m {}\n"
        self.assert_fails("unsafe_code", ir=ir)
        self.assert_fails("unsafe_code", ir="#[allow(::all, unsafe_code)]\nmod m {}\n")
        ir = "#[cfg_attr(unix, expect(unsafe_code))]\nmod m {}\n"
        self.assert_fails("unsafe_code", ir=ir)

    def test_a_crate_that_does_not_forbid_unsafe_code(self):
        evil = "crates/evil/Cargo.toml"
        head = '[package]\nname = "evil"\nversion = "0.1.0"\n'
        for toml in (head, head + '[lints.clippy]\ntodo = "deny"\n'):
            found = check(**{evil: toml, "crates/evil/src/lib.rs": "pub fn f() {}\n"})
            self.assertTrue(
                any(f"{evil}: unsafe_code is allow" in m for m in found), found
            )
        fds = real(FDS, 'unsafe_code = "deny"', 'unsafe_code = "allow"')
        found = check(fds=fds)
        self.assertTrue(
            any(f"{FDS}: unsafe_code is allow, not deny" in m for m in found), found
        )

    def test_unsafe_code_lowered_in_a_manifest(self):
        lowered = real(
            IR_TOML, "[lints]\nworkspace = true", '[lints.rust]\nunsafe_code = "allow"'
        )
        found = check(ir_toml=lowered)
        self.assertTrue(any("unsafe_code is allow" in m for m in found), found)
        root = (REPO / "Cargo.toml").read_text().replace('"forbid"', '"deny"')
        found = check(root=root)
        self.assertTrue(
            any("Cargo.toml: unsafe_code is deny" in m for m in found), found
        )

    def test_unsafe_outside_verus_on_an_untrusted_item(self):
        planted = record("} // verus!", "} // verus!\nfn evil() { unsafe {} }")
        self.assert_fails("unsafe", record=planted)

    def test_unsafe_inside_verus_on_an_untrusted_item(self):
        self.assert_fails("unsafe", record=in_verus("unsafe fn checked() {}"))
        code = "pub unsafe trait Trusted {}\nunsafe impl Trusted for u8 {}"
        self.assert_fails("unsafe", record=in_verus(code))

    def test_a_second_function_in_the_trusted_extern_block(self):
        planted = record(
            "-> c_int;\n}", "-> c_int;\n    fn evil(fd: c_int) -> c_int;\n}"
        )
        found = check(record=planted)
        self.assertTrue(any("in fcntl+evil" in m for m in found), found)

    def test_unsafe_in_a_verus_block_of_an_unverified_crate(self):
        toml = (REPO / IR_TOML).read_text() + '\n[dependencies]\nvstd = "=0"\n'
        ir = "verus! {\nunsafe fn f() {}\n}\n"
        self.assert_fails("unsafe", ir=ir, ir_toml=toml)


class PlantedAssumptions(unittest.TestCase):
    def assert_fails(self, word: str, **files: str):
        found = check(**files)
        self.assertTrue(any(f"`{word}`" in m for m in found), found)

    def test_assume(self):
        self.assert_fails("assume", record=in_record_slots("    assume(false);\n"))

    def test_admit(self):
        self.assert_fails(
            "admit", record=in_verus("proof fn p() ensures false { admit(); }")
        )

    def test_external_body_on_an_untrusted_item(self):
        planted = record(
            "fn record_slots(", "#[verifier::external_body]\nfn record_slots("
        )
        self.assert_fails("external_body", record=planted)

    def test_external_body_as_a_raw_identifier(self):
        planted = record(
            "fn record_slots(", "#[verifier::r#external_body]\nfn record_slots("
        )
        found = check(record=planted)
        self.assertTrue(any("`external_body` in record_slots" in m for m in found))

    def test_external_body_in_the_older_syntax(self):
        self.assert_fails(
            "external_body", record=in_verus("#[verifier(external_body)]\nfn f() {}")
        )

    def test_assume_specification(self):
        code = "pub assume_specification [ std::process::abort ] () -> !;"
        self.assert_fails("assume_specification", record=in_verus(code))

    def test_external(self):
        self.assert_fails(
            "external", record=in_verus("#[verifier::external]\nfn f() {}")
        )

    def test_assume_new(self):
        code = "fn f() { let tracked s: Slots = Tracked::assume_new().get(); }"
        self.assert_fails("assume_new", record=in_verus(code))

    def test_axiom(self):
        self.assert_fails("axiom", record=in_verus("axiom fn lie() ensures false;"))

    def test_assumptions_in_a_verus_crate_that_is_not_verified(self):
        toml = (REPO / IR_TOML).read_text() + '\n[dependencies]\nvstd = "=0"\n'
        self.assert_fails(
            "assume", ir="verus! {\nfn f() { assume(false); }\n}\n", ir_toml=toml
        )

    def test_a_verifier_attribute_other_than_external_body(self):
        """`exec_allows_no_decreases_clause` lets `loop {}` prove anything."""
        attribute = "exec_allows_no_decreases_clause"
        for written in (f"verifier::{attribute}", f"verifier({attribute})"):
            code = f"#[{written}]\nfn f() ensures false {{ loop {{}} }}"
            self.assert_fails(f"verifier::{attribute}", record=in_verus(code))
        planted = with_record_slots_body("    loop {}\n")
        planted = planted.replace(
            "fn record_slots(", f"#[verifier::{attribute}]\nfn record_slots("
        )
        self.assert_fails(f"verifier::{attribute}", record=planted)
        code = "#[verus::internal(spec)]\nfn f() {}"
        self.assert_fails("verus::internal", record=in_verus(code))


class TheAdr(unittest.TestCase):
    def test_every_trusted_item_is_pinned(self):
        """A pin covers every item of a name, so no second item may take a
        trusted item's name, and its marks, past the check."""
        for path, trusted in TRUSTED_BASE.items():
            self.assertLessEqual(set(trusted), set(PINS[path]))

    def test_lists_every_trusted_item_and_every_pin(self):
        text = (REPO / ADR).read_text(encoding="utf-8")
        for path, trusted in TRUSTED_BASE.items():
            self.assertIn(f"`{path}`", text)
            for item in trusted:
                name = "#![allow(unsafe_code)]" if item == "<module>" else item
                self.assertIn(f"`{name}`", text, f"{ADR} does not list {name}")
        for path, pins in PINS.items():
            for item, digest in pins.items():
                found = f"`{digest}`" in text
                self.assertTrue(found, f"{ADR} lacks {item}'s digest, {digest}")


if __name__ == "__main__":
    unittest.main()
