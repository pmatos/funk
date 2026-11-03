"""Tests for scripts/check_unsafe_code.py. Run: python scripts/test_check_unsafe_code.py

Each test plants one kind of violation in a copy of the workspace's real
files and checks that the check fails on it, naming the word it found.
"""

import tempfile
import unittest
from pathlib import Path

from check_unsafe_code import ADR, TRUSTED_BASE, problems

REPO = Path(__file__).resolve().parent.parent
RECORD = "crates/funk-start-fds/src/record.rs"
FDS = "crates/funk-start-fds/Cargo.toml"
IR = "crates/funk-ir/src/lib.rs"
IR_TOML = "crates/funk-ir/Cargo.toml"
REAL = ["Cargo.toml", FDS, "crates/funk-start-fds/src/lib.rs", RECORD, IR_TOML]


def check(**files: str) -> list[str]:
    """problems() on a copy of the real files, with `files`, keyed by a
    repository path or a key of PATHS, replacing or adding to them."""
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        texts = {path: (REPO / path).read_text(encoding="utf-8") for path in REAL}
        texts[IR] = "pub fn f() {}\n"
        texts.update({PATHS.get(key, key): text for key, text in files.items()})
        for path, text in texts.items():
            (root / path).parent.mkdir(parents=True, exist_ok=True)
            (root / path).write_text(text, encoding="utf-8")
        rust = [p for p in texts if p.endswith(".rs")]
        manifests = [p for p in texts if p.endswith("Cargo.toml")]
        return problems(root, rust, manifests)


PATHS = {
    "ir": IR,
    "ir_toml": IR_TOML,
    "record": RECORD,
    "fds": FDS,
    "root": "Cargo.toml",
}


def record(old: str, new: str) -> str:
    text = (REPO / RECORD).read_text(encoding="utf-8")
    assert text.count(old) == 1, old
    return text.replace(old, new)


def in_verus(code: str) -> str:
    return record("} // verus!", code + "\n} // verus!")


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
        self.assertEqual(check(ir=ir), [])

    def test_verus_words_outside_a_verus_crate_do_not_count(self):
        ir = "pub fn assume(external: bool) -> bool { admit(external) }\n"
        ir += "fn admit(axiom: bool) -> bool { axiom }\n#[cfg(test)]\nmod t {}\n"
        self.assertEqual(check(ir=ir), [])

    def test_unsafe_inside_verus_in_a_verified_module_passes(self):
        self.assertEqual(check(record=in_verus("unsafe fn checked() {}")), [])


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

    def test_unsafe_code_lowered_in_a_manifest(self):
        lowered = (
            (REPO / IR_TOML)
            .read_text()
            .replace("[lints]\nworkspace = true", '[lints.rust]\nunsafe_code = "allow"')
        )
        found = check(ir_toml=lowered)
        self.assertTrue(any("unsafe_code is allow" in m for m in found), found)
        root = (REPO / "Cargo.toml").read_text().replace('"forbid"', '"deny"')
        found = check(root=root)
        self.assertTrue(
            any("Cargo.toml: unsafe_code is deny" in m for m in found), found
        )

    def test_unsafe_outside_verus_on_an_untrusted_item(self):
        self.assert_fails(
            "unsafe",
            record=record("} // verus!", "} // verus!\nfn evil() { unsafe {} }"),
        )

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
        planted = record(
            "        fd += 1;\n", "        fd += 1;\n        assume(false);\n"
        )
        self.assert_fails("assume", record=planted)

    def test_admit(self):
        self.assert_fails(
            "admit", record=in_verus("proof fn p() ensures false { admit(); }")
        )

    def test_external_body_on_an_untrusted_item(self):
        planted = record(
            "fn record_slots(", "#[verifier::external_body]\nfn record_slots("
        )
        self.assert_fails("external_body", record=planted)

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


class PlantedBlindSpots(unittest.TestCase):
    def test_code_that_verus_does_not_see(self):
        found = check(record=in_verus("#[cfg(not(verus_keep_ghost))]\nfn f() {}"))
        self.assertTrue(any("`verus_keep_ghost`" in m for m in found), found)
        self.assertTrue(any("`cfg`" in m for m in found), found)
        found = check(ir="#[cfg(verus_only)]\npub fn f() {}\n")
        self.assertTrue(any("`verus_only`" in m for m in found), found)

    def test_a_cfg_inside_a_verified_module(self):
        found = check(record=in_verus('#[cfg(target_os = "linux")]\nfn f() {}'))
        self.assertTrue(any("`cfg`" in m for m in found), found)

    def test_a_verified_module_whose_crate_does_not_opt_in(self):
        fds = (REPO / FDS).read_text().replace("verify = true", "verify = false")
        found = check(fds=fds)
        self.assertTrue(any("does not opt into Verus" in m for m in found), found)

    def test_a_trusted_item_that_is_gone(self):
        found = check(record=record("axiom fn take_slots()", "axiom fn take_all()"))
        self.assertTrue(
            any("trusted item take_slots has no `axiom`" in m for m in found), found
        )
        self.assertTrue(any("`axiom` in take_all" in m for m in found), found)


class TheAdr(unittest.TestCase):
    def test_lists_every_trusted_item(self):
        text = (REPO / ADR).read_text(encoding="utf-8")
        for path, trusted in TRUSTED_BASE.items():
            self.assertIn(f"`{path}`", text)
            for item in trusted:
                name = "#![allow(unsafe_code)]" if item == "<module>" else item
                self.assertIn(f"`{name}`", text, f"{ADR} does not list {name}")


if __name__ == "__main__":
    unittest.main()
