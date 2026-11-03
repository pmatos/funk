"""Tests for scripts/check_unsafe_code.py: what a verified module may hold,
the names that its proof rests on, and code that Verus would not see. Run:
python -m unittest discover -s scripts -p "test_*unsafe*.py"
"""

import unittest

from unsafe_planting import FDS, FDS_LIB, REPO, after_verus, check, in_verus, real
from unsafe_planting import record as planted_record


class Case(unittest.TestCase):
    def assert_fails(self, text: str, **files: str):
        found = check(**files)
        self.assertTrue(any(text in m for m in found), found)


class PlantedOutsideVerus(Case):
    """Outside verus!, a verified module holds only inner attributes, use,
    constants and trusted items; it defines and calls no macro but its
    verus! block, and renames no import."""

    def test_global_asm(self):
        code = 'std::arch::global_asm!(".pushsection .init_array");'
        self.assert_fails("`global_asm!`", record=after_verus(code))
        self.assert_fails("`global_asm!`", record=in_verus(code))

    def test_include(self):
        self.assert_fails("`include`", record=after_verus('include!("helper.in");'))
        code = 'fn f() -> u8 { include!("helper.in") }'
        self.assert_fails("`include`", record=in_verus(code))
        self.assert_fails("`include`", fds_lib=(REPO / FDS_LIB).read_text() + code)

    def test_a_macro_called_in_an_expression(self):
        """`option_env!` is set when cargo-verus builds, not cargo build."""
        line = "        let code = if result == -1 {\n"
        for name in ("option_env", "env", "cfg", "include_str", "concat"):
            call = f'{name}!("__VERUS_DRIVER_VIA_CARGO__")'
            planted = planted_record(line, f"        let _x = {call};\n{line}")
            self.assert_fails(f"`{name}!`", record=planted)
        self.assert_fails("`m!`", record=after_verus("const C: u8 = m!();"))

    def test_a_macro_defined_in_verus_that_expands_outside(self):
        code = "macro_rules! sneak { () => { unsafe { fcntl(2, 1) } } }"
        found = check(record=in_verus(code))
        self.assertTrue(any("`macro_rules`" in m for m in found), found)
        self.assertTrue(any("`unsafe` in sneak" in m for m in found), found)

    def test_a_renamed_import(self):
        code = "use std::option_env as requires;"
        self.assert_fails("`as` in std", record=in_verus(code))

    def test_a_path_attribute_in_a_verus_crate(self):
        lib = (REPO / FDS_LIB).read_text() + '#[path = "evil.txt"]\nmod evil;\n'
        self.assert_fails("`path`", fds_lib=lib)

    def test_a_verus_macro_that_shadows_vstds(self):
        code = "macro_rules! verus { ($($t:tt)*) => { $($t)* } }"
        self.assert_fails("`verus`", record=after_verus(code))
        self.assert_fails("`verus`", ir=code + "\n")
        self.assert_fails("`verus`", record=after_verus("use std::vec as verus;"))

    def test_an_item_that_is_not_trusted(self):
        self.assert_fails(
            "evil sits outside verus!", record=after_verus("fn evil() {}")
        )


class PlantedNames(Case):
    """take_slots and finish are named once, in record; getfd and store
    once, in record_slots; record once, in RECORD; and Slots only by the
    items that use the view of the slots."""

    def test_a_second_take_slots(self):
        second = (
            "let tracked mut other = take_slots();\n"
            "        store(0, 99, Tracked(&mut other));\n"
        )
        planted = planted_record(
            "        fd += 1;\n", "        fd += 1;\n        " + second
        )
        self.assert_fails("`take_slots` in record_slots", record=planted)
        planted = planted_record("    proof {\n", "    " + second + "    proof {\n")
        self.assert_fails("record names take_slots 2 times", record=planted)

    def test_record_without_finish(self):
        planted = planted_record("    proof {\n        finish(slots);\n    }\n", "")
        self.assert_fails("record names finish 0 times", record=planted)

    def test_a_second_getfd(self):
        code = "        let _first = getfd(fd as c_int);\n"
        planted = planted_record("        let (result,", code + "        let (result,")
        self.assert_fails("record_slots names getfd 2 times", record=planted)
        self.assert_fails("`getfd` in f", record=in_verus("fn f() { getfd(0); }"))

    def test_a_store_outside_record_slots(self):
        code = (
            "fn put(Tracked(slots): Tracked<&mut Slots>) "
            "{ store(0, 99, Tracked(slots)); }"
        )
        self.assert_fails("`store` in put", record=in_verus(code))

    def test_init_array_without_record(self):
        planted = planted_record("fn() = record;", "fn() = other;")
        self.assert_fails("RECORD names record 0 times", record=planted)

    def test_an_alias_of_slots(self):
        """A copy of the view would let a store follow `finish`."""
        code = "type View = Slots;\nimpl Clone for View { fn clone(&self) -> Self"
        code += " { loop {} } }"
        self.assert_fails("`Slots` in View", record=in_verus(code))
        code = "mod copy { use super::Slots; }"
        self.assert_fails("`Slots` in copy", record=in_verus(code))


class PlantedBlindSpots(Case):
    def test_code_that_verus_does_not_see(self):
        found = check(record=in_verus("#[cfg(not(verus_keep_ghost))]\nfn f() {}"))
        self.assertTrue(any("`verus_keep_ghost`" in m for m in found), found)
        self.assertTrue(any("`cfg`" in m for m in found), found)
        self.assert_fails("`verus_only`", ir="#[cfg(verus_only)]\npub fn f() {}\n")

    def test_any_verus_cfg(self):
        ir = "#[cfg(not(verus_keep_ghost_body))]\npub fn f() {}\n"
        self.assert_fails("`verus_keep_ghost_body`", ir=ir)

    def test_a_cfg_on_the_mod_that_mounts_a_verified_module(self):
        lib = real(FDS_LIB, "))]\nmod record;", ', not(feature = "x")))]\nmod record;')
        self.assert_fails("`not` on `mod record`", fds_lib=lib)
        lib = real(
            FDS_LIB, "mod record;", '#[cfg_attr(unix, path = "empty.rs")]\nmod record;'
        )
        self.assert_fails("`cfg_attr` on `mod record`", fds_lib=lib)

    def test_a_verified_module_that_is_not_mounted(self):
        lib = real(FDS_LIB, "mod record;", "mod other;")
        self.assert_fails("must mount the verified module", fds_lib=lib)

    def test_a_verus_cfg_declared_in_a_manifest(self):
        fds = real(
            FDS,
            "[lints.rust]\n",
            '[lints.rust]\nunexpected_cfgs = { level = "warn", check-cfg = '
            '["cfg(verus_keep_ghost_body)"] }\n',
        )
        self.assert_fails("a Verus cfg", fds=fds)

    def test_a_cfg_inside_a_verified_module(self):
        code = '#[cfg(target_os = "linux")]\nfn f() {}'
        self.assert_fails("`cfg`", record=in_verus(code))

    def test_a_verified_module_whose_crate_does_not_opt_in(self):
        fds = real(FDS, "verify = true", "verify = false")
        self.assert_fails("does not opt into Verus", fds=fds)

    def test_a_trusted_item_that_is_gone(self):
        planted = planted_record("axiom fn take_slots()", "axiom fn take_all()")
        found = check(record=planted)
        self.assertTrue(
            any("trusted item take_slots has no `axiom`" in m for m in found), found
        )
        self.assertTrue(any("`axiom` in take_all" in m for m in found), found)


if __name__ == "__main__":
    unittest.main()
