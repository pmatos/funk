"""Tests for the manifest and crate-root rules of
scripts/check_unsafe_code.py (scripts/unsafe_manifests.py). Run:
python -m unittest discover -s scripts -p "test_*unsafe*.py"
"""

import re
import unittest

from unsafe_planting import DOCTESTS, FDS, FDS_LIB, IR, IR_TOML, REPO, check, real


class Case(unittest.TestCase):
    def assert_fails(self, text: str, **files: str):
        found = check(**files)
        self.assertTrue(any(text in m for m in found), found)


class PlantedTargets(Case):
    """A target's file and a build script are tracked .rs files, which the
    check reads; a crate with a verified module keeps the default layout."""

    def test_a_library_in_a_file_the_check_does_not_read(self):
        lib = real(
            FDS, "[dependencies]", '[lib]\npath = "src/lib.txt"\n\n[dependencies]'
        )
        self.assert_fails("[lib] path in a crate with a verified module", fds=lib)
        toml = (REPO / IR_TOML).read_text() + '\n[lib]\npath = "src/lib.txt"\n'
        self.assert_fails("[lib] path = 'src/lib.txt' is not a tracked", ir_toml=toml)
        toml = (REPO / IR_TOML).read_text() + '\n[[bin]]\nname = "x"\npath = "x.md"\n'
        self.assert_fails("[bin] path = 'x.md'", ir_toml=toml)

    def test_a_target_in_a_tracked_rust_file_passes(self):
        toml = (REPO / IR_TOML).read_text() + '\n[[example]]\nname = "x"\n'
        toml += 'path = "examples/../src/x.rs"\n'
        self.assertEqual(check(ir_toml=toml, **{"crates/funk-ir/src/x.rs": ""}), [])

    def test_a_build_script(self):
        toml = real(IR_TOML, "publish.workspace = true", 'build = "b.txt"')
        self.assert_fails("build = 'b.txt' is not a tracked", ir_toml=toml)
        fds = real(FDS, "publish.workspace = true", 'build = "build.rs"')
        self.assert_fails("build in a crate with a verified module", fds=fds)
        planted = {"crates/funk-start-fds/build.rs": "fn main() {}\n"}
        self.assert_fails("a crate with a verified module has no build.rs", **planted)


class PlantedDependencies(Case):
    """A crate with a verified module depends on vstd alone, from crates.io:
    a proc macro could put unsafe code in it, past its `deny`."""

    def test_a_second_dependency(self):
        fds = real(
            FDS, "[dependencies]\n", '[dependencies]\nsneak = { path = "../s" }\n'
        )
        self.assert_fails("[dependencies] sneak: a crate with a verified", fds=fds)
        fds = (REPO / FDS).read_text() + '\n[dev-dependencies]\nsneak = "1"\n'
        self.assert_fails("[dev-dependencies] sneak", fds=fds)
        fds = (REPO / FDS).read_text() + "\n[target.'cfg(unix)'.build-dependencies]\n"
        self.assert_fails("build-dependencies] cc", fds=fds + 'cc = "1"\n')

    def test_vstd_from_elsewhere(self):
        fds = (REPO / FDS).read_text()
        fds = re.sub(
            r"^vstd = .*$", 'vstd = { path = "../vstd" }', fds, flags=re.MULTILINE
        )
        self.assert_fails("vstd is not a version from crates.io", fds=fds)
        root = (REPO / "Cargo.toml").read_text()
        patch = '\n[patch.crates-io]\nverus_builtin_macros = { path = "m" }\n'
        self.assert_fails("patches or replaces verus_builtin_macros", root=root + patch)
        replace = '\n[replace]\n"vstd:0.0.0" = { path = "v" }\n'
        self.assert_fails("patches or replaces vstd", root=root + replace)


class PlantedEditionAndDoctests(Case):
    def test_an_older_edition(self):
        """In the 2021 edition an extern block need not say `unsafe`."""
        toml = real(IR_TOML, "edition.workspace = true", 'edition = "2021"')
        ir = (
            DOCTESTS
            + '#[link(name = "m")]\nextern "C" { pub fn cos(x: f64) -> f64; }\n'
        )
        self.assert_fails(f"{IR_TOML}: the edition is not", ir_toml=toml, ir=ir)
        root = (REPO / "Cargo.toml").read_text().replace('"2024"', '"2021"')
        self.assert_fails("the workspace's edition is 2021", root=root)

    def test_a_library_whose_doctests_may_use_unsafe_code(self):
        ir = "//! ```\n//! unsafe { std::hint::unreachable_unchecked() }\n//! ```\n"
        self.assert_fails(f"{IR}: a library's root holds", ir=ir)
        lib = real(FDS_LIB, DOCTESTS, "")
        self.assert_fails(f"{FDS_LIB}: a library's root holds", fds_lib=lib)
        ir = "#![cfg_attr(test, doc(test(attr(forbid(unsafe_code)))))]\n"
        self.assert_fails(f"{IR}: a library's root holds", ir=ir)


if __name__ == "__main__":
    unittest.main()
