"""Tests that scripts/check_unsafe_code.py accepts legitimate work that only
a deliberately disguised change could abuse. The check catches careless or
well-meaning changes; review of the diff is the defence against a
deliberate one (ADR-2026-11-03-0808). Run:
python -m unittest discover -s scripts -p "test_*unsafe*.py"
"""

import unittest

from unsafe_planting import DOCTESTS, FDS, REPO, check, with_record_slots_body

# A new library crate that inherits the workspace's lints.
PACKAGE = """[package]
name = "{name}"
version.workspace = true
edition.workspace = true
license.workspace = true
publish.workspace = true
{extra}
[lints]
workspace = true
"""

# `record_slots`' loop, with the code to store worked out by a helper.
BODY = """    let mut fd: usize = 0;
    while fd < 3
        invariant
            fd <= 3,
            forall|i: int| 0 <= i < fd ==> #[trigger] slots.holds(i) == recorded(i),
        decreases 3 - fd,
    {
        let (result, error) = getfd(fd as c_int);
        store(fd, code_of(result, error), Tracked(slots));
        fd += 1;
    }
"""
HELPER = """/// The code that `record_slots` stores for one answer of `getfd`.
fn code_of(result: c_int, error: Option<i32>) -> (code: i32)
    ensures
        code == (if result == -1 {
            match error {
                Some(c) => c,
                None => 0,
            }
        } else {
            0
        }),
    no_unwind
{
    if result == -1 {
        error.unwrap_or(0)
    } else {
        0
    }
}
"""


def crate(name: str, extra: str = "", lib: str = "pub fn f() {}\n") -> dict:
    """The files of a new crate under crates/, keyed by their paths."""
    return {
        f"crates/{name}/Cargo.toml": PACKAGE.format(name=name, extra=extra),
        f"crates/{name}/src/lib.rs": DOCTESTS + lib,
    }


class AcceptedWork(unittest.TestCase):
    def test_a_crate_with_a_build_script(self):
        files = crate("funk-gen")
        files["crates/funk-gen/build.rs"] = (
            'fn main() {\n    println!("cargo::rerun-if-changed=build.rs");\n}\n'
        )
        self.assertEqual(check(**files), [])

    def test_a_proc_macro_crate(self):
        lib = (
            "use proc_macro::TokenStream;\n\n#[proc_macro_derive(Op)]\n"
            "pub fn derive_op(input: TokenStream) -> TokenStream {\n"
            "    let _ = input;\n    TokenStream::new()\n}\n"
        )
        files = crate("funk-derive", "\n[lib]\nproc-macro = true\n", lib)
        self.assertEqual(check(**files), [])

    def test_a_crate_on_the_2021_edition_that_forbids_unsafe_code(self):
        files = crate("funk-old")
        toml = "crates/funk-old/Cargo.toml"
        files[toml] = files[toml].replace(
            "edition.workspace = true", 'edition = "2021"'
        )
        self.assertEqual(check(**files), [])
        files[toml] = files[toml].replace("[lints]\nworkspace = true\n", "")
        found = check(**files)
        self.assertTrue(any(f"{toml}: unsafe_code is allow" in m for m in found))

    def test_a_dev_dependency_of_funk_start_fds(self):
        fds = (REPO / FDS).read_text() + '\n[dev-dependencies]\ntempfile = "3"\n'
        self.assertEqual(check(fds=fds), [])

    def test_an_exec_helper_inside_verus_called_from_record_slots(self):
        """Verus proves the helper too; only `record_slots` names `getfd`
        and `store`."""
        text = with_record_slots_body(BODY)
        assert text.count("} // verus!") == 1
        text = text.replace("} // verus!", HELPER + "\n} // verus!")
        self.assertEqual(check(record=text), [])


if __name__ == "__main__":
    unittest.main()
