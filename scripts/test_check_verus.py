"""Tests for scripts/check-verus.sh, against fake cargo, rustc, verus and
cargo-verus that log how the script calls them. Run:
python -m unittest discover -s scripts -p "test_*verus*.py"
"""

import json
import os
import re
import subprocess
import tempfile
import unittest
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
SCRIPT = REPO / "scripts" / "check-verus.sh"
RUST = re.search(
    r'^channel = "(.*)"$', (REPO / "rust-toolchain.toml").read_text(), re.MULTILINE
)[1]
VERUS = re.search(r"^pinned=(\S+)$", SCRIPT.read_text(), re.MULTILINE)[1]

METADATA = {
    "packages": [{"name": "funk-start-fds", "metadata": {"verus": {"verify": True}}}]
}
NOTES = {"obligation_proof_notes": [], "failed_proof_notes": []}
REPORT = {
    "verification-results": {"success": True, "verified": 3, "errors": 0},
    "func-details": {
        f"funk_start_fds::record::{name}": NOTES for name in ("record", "record_slots")
    },
}


def tool(path: Path, body: str) -> None:
    path.write_text("#!/usr/bin/env bash\n" + body, encoding="utf-8")
    path.chmod(0o755)


class CheckVerus(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(self.enterContext(tempfile.TemporaryDirectory()))
        self.bin, self.release = self.tmp / "bin", self.tmp / "release"
        self.bin.mkdir()
        self.release.mkdir()
        tool(
            self.bin / "cargo",
            f'if [[ $1 == --version ]]; then echo "cargo {RUST} (fake)"; exit; fi\n'
            'echo "$*" >>"$LOG/cargo"\n'
            f"if [[ $1 == metadata ]]; then echo '{json.dumps(METADATA)}'; fi\n",
        )
        tool(self.bin / "rustc", f'echo "rustc {RUST} (fake)"\n')
        tool(
            self.release / "verus",
            f'printf "Verus\\n  Version: {VERUS}\\n'
            f'  Toolchain: {RUST}-x86_64-unknown-linux-gnu\\n"\n',
        )
        tool(
            self.release / "cargo-verus",
            f'echo "$*" >>"$LOG/cargo-verus"\necho \'{json.dumps(REPORT)}\'\n',
        )
        # Installed as a symlink, as a user's ~/.local/bin may hold it.
        (self.bin / "verus").symlink_to(self.release / "verus")

    def run_script(self) -> subprocess.CompletedProcess:
        env = dict(os.environ, LOG=str(self.tmp))
        env["PATH"] = f"{self.bin}:{env['PATH']}"
        return subprocess.run(
            ["bash", str(SCRIPT)],
            check=False,
            env=env,
            capture_output=True,
            text=True,
            timeout=60,
        )

    def test_a_symlinked_verus_runs_its_release_s_cargo_verus(self):
        done = self.run_script()
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertIn("--locked", (self.tmp / "cargo-verus").read_text())

    def test_every_cargo_call_is_locked(self):
        """An unlocked `cargo clean` would rewrite a stale Cargo.lock."""
        self.assertEqual(self.run_script().returncode, 0)
        calls = (self.tmp / "cargo").read_text().splitlines()
        self.assertTrue(any(c.startswith("clean ") for c in calls), calls)
        for call in calls:
            self.assertIn("--locked", call.split(), call)

    def test_a_verus_without_its_cargo_verus(self):
        (self.release / "cargo-verus").unlink()
        done = self.run_script()
        self.assertEqual(done.returncode, 1)
        self.assertIn("cargo-verus is missing", done.stderr)

    def test_a_source_build_gets_a_hint(self):
        """A source build's cargo-verus knows no vstd for its own release."""
        tool(
            self.release / "cargo-verus",
            'echo "Error: Components are incompatible:" >&2\nexit 1\n',
        )
        done = self.run_script()
        self.assertEqual(done.returncode, 1)
        self.assertIn("Components are incompatible", done.stderr)
        self.assertIn("needs the official release zip", done.stderr)

    def test_another_failure_gets_no_hint(self):
        tool(self.release / "cargo-verus", 'echo "error: proof failed" >&2\nexit 1\n')
        done = self.run_script()
        self.assertEqual(done.returncode, 1)
        self.assertIn("proof failed", done.stderr)
        self.assertNotIn("release zip", done.stderr)


if __name__ == "__main__":
    unittest.main()
