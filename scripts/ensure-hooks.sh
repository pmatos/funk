#!/usr/bin/env bash
# Install and verify the repository's pre-commit and commit-msg hooks.
# Run during provisioning, before making Git metadata read-only.
set -euo pipefail

if [[ $# -gt 1 || ( $# -eq 1 && "$1" != --check ) ]]; then
    echo "Usage: $0 [--check]" >&2
    exit 2
fi

repo_root=$(git -C "$(dirname "${BASH_SOURCE[0]}")/.." rev-parse --show-toplevel)
cd "$repo_root"

fail() {
    echo "Hook setup failed: $*" >&2
    echo "Do not edit or commit until hook setup succeeds. Provision hooks before mounting Git metadata read-only and provide a writable PRE_COMMIT_HOME cache." >&2
    exit 1
}

command -v pre-commit >/dev/null || fail "Install pre-commit first: uv tool install pre-commit"
[[ -z "${SKIP:-}" ]] || fail "Unset SKIP; required hooks must not be skipped."
if git config --get core.hooksPath >/dev/null; then
    fail "core.hooksPath is overridden; resolve it without disabling or overwriting existing hooks."
fi

hooks_installed() {
    local hook_type hook_path
    for hook_type in pre-commit commit-msg; do
        hook_path=$(git rev-parse --git-path "hooks/$hook_type")
        [[ -x "$hook_path" ]] && grep -q 'pre_commit' "$hook_path" || return 1
    done
}

if [[ "${1:-}" == --check ]]; then
    hooks_installed || fail "This worktree has no verified pre-commit and commit-msg hooks. Run ./scripts/ensure-hooks.sh first."
    exit 0
fi

if hooks_installed; then
    # A provisioned, read-only hooks directory needs no rewrite on resume.
    pre-commit install-hooks || fail "pre-commit could not prepare hook environments."
else
    # Do not use --overwrite: pre-commit preserves/chains existing Git hooks.
    pre-commit install --install-hooks || fail "pre-commit could not install the hooks or their environments."
fi
hooks_installed || fail "pre-commit and commit-msg must both be executable pre-commit hooks."

# The fir-spec, fir-ref-test and fir-round-trip hooks build the Lean code
# (ADR-2026-10-29-2135, ADR-2026-10-30-1250). A warning, not a failure: a
# commit that runs none of them can go on. It goes to stdout too, because a
# SessionStart hook that exits 0 shows only stdout.
if ! command -v elan >/dev/null && [[ ! -x "$HOME/.elan/bin/elan" ]]; then
    warning="Warning: elan, the Lean toolchain manager, is not installed.
The fir-spec, fir-ref-test and fir-round-trip hooks need it. A commit that
changes lean/, docs/spec/, tests/fir/, the Rust crates or the Rust toolchain
runs one of them, and so does every 'pre-commit run --all-files'.
Install it as https://github.com/leanprover/elan#installation says."
    echo "$warning"
    echo "$warning" >&2
fi
# The rust-* hooks build and test the Cargo workspace (ADR-2026-10-30-1030),
# and fir-round-trip runs it (ADR-2026-10-30-1250).
if ! command -v cargo >/dev/null && [[ ! -x "$HOME/.cargo/bin/cargo" ]]; then
    warning="Warning: cargo, from the Rust toolchain manager rustup, is not installed.
The rust-fmt, rust-clippy, rust-test and fir-round-trip hooks need it. A
commit that changes the Rust crates, the Rust toolchain, tests/fir/ or lean/
runs one of them, and so does every 'pre-commit run --all-files'.
Install rustup as https://rustup.rs says; it installs the toolchain that
rust-toolchain.toml pins on first use."
    echo "$warning"
    echo "$warning" >&2
fi
# The rust-test hook runs funk build, which needs GNU as and ld on an
# x86-64 Linux host (ADR-2026-10-30-1229).
host=$(uname -sm)
as_version=$(as --version 2>/dev/null || true)
ld_version=$(ld --version 2>/dev/null || true)
binutils_problem=""
if [[ "$host" != "Linux x86_64" ]]; then
    binutils_problem="This host is $host."
elif [[ "${as_version%%$'\n'*}" != "GNU assembler"* ]]; then
    binutils_problem="as is missing or is not GNU as."
elif [[ "${ld_version%%$'\n'*}" != "GNU ld"* ]]; then
    binutils_problem="ld is missing or is not GNU ld."
fi
if [[ -n "$binutils_problem" ]]; then
    warning="Warning: $binutils_problem
funk build and the rust-test hook, which runs on every
'pre-commit run --all-files', need GNU binutils (as and ld) on an x86-64
Linux host. Install binutils with your system's package manager, or work
on such a host."
    echo "$warning"
    echo "$warning" >&2
fi
echo "Repository hooks and environments are installed and verified."
