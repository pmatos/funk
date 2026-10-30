#!/usr/bin/env bash
# Runs one Rust check over the whole Cargo workspace: fmt, clippy or test.
# The pre-commit hooks rust-fmt, rust-clippy and rust-test call it, locally
# and in CI (ADR-2026-10-30-1030). rust-toolchain.toml pins the toolchain;
# rustup installs it on first use.
set -euo pipefail

if [[ $# -ne 1 ]]; then
    echo "Usage: $0 fmt|clippy|test" >&2
    exit 2
fi

cd "$(git -C "$(dirname "${BASH_SOURCE[0]}")/.." rev-parse --show-toplevel)"

# The pin, not the environment, picks the toolchain, so a local pass predicts
# a CI pass.
unset RUSTUP_TOOLCHAIN

if ! command -v cargo >/dev/null; then
    if [[ -x "$HOME/.cargo/bin/cargo" ]]; then
        PATH="$HOME/.cargo/bin:$PATH"
    else
        echo "cargo is not installed. Install rustup as https://rustup.rs says." >&2
        exit 1
    fi
fi

pinned=$(sed -n 's/^channel = "\(.*\)"$/\1/p' rust-toolchain.toml)
for tool in cargo rustc; do
    version=$("$tool" --version | cut -d' ' -f2)
    if [[ "$version" != "$pinned" ]]; then
        echo "$tool on PATH is $version, not $pinned as rust-toolchain.toml pins." >&2
        echo "Put rustup's cargo and rustc first on PATH: they follow the pin." >&2
        exit 1
    fi
done

case "$1" in
    fmt) exec cargo fmt --all --check ;;
    clippy) exec cargo clippy --workspace --all-targets --locked -- -D warnings ;;
    test) exec cargo test --workspace --locked ;;
    *)
        echo "Usage: $0 fmt|clippy|test" >&2
        exit 2
        ;;
esac
