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

# shellcheck source=scripts/rust-env.sh
source scripts/rust-env.sh

case "$1" in
    fmt) exec cargo fmt --all --check ;;
    clippy) exec cargo clippy --workspace --all-targets --locked -- -D warnings ;;
    test) exec cargo test --workspace --locked ;;
    *)
        echo "Usage: $0 fmt|clippy|test" >&2
        exit 2
        ;;
esac
