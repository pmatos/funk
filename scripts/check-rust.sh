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
    test)
        if [[ -z "${GITHUB_STEP_SUMMARY:-}" ]]; then
            exec cargo test --workspace --locked
        fi
        # In CI, the counts also go to the job summary (ADR-2026-11-05-1408).
        log=$(mktemp)
        trap 'rm -f "$log"' EXIT
        status=0
        cargo test --workspace --locked | tee "$log" || status=$?
        if ! python3 -I scripts/suite_summary.py cargo-test "$log" "$status"; then
            status=$((status ? status : 1))
        fi
        exit "$status"
        ;;
    *)
        echo "Usage: $0 fmt|clippy|test" >&2
        exit 2
        ;;
esac
