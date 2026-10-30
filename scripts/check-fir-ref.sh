#!/usr/bin/env bash
# Runs fir-ref over fir texts (ADR-2026-10-30-1250). The pre-commit hooks
# fir-ref-test and fir-round-trip call it, locally and in CI.
#   test        Builds the Lean package, which runs the Lean tests, then
#               checks print(parse(t)) == t on every canonical text of
#               tests/fir/, and that each non-canonical text prints as its
#               canonical sibling.
#   round-trip  Rust prints every text of tests/fir/ and modules from its
#               generator; fir-ref parses and reprints each one, and the
#               bytes must match.
set -euo pipefail

if [[ $# -ne 1 || ( "$1" != test && "$1" != round-trip ) ]]; then
    echo "Usage: $0 test|round-trip" >&2
    exit 2
fi

repo_root=$(git -C "$(dirname "${BASH_SOURCE[0]}")/.." rev-parse --show-toplevel)
cd "$repo_root"

# The only way to run Lake here: under the guards of ADR-2026-10-29-2135.
scripts/build-spec.sh --lean
fir_ref=$repo_root/lean/.lake/build/bin/fir-ref

case "$1" in
    test)
        status=0
        "$fir_ref" fmt --check tests/fir/canonical/*.fir || status=1
        for text in tests/fir/noncanonical/*.fir; do
            canonical=tests/fir/canonical/$(basename "$text")
            if ! "$fir_ref" fmt "$text" | cmp -s - "$canonical"; then
                echo "$text does not print as $canonical" >&2
                status=1
            fi
        done
        exit "$status"
        ;;
    round-trip)
        # As in check-rust.sh: the pin, not the environment, picks the
        # toolchain.
        unset RUSTUP_TOOLCHAIN
        if ! command -v cargo >/dev/null && [[ -x "$HOME/.cargo/bin/cargo" ]]; then
            PATH="$HOME/.cargo/bin:$PATH"
        fi
        out=$(mktemp -d)
        trap 'rm -rf "$out"' EXIT
        cargo run --quiet --locked -p funk-ir --example fir_texts -- "$out"
        if ! "$fir_ref" fmt --check "$out"/*.fir; then
            echo "fir-ref does not print the texts above as Rust prints them" >&2
            exit 1
        fi
        ;;
esac
