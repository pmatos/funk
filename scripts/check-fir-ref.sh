#!/usr/bin/env bash
# Runs fir-ref over fir texts (ADR-2026-10-30-1250). The pre-commit hooks
# fir-ref-test and fir-round-trip call it, locally and in CI.
#   test        Builds the Lean package, which runs the Lean tests, then
#               checks print(parse(t)) == t on every canonical text of
#               tests/fir/, that each non-canonical text prints as its
#               canonical sibling, that a string of ten million
#               characters is read and printed on a 256 KiB stack, and
#               that long blocks and deep regions are reprinted in
#               seconds (#47).
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

# fir-ref and cargo run code from this repository; keep CI tokens away.
unset GH_TOKEN GITHUB_TOKEN

if [[ "$1" == round-trip ]]; then
    # Before the Lean build, so that a missing cargo fails at once.
    # shellcheck source=scripts/rust-env.sh
    source scripts/rust-env.sh
fi

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
        tmp=$(mktemp -d)
        trap 'rm -rf "$tmp"' EXIT
        {
            printf 'func @f() {\n^e:\n  ret @0\n}\n\nlocs {\n  @0 = "'
            head -c 10000000 /dev/zero | tr '\0' f
            printf '":1:1 to 1:2\n}\n'
        } >"$tmp/long.fir"
        if ! LEAN_STACK_SIZE_KB=256 "$fir_ref" fmt --check "$tmp/long.fir"; then
            echo "fir-ref does not reprint a string of ten million characters on a 256 KiB stack" >&2
            status=1
        fi
        # Large canonical texts. The spec's printer takes time quadratic in
        # the length of a block, over 400 seconds for each of the first two,
        # and cubic in the depth of regions; fir-ref's printer takes time
        # linear in the text it writes.
        ending='}\n\nlocs {\n  @0 = unknown\n}\n'
        awk -v end="$ending" 'BEGIN {
            printf "func @f() {\n^e:\n"
            for (i = 0; i < 1000000; i++) printf "  %%c%d: i32 = const %d @0\n", i, i
            printf "  ret @0\n%s", end
        }' >"$tmp/ops.fir"
        awk -v end="$ending" 'BEGIN {
            printf "func @f() {\n"
            for (i = 0; i < 1000000; i++) printf "^b%d:\n  ret @0\n", i
            printf "%s", end
        }' >"$tmp/blocks.fir"
        awk -v end="$ending" 'function pad(w) { return sprintf("%" w "s", "") }
        BEGIN {
            n = 3000
            printf "func @f() {\n^e:\n"
            for (i = 0; i < n; i++) printf "%sbr {\n%s^b:\n", pad(2 + 4 * i), pad(4 + 4 * i)
            printf "%sret @0\n", pad(2 + 4 * n)
            for (i = n - 1; i >= 0; i--) printf "%s} @0\n", pad(2 + 4 * i)
            printf "%s", end
        }' >"$tmp/regions.fir"
        for check in "ops:a block of a million ops" "blocks:a function of a million blocks" \
            "regions:regions nested 3,000 deep"; do
            if ! timeout 120 "$fir_ref" fmt --check "$tmp/${check%%:*}.fir"; then
                echo "fir-ref does not reprint ${check#*:} within 120 seconds" >&2
                status=1
            fi
        done
        exit "$status"
        ;;
    round-trip)
        out=$(mktemp -d)
        trap 'rm -rf "$out"' EXIT
        cargo run --quiet --locked -p funk-ir --example fir_texts -- "$out"
        if ! "$fir_ref" fmt --check "$out"/*.fir; then
            echo "fir-ref does not print the texts above as Rust prints them" >&2
            exit 1
        fi
        ;;
esac
