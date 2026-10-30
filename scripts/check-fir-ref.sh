#!/usr/bin/env bash
# Runs fir-ref over fir texts (ADR-2026-10-30-1250). The pre-commit hooks
# fir-ref-test and fir-round-trip call it, locally and in CI.
#   test        Builds the Lean package, which runs the Lean tests, then
#               checks print(parse(t)) == t on every canonical text of
#               tests/fir/, that each non-canonical text prints as its
#               canonical sibling, that a string of ten million
#               characters is read and printed on a 256 KiB stack, that
#               a block of a million ops and a function of a million
#               blocks are reprinted within 120 seconds, and regions
#               nested 3,000 deep within 8 seconds of CPU time (#47).
#               fir-ref validate accepts every text of tests/fir/, and
#               gives a module with an unreachable block, a text that does
#               not parse and a missing file their verdicts (#10).
#   round-trip  Rust prints every text of tests/fir/ and modules from its
#               generator; fir-ref parses and reprints each one, and the
#               bytes must match. fir-ref validate accepts each one: the
#               generator makes valid modules, which funk verify accepts.
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
        # fir-ref validate reports one JSON verdict per file (ADR-2026-10-30-1741).
        corpus=(tests/fir/canonical/*.fir tests/fir/noncanonical/*.fir)
        rc=0
        "$fir_ref" validate "${corpus[@]}" >"$tmp/corpus.json" || rc=$?
        accepted=$(grep -c '"verdict":"accepted"' "$tmp/corpus.json" || true)
        if [[ $rc -ne 0 || $accepted -ne ${#corpus[@]} ]]; then
            grep -v '"verdict":"accepted"' "$tmp/corpus.json" >&2 || true
            echo "fir-ref validate does not accept every text of tests/fir/" >&2
            status=1
        fi
        printf 'func @f() -> i32 {\n^entry:\n  %%c: i32 = const 0 @0\n  ret %%c @0\n' >"$tmp/dead.fir"
        printf '^dead:\n  %%d: i32 = const 1 @0\n  ret %%d @0\n}\n\nlocs {\n  @0 = unknown\n}\n' \
            >>"$tmp/dead.fir"
        printf 'func @f() {\n' >"$tmp/open.fir"
        # validates FILE STATUS PATTERN: fir-ref validate exits with STATUS on
        # FILE, and its report matches PATTERN.
        validates() {
            local rc=0 report
            report=$("$fir_ref" validate "$1") || rc=$?
            if [[ $rc -ne $2 ]] || ! grep -q -- "$3" <<<"$report"; then
                echo "fir-ref validate $1 exits with $rc, not $2, or its report lacks $3: $report" >&2
                return 1
            fi
        }
        validates "$tmp/dead.fir" 1 '"verdict":"validation-error".*block ^dead is not reachable' ||
            status=1
        validates "$tmp/open.fir" 1 '"verdict":"parse-error".*"line":2,"column":1' || status=1
        validates "$tmp/missing.fir" 2 '"verdict":"io-error"' || status=1
        # Large canonical texts (#47). On a block of a million ops and on a
        # function of a million blocks, the spec's printer, quadratic in a
        # block's length, takes over 400 seconds: the wall-clock limit
        # catches it. On regions nested 3,000 deep, cubic in the depth, it
        # takes about 30 seconds of CPU time, and fir-ref 1 or 2: that case
        # also runs under a soft limit on CPU time, which, unlike wall-clock
        # time, the machine's load barely changes. Past the limit fir-ref
        # ends with SIGXCPU, status 152, and writes no core file.
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
        reprint() {
            ulimit -c 0
            if [[ $1 == regions ]]; then
                ulimit -S -t 8
            fi
            exec timeout 120 "$fir_ref" fmt --check "$tmp/$1.fir"
        }
        for check in "ops:a block of a million ops" "blocks:a function of a million blocks" \
            "regions:regions nested 3,000 deep"; do
            rc=0
            (reprint "${check%%:*}") || rc=$?
            case $rc in
                0) continue ;;
                124) why=" within 120 seconds" ;;
                152) why=" within 8 seconds of CPU time" ;;
                *) why="" ;;
            esac
            echo "fir-ref does not reprint ${check#*:}$why" >&2
            status=1
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
        if ! verdicts=$("$fir_ref" validate "$out"/*.fir); then
            grep -v '"verdict":"accepted"' <<<"$verdicts" >&2 || true
            echo "fir-ref validate rejects the texts above, which funk verify accepts" >&2
            exit 1
        fi
        ;;
esac
