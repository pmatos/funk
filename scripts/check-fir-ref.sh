#!/usr/bin/env bash
# Runs fir-ref over fir texts (ADR-2026-10-30-1250). The pre-commit hooks
# fir-ref-test and fir-round-trip call it, locally and in CI.
#   test        Builds the Lean package, which runs the Lean tests, then
#               checks print(parse(t)) == t on every canonical text of
#               tests/fir/, in canonical/ and in llvm/, the modules ported
#               from LLVM's tests, that each non-canonical text prints as its
#               canonical sibling, that a string of ten million
#               characters is read and printed on a 256 KiB stack, that
#               a block of a million ops and a function of a million
#               blocks are reprinted within 120 seconds, and regions
#               nested 3,000 deep within 8 seconds of CPU time (#47), and
#               that fir-ref run and fmt write the signed maximum and
#               minimum of i16777215, of 5,050,445 digits, within 30
#               seconds of CPU time each (#41).
#               fir-ref validate accepts every text of tests/fir/, and
#               gives a module with an unreachable block, a text that does
#               not parse and a missing file their verdicts (#10); it exits
#               with 2 on an argument that is not UTF-8 and when it cannot
#               write its output. It accepts two functions of a million
#               blocks, each block using the value of the block before it:
#               a chain within 180 seconds of CPU time, and a chain of
#               checks that may each leave for one shared exit within 240
#               (#55). check-fir-ref-run.sh checks fir-ref run.
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
        "$fir_ref" fmt --check tests/fir/canonical/*.fir tests/fir/llvm/*.fir || status=1
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
        corpus=(tests/fir/canonical/*.fir tests/fir/noncanonical/*.fir tests/fir/llvm/*.fir)
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
        # Errors that are not about a file exit with 2, as funk's do
        # (ADR-2026-10-30-1032): an argument that is not UTF-8, a full disk,
        # and a reader that stops reading, which gets no message. The pipe
        # holds less than the reports of 4,000 files, so the write fails.
        rc=0
        "$fir_ref" validate $'bad\xff.fir' 2>"$tmp/err" || rc=$?
        if [[ $rc -ne 2 ]] || ! grep -q 'is not UTF-8' "$tmp/err"; then
            echo "fir-ref validate exits with $rc, not 2, on an argument that is not UTF-8" >&2
            status=1
        fi
        if [[ -w /dev/full ]]; then
            rc=0
            "$fir_ref" validate "$tmp/dead.fir" >/dev/full 2>"$tmp/err" || rc=$?
            if [[ $rc -ne 2 ]] || ! grep -q 'cannot write standard output' "$tmp/err"; then
                echo "fir-ref validate exits with $rc, not 2, when it cannot write" >&2
                status=1
            fi
        fi
        many=()
        for _ in {1..4000}; do many+=("$tmp/dead.fir"); done
        rc=0
        ("$fir_ref" validate "${many[@]}" 2>"$tmp/err" | true; exit "${PIPESTATUS[0]}") || rc=$?
        if [[ $rc -ne 2 || -s "$tmp/err" ]]; then
            echo "fir-ref validate exits with $rc, not 2 and silent, on a closed pipe" >&2
            status=1
        fi
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
        # Two functions of a million blocks, each block using the value of the
        # block before it (#55): a chain, and a chain of checks that may each
        # leave for one shared exit, the shape on which Cooper, Harvey and
        # Kennedy's lifting alone takes quadratic time. The spec's check
        # searches the graph once per such use, in time quadratic in the
        # number of blocks: hours here. fir-ref builds the dominator tree once
        # and takes 19 to 27, and 25 to 30, seconds of CPU time on a lightly
        # loaded host, and up to 75 and 88 under heavy load. Past the soft
        # limit it ends with SIGXCPU, status 152.
        awk -v end="$ending" 'BEGIN {
            printf "func @f() {\n^b0:\n  %%v0: i32 = const 0 @0\n"
            for (i = 1; i < 1000000; i++)
                printf "  br ^b%d @0\n^b%d:\n  %%v%d: i32 = freeze %%v%d @0\n", i, i, i, i - 1
            printf "  ret @0\n%s", end
        }' >"$tmp/chain.fir"
        awk -v end="$ending" 'BEGIN {
            printf "func @f(%%c: i1) -> i32 {\n^e:\n  %%v0: i32 = const 0 @0\n  br ^c1 @0\n"
            for (i = 1; i < 999999; i++) {
                printf "^c%d:\n  %%v%d: i32 = freeze %%v%d @0\n", i, i, i - 1
                printf "  cond_br %%c, ^%s, ^j @0\n", i < 999998 ? "c" (i + 1) : "j"
            }
            printf "^j:\n  ret %%v0 @0\n%s", end
        }' >"$tmp/exits.fir"
        for check in "chain:180:a chain of a million blocks" \
            "exits:240:a million blocks that may each leave for one exit"; do
            IFS=: read -r name limit what <<<"$check"
            rc=0
            (ulimit -c 0 && ulimit -S -t "$limit" && exec "$fir_ref" validate "$tmp/$name.fir") \
                >"$tmp/$name.json" || rc=$?
            if [[ $rc -ne 0 ]] || ! grep -q '"verdict":"accepted"' "$tmp/$name.json"; then
                why=""
                if [[ $rc -eq 152 ]]; then why=" within $limit seconds of CPU time"; fi
                echo "fir-ref validate does not accept $what$why" >&2
                status=1
            fi
        done
        # The widest constants (#41): the signed maximum of i16777215,
        # 2^16777214 - 1, and its minimum have 5,050,445 digits. fir-ref run
        # computes the maximum, whose length and last nine digits are checked
        # here, fir-ref fmt reprints a module with both constants, and
        # fir-ref run returns them. Each takes about 5 seconds of CPU time,
        # and runs under a soft limit of 30; the spec's printInt, quadratic
        # in the number of digits, takes hours.
        printf 'func @max() -> i16777215 {\n^e:\n  %%a: i16777215 = const -1 @0\n' >"$tmp/max.fir"
        printf '  %%b: i16777215 = const 1 @0\n  %%m: i16777215 = lshr %%a, %%b @0\n' >>"$tmp/max.fir"
        printf '  ret %%m @0\n}\n\nlocs {\n  @0 = unknown\n}\n' >>"$tmp/max.fir"
        # widest WHAT ARGS...: fir-ref ARGS... succeeds within 30 seconds of
        # CPU time, or the check reports that fir-ref does not WHAT.
        widest() {
            local what=$1 rc=0
            shift
            (ulimit -c 0; ulimit -S -t 30; exec "$fir_ref" "$@") || rc=$?
            case $rc in
                0) return 0 ;;
                152) what+=" within 30 seconds of CPU time" ;;
            esac
            echo "fir-ref does not $what" >&2
            return 1
        }
        widest "compute 2^16777214 - 1" run "$tmp/max.fir" @max >"$tmp/max.json" || status=1
        max=$(sed -n 's/^{"kind":"return","values":\["\([0-9]*\)"\],"choices":0}$/\1/p' "$tmp/max.json")
        # The last nine digits of 2^16777214, by repeated squaring.
        r=1 b=2 e=16777214 m=1000000000
        while ((e > 0)); do
            if ((e & 1)); then r=$((r * b % m)); fi
            b=$((b * b % m)) e=$((e >> 1))
        done
        printf -v last '%09d' $(((r + m - 1) % m))
        if [[ ${#max} -ne 5050445 || ${max: -9} != "$last" ]]; then
            echo "fir-ref run does not return 2^16777214 - 1 at i16777215" >&2
            status=1
        else
            # 2^16777214 ends in 4, so the minimum is the maximum's digits
            # with the last one 4, negated.
            min=-${max%?}4
            {
                printf 'func @f() -> i16777215, i16777215 {\n^e:\n'
                printf '  %%max: i16777215 = const %s @0\n' "$max"
                printf '  %%min: i16777215 = const %s @0\n' "$min"
                printf '  ret %%max, %%min @0\n}\n\nlocs {\n  @0 = unknown\n}\n'
            } >"$tmp/widest.fir"
            widest "reprint the widest constants" fmt --check "$tmp/widest.fir" || status=1
            want=$(printf '{"kind":"return","values":["%s","%s"],"choices":0}' "$max" "$min")
            if ! widest "return the widest constants" run "$tmp/widest.fir" @f >"$tmp/widest.json"; then
                status=1
            elif [[ $(<"$tmp/widest.json") != "$want" ]]; then
                echo "fir-ref run does not return the widest constants as their text writes them" >&2
                status=1
            fi
        fi
        # fir-ref run runs functions and prints their results (#10, #14 to
        # #20); check-fir-ref-run.sh holds those checks.
        scripts/check-fir-ref-run.sh "$fir_ref" || status=1
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
