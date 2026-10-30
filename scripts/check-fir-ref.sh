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
#               not parse and a missing file their verdicts (#10); it exits
#               with 2 on an argument that is not UTF-8 and when it cannot
#               write its output. fir-ref run runs functions of tests/fir/
#               and prints the result that each one should give (#10),
#               runs a function that freezes poison in scripted and
#               exhaustive mode (#14), and runs bitwise ops and shifts
#               (#15).
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
        # fir-ref run runs the functions of the corpus and prints each
        # result as one JSON object (ADR-2026-10-30-1856). runs FILE STATUS
        # OUTPUT ARGS...: fir-ref run FILE ARGS... exits with STATUS and
        # prints OUTPUT, a JSON result on standard output or a message on
        # standard error, and nothing on the other stream.
        runs() {
            local file=$1 want_rc=$2 want=$3 rc=0 out err want_out want_err
            shift 3
            out=$("$fir_ref" run "$file" "$@" 2>"$tmp/run.err") || rc=$?
            err=$(<"$tmp/run.err")
            if [[ $want == "{"* ]]; then
                want_out=$want want_err=''
            else
                want_out='' want_err=$want
            fi
            if [[ $rc -ne $want_rc || $out != "$want_out" || $err != "$want_err" ]]; then
                echo "fir-ref run $file $* exits with $rc, prints '$out' and" \
                    "'$err' on standard error; expected $want_rc, '$want_out'" \
                    "and '$want_err'" >&2
                return 1
            fi
        }
        c=tests/fir/canonical
        ret='{"kind":"return","values":'
        # A run that makes no choice says so (ADR-2026-10-30-2218).
        none=',"choices":0}'
        while read -r file want args; do
            # shellcheck disable=SC2086 # ARGS is a list of words.
            runs "$c/$file" 0 "$ret$want$none" $args || status=1
        done <<'END'
add.fir ["6"] @add3 1 2 3
add.fir ["-2147483648"] @add3 2147483647 1 0
add.fir ["-10"] @double -5
locations.fir ["15"] @f 1
names.fir ["105"] @names 1 2 3
results.fir [] @none
results.fir ["-7"] @one -7
results.fir ["2","2","1"] @several 1 2
results.fir [] @unused 3
seven.fir ["7"] @seven
symbols.fir [] @_start.v2
widths.fir ["true","false"] @booleans
widths.fir ["-128","127","0","-1"] @bytes
widths.fir ["-63","-4294967296"] @odd 1 1
widths.fir ["-9223372036854775808","170141183460469231731687303715884105727","-170141183460469231731687303715884105728"] @wide
widths.fir ["-1"] @widest 0
END
        # shellcheck disable=SC2016 # The symbols are written as text writes them.
        for sym in '@"1"' '@"a b"' '@""' '@"_ZN3foo$LT$E"' '@"tab\tquote\"slash\\line\n"' \
            '@"\u{202e}hidden\u{85}\u{feff}\u{1}"' '@"résumé"'; do
            runs $c/symbols.fir 0 "${ret}[]$none" "$sym" || status=1
        done
        runs tests/fir/noncanonical/add.fir 0 "${ret}[\"6\"]$none" @add3 1 2 3 || status=1
        runs $c/seven.fir 0 '{"kind":"fuel-exhausted","choices":0}' --fuel 1 @seven || status=1
        runs - 0 "${ret}[\"7\"]$none" @seven <$c/seven.fir || status=1
        printf 'func @f() -> i32 {\n^e:\n  %%c: i32 = const 1 @0\n}\n\nlocs {\n  @0 = unknown\n}\n' \
            >"$tmp/open-block.fir"
        runs "$tmp/open-block.fir" 1 \
            '{"kind":"stuck","reason":"a block ends without a terminator","choices":0}' @f || status=1
        printf 'func @f(%%a: i8) -> i8 {\n^e:\n  %%s: i8 = and %%a, %%a @0\n  ret %%s @0\n}\n' \
            >"$tmp/and.fir"
        printf '\nlocs {\n  @0 = unknown\n}\n' >>"$tmp/and.fir"
        runs "$tmp/and.fir" 0 "${ret}[\"-3\"]$none" @f -3 || status=1
        # A shift by N or more gives poison (#15).
        printf 'func @f(%%a: i8, %%n: i8) -> i8 {\n^e:\n  %%s: i8 = ashr %%a, %%n @0\n' >"$tmp/ashr.fir"
        printf '  ret %%s @0\n}\n\nlocs {\n  @0 = unknown\n}\n' >>"$tmp/ashr.fir"
        runs "$tmp/ashr.fir" 0 "${ret}[\"-1\"]$none" @f -128 7 || status=1
        runs "$tmp/ashr.fir" 0 "${ret}[\"poison\"]$none" @f -128 8 || status=1
        # An op without rules is an error (ADR-2026-10-30-1855).
        printf 'func @f(%%a: i8) -> i1 {\n^e:\n  %%s: i1 = icmp eq %%a, %%a @0\n  ret %%s @0\n}\n' \
            >"$tmp/icmp.fir"
        printf '\nlocs {\n  @0 = unknown\n}\n' >>"$tmp/icmp.fir"
        runs "$tmp/icmp.fir" 2 'fir-ref: @f: icmp eq has no execution rules yet' @f 1 || status=1
        # freeze of poison makes a choice: %a + 1 overflows i2 at 1
        # (ADR-2026-10-30-2218).
        printf 'func @f(%%a: i2) -> i2 {\n^e:\n  %%m: i2 = const 1 @0\n' >"$tmp/freeze.fir"
        printf '  %%p: i2 = add nsw %%a, %%m @0\n  %%f: i2 = freeze %%p @0\n  ret %%f @0\n}\n' \
            >>"$tmp/freeze.fir"
        printf '\nlocs {\n  @0 = unknown\n}\n' >>"$tmp/freeze.fir"
        runs "$tmp/freeze.fir" 0 "${ret}[\"-1\"],\"choices\":1}" --choices -1 @f 1 || status=1
        runs "$tmp/freeze.fir" 0 "${ret}[\"1\"]$none" @f 0 || status=1
        runs "$tmp/freeze.fir" 2 'fir-ref: @f: the choices do not fit the run: the run makes choice 1, of type i2, and --choices gives 0 choices' \
            @f 1 || status=1
        runs "$tmp/freeze.fir" 2 'fir-ref: @f: the choices do not fit the run: choice 1, 2, is not a value of type i2' \
            --choices 2 @f 1 || status=1
        outcomes='{"kind":"outcomes","choices":1,"outcomes":['
        for v in 0 1 -2 -1; do outcomes+="${ret}[\"$v\"]},"; done
        runs "$tmp/freeze.fir" 0 "${outcomes%,}]}" --exhaustive @f 1 || status=1
        runs "$tmp/freeze.fir" 0 '{"kind":"choice-budget-exceeded","budget":1}' \
            --exhaustive --choice-bits 1 @f 1 || status=1
        runs $c/add.fir 2 'fir-ref: 9223372036854775808 is not a value of type i64' \
            @double 9223372036854775808 || status=1
        runs $c/add.fir 2 'fir-ref: poison is not a value of type i64' @double poison || status=1
        runs $c/add.fir 2 'fir-ref: @add3 takes 3 arguments, not 2' @add3 1 2 || status=1
        runs $c/empty.fir 2 "fir-ref: $c/empty.fir has no function @f" @f || status=1
        rc=0
        "$fir_ref" run "$tmp/missing.fir" @f 2>/dev/null || rc=$?
        if [[ $rc -ne 2 ]]; then
            echo "fir-ref run on a missing file exits with $rc, not 2" >&2
            status=1
        fi
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
