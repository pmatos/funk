#!/usr/bin/env bash
# Checks fir-ref run (ADR-2026-10-30-1856). check-fir-ref.sh test calls it
# with the fir-ref that it builds: scripts/check-fir-ref-run.sh FIR_REF.
# fir-ref run runs functions of tests/fir/ and prints the result that each
# one should give (#10), runs a function that freezes poison in scripted
# and exhaustive mode (#14), runs bitwise ops and shifts (#15), runs icmp
# and select (#16), runs loops with br and cond_br, a branch on poison and a
# loop that never ends (#19), and runs calls: a function named by a quoted
# symbol returns its callee's result, and a call without end runs out of
# fuel (#20). On a 256 KiB stack, that loop and that call run out of a
# million steps in each mode (#47). It runs functions on poison arguments,
# and rejects poison where it is not an argument of an integer type (#123).
# It rejects an argument that is a long comment, on a 256 KiB stack (#135).
set -euo pipefail

if [[ $# -ne 1 ]]; then
    echo "Usage: $0 FIR_REF" >&2
    exit 2
fi
fir_ref=$1

repo_root=$(git -C "$(dirname "${BASH_SOURCE[0]}")/.." rev-parse --show-toplevel)
cd "$repo_root"

# fir-ref runs code from this repository; keep CI tokens away.
unset GH_TOKEN GITHUB_TOKEN

status=0
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
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
# icmp reads its operands as signed or unsigned, by its predicate,
# and select gives the value its condition chooses (#16).
printf 'func @f(%%a: i8, %%b: i8) -> i1, i1, i8 {\n^e:\n  %%s: i1 = icmp slt %%a, %%b @0\n' \
    >"$tmp/icmp.fir"
printf '  %%u: i1 = icmp ult %%a, %%b @0\n  %%m: i8 = select %%s, %%a, %%b @0\n' >>"$tmp/icmp.fir"
printf '  ret %%s, %%u, %%m @0\n}\n\nlocs {\n  @0 = unknown\n}\n' >>"$tmp/icmp.fir"
runs "$tmp/icmp.fir" 0 "${ret}[\"true\",\"false\",\"-1\"]$none" @f -1 1 || status=1
# br and cond_br run the spec's @sum; a branch on poison is UB, and
# a loop that never ends runs out of the fuel that --fuel sets (#19).
cat >"$tmp/loops.fir" <<'END'
func @sum(%n: i32) -> i32 {
^entry:
  %zero: i32 = const 0 @0
  br ^loop(%zero, %zero) @0
^loop(%i: i32, %acc: i32):
  %done: i1 = icmp sge %i, %n @0
  cond_br %done, ^exit(%acc), ^body @0
^body:
  %acc1: i32 = add nsw %acc, %i @0
  %one: i32 = const 1 @0
  %i1: i32 = add nsw %i, %one @0
  br ^loop(%i1, %acc1) @0
^exit(%r: i32):
  ret %r @0
}

func @branch(%a: i1) -> i1 {
^entry:
  %p: i1 = add nsw %a, %a @0
  cond_br %p, ^x(%a), ^x(%p) @0
^x(%r: i1):
  ret %r @0
}

func @spin() {
^entry:
  br ^l @0
^l:
  br ^l @0
}

locs {
  @0 = unknown
}
END
exhausted='{"kind":"fuel-exhausted","choices":0}'
runs "$tmp/loops.fir" 0 "${ret}[\"45\"]$none" @sum 10 || status=1
runs "$tmp/loops.fir" 0 "$exhausted" --fuel 64 @sum 10 || status=1
runs "$tmp/loops.fir" 0 "${ret}[\"false\"]$none" @branch false || status=1
runs "$tmp/loops.fir" 0 '{"kind":"ub","reason":"cond_br on poison","choices":0}' \
    @branch true || status=1
runs "$tmp/loops.fir" 0 "$exhausted" --fuel 1000 @spin || status=1
# A call runs its callee, which may be any function of the module,
# named as text names it, and a call without end runs out of fuel
# (#20).
{
    printf 'func @f(%%a: i8) -> i8 {\n^e:\n  %%s: i8 = call @f %%a @0\n  ret %%s @0\n}\n'
    printf '\nfunc @"1"(%%a: i8) -> i8 {\n^e:\n  %%s: i8 = call @g %%a @0\n  ret %%s @0\n}\n'
    printf '\nfunc @g(%%a: i8) -> i8 {\n^e:\n  %%s: i8 = add %%a, %%a @0\n  ret %%s @0\n}\n'
    printf '\nlocs {\n  @0 = unknown\n}\n'
} >"$tmp/call.fir"
runs "$tmp/call.fir" 0 "$exhausted" --fuel 100 @f 1 || status=1
runs "$tmp/call.fir" 0 "${ret}[\"42\"]$none" '@"1"' 21 || status=1
# fir-ref run takes no stack per step or per level of calls (#47): on a
# 256 KiB stack, @spin and @f above, a loop and a recursion that never
# end, run out of a budget of a million steps in each mode, never abort.
while read -r want mode; do
    for run in "loops.fir @spin" "call.fir @f 1"; do
        # shellcheck disable=SC2086 # MODE and RUN are lists of words.
        (ulimit -c 0 && LEAN_STACK_SIZE_KB=256 runs "$tmp/${run%% *}" 0 "$want" \
            --fuel 1000000 $mode ${run#* }) || status=1
    done
done <<END
$exhausted
{"kind":"outcomes","choices":0,"outcomes":[{"kind":"fuel-exhausted"}]} --exhaustive
{"kind":"fuel-exhausted","choices":0,"sequence":[]} --seed 7
END
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
# An argument is lexed over positions, with no stack per character: a
# comment of 100,000 characters is no value, alone or after one, on a
# 256 KiB stack (#135).
long="// $(head -c 100000 /dev/zero | tr '\0' x)"
for arg in "$long" "1 $long"; do
    LEAN_STACK_SIZE_KB=256 runs $c/add.fir 2 "fir-ref: $arg is not a value of type i64" \
        @double "$arg" || status=1
done
# poison is an argument of any iN (#123) and of ptr, the only one of ptr
# since a run starts with no allocation, but not a choice.
runs $c/add.fir 0 "${ret}[\"poison\"]$none" @double poison || status=1
runs $c/add.fir 0 "${ret}[\"poison\"]$none" @add3 1 poison 3 || status=1
runs $c/add.fir 2 'fir-ref: Poison is not a value of type i64' @double Poison || status=1
runs "$tmp/freeze.fir" 0 "${ret}[\"-2\"],\"choices\":1}" --choices -2 @f poison || status=1
runs "$tmp/freeze.fir" 0 "${outcomes%,}]}" --exhaustive @f poison || status=1
runs "$tmp/freeze.fir" 2 'fir-ref: @f: the choices do not fit the run: choice 1, poison, is not a value of type i2' \
    --choices poison @f poison || status=1
printf 'func @p(%%x: ptr) -> ptr {\n^e:\n  ret %%x @0\n}\n\nlocs {\n  @0 = unknown\n}\n' >"$tmp/ptr.fir"
runs "$tmp/ptr.fir" 0 "${ret}[\"poison\"]$none" @p poison || status=1
runs "$tmp/ptr.fir" 2 'fir-ref: 0 is not a value of type ptr' @p 0 || status=1
runs $c/add.fir 2 'fir-ref: @add3 takes 3 arguments, not 2' @add3 1 2 || status=1
runs $c/empty.fir 2 "fir-ref: $c/empty.fir has no function @f" @f || status=1
rc=0
"$fir_ref" run "$tmp/missing.fir" @f 2>/dev/null || rc=$?
if [[ $rc -ne 2 ]]; then
    echo "fir-ref run on a missing file exits with $rc, not 2" >&2
    status=1
fi
exit "$status"
