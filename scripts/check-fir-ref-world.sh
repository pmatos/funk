#!/usr/bin/env bash
# Checks fir-ref run --world (docs/decisions/fir-ref-run-end.md).
# check-fir-ref.sh test calls it with the fir-ref that it builds:
# scripts/check-fir-ref-world.sh FIR_REF. With a scripted world, fir-ref run
# reports the trace of each path and, at a return, what escaped and the
# memory that an observer reaches: the allocation that a returned pointer
# points into, and those that its units point into, but not a stack
# allocation freed at the return (#233, stage 4). A run of the core and gpu
# shows no event yet, so an empty script fits it and a script that answers
# an event does not; a script that does not read is an error. On a 256 KiB
# stack, it reports a chain of 10,000 work-group allocations, each holding a
# pointer into the one before it, and an allocation of 100,000 units.
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
# runs STATUS OUTPUT ARGS...: fir-ref run ARGS... exits with STATUS and
# prints OUTPUT, a JSON result on standard output or a message on
# standard error, and nothing on the other stream.
runs() {
    local want_rc=$1 want=$2 rc=0 out err want_out want_err
    shift 2
    out=$("$fir_ref" run "$@" 2>"$tmp/run.err") || rc=$?
    err=$(<"$tmp/run.err")
    if [[ $want == "{"* ]]; then
        want_out=$want want_err=''
    else
        want_out='' want_err=$want
    fi
    if [[ $rc -ne $want_rc || $out != "$want_out" || $err != "$want_err" ]]; then
        echo "fir-ref run $* exits with $rc, prints '$out' and '$err' on standard" \
            "error; expected $want_rc, '$want_out' and '$want_err'" >&2
        return 1
    fi
}
c=tests/fir/canonical
: >"$tmp/none.world"
printf '# This script answers no event.\n\n' >"$tmp/quiet.world"
printf 'answer 5\nstore 0 0 0x07\n' >"$tmp/one.world"
printf 'answer\nfree x\n' >"$tmp/bad.world"
printf '# CRLF line ends and tabs read as LF and spaces.\r\n\t\r\n' >"$tmp/crlf.world"
w="--world $tmp/none.world"
end='"trace":[],"escaped":[],"memory":[]'
# A run with no pointer: what fir-ref run reports, with an empty trace and no
# memory, in every mode.
# shellcheck disable=SC2086 # $w is two words.
runs 0 "{\"kind\":\"return\",\"values\":[\"6\"],$end,\"choices\":0}" $w $c/add.fir @add3 1 2 3 ||
    status=1
for quiet in quiet crlf; do
    runs 0 "{\"kind\":\"return\",\"values\":[\"6\"],$end,\"choices\":0}" \
        --world "$tmp/$quiet.world" $c/add.fir @add3 1 2 3 || status=1
done
# shellcheck disable=SC2086
runs 0 "{\"kind\":\"outcomes\",\"choices\":0,\"outcomes\":[{\"kind\":\"return\",\"values\":[\"poison\"],$end}]}" \
    $w --exhaustive $c/add.fir @double poison || status=1
# shellcheck disable=SC2086
runs 0 "{\"kind\":\"return\",\"values\":[\"-10\"],$end,\"choices\":0,\"sequence\":[]}" \
    $w --seed 7 $c/add.fir @double -5 || status=1
# The work-group allocations that a kernel returns pointers into outlive the
# call, and an observer reaches them; a stack allocation is freed at the
# return, so a pointer into it is dangling and reaches nothing.
poisons=$(printf '"poison",%.0s' $(seq 16))
block='"kind":"global","align":4,"size":16,"live":true,"units":['"${poisons%,}"']'
# shellcheck disable=SC2086
runs 0 "{\"kind\":\"return\",\"values\":[\"ptr(0, 0)\",\"ptr(1, 0)\"],\"trace\":[],\"escaped\":[],\"memory\":[{\"memory\":3,\"alloc\":0,$block},{\"memory\":3,\"alloc\":1,$block}],\"choices\":0}" \
    $w $c/gpu-work-group.fir @dev::@twice || status=1
# shellcheck disable=SC2086
runs 0 "{\"kind\":\"return\",\"values\":[\"ptr(0, 0)\",\"ptr(1, 0)\"],\"trace\":[],\"escaped\":[],\"memory\":[{\"memory\":3,\"alloc\":0,\"kind\":\"global\",\"align\":2,\"size\":2,\"live\":true,\"units\":[\"poison\",\"poison\"]}],\"choices\":0}" \
    $w $c/gpu-work-group.fir @dev::@both || status=1
# UB keeps the trace before it.
# shellcheck disable=SC2086
runs 0 '{"kind":"ub","reason":"a misaligned access","trace":[],"choices":0}' \
    $w $c/gpu-work-group.fir @dev::@misaligned || status=1
# A script that answers an event fits no run of the core and gpu, and a
# script that does not read is an error.
printf 'answer\t5\r\nstore 0 0 0x07\r\n' >"$tmp/crlf-one.world"
for one in one crlf-one; do
    runs 2 'fir-ref: @add3: the world'"'"'s script does not fit the run: the run shows no event, and the script answers 1' \
        --world "$tmp/$one.world" $c/add.fir @add3 1 2 3 || status=1
done
runs 2 "fir-ref: $tmp/bad.world: line 2: free x is not an answer or an action of the world" \
    --world "$tmp/bad.world" $c/add.fir @add3 1 2 3 || status=1
rc=0
"$fir_ref" run --world "$tmp/missing.world" $c/add.fir @add3 1 2 3 >"$tmp/run.out" 2>"$tmp/run.err" ||
    rc=$?
if [[ $rc -ne 2 || -s "$tmp/run.out" || $(<"$tmp/run.err") != "fir-ref: cannot read $tmp/missing.world: "* ]]; then
    echo "fir-ref run --world with a missing script exits with $rc, not 2 with an I/O error" >&2
    status=1
fi
# The memory an observer reaches is walked with no stack per allocation: a
# chain of 10,000 work-group allocations, each holding a pointer into the
# one before it, on a 256 KiB stack. The walk reaches them from the last.
# Memory 0 starts with @chain's own allocation (#235), so the work-group
# allocations take the ids from 1.
n=10000
{
    printf 'module @dev() {\n  dialects gpu\n\n  func @chain() -> ptr {\n  ^e:\n'
    printf '    %%p0: ptr = gpu.work_group_alloca ptr @0\n'
    for i in $(seq "$n"); do
        printf '    %%p%d: ptr = gpu.work_group_alloca ptr @0\n' "$i"
        printf '    store nonatomic %%p%d, %%p%d @0\n' "$((i - 1))" "$i"
    done
    printf '    ret %%p%d @0\n  }\n}\n\nlocs {\n  @0 = unknown\n}\n' "$n"
} >"$tmp/chain.fir"
{
    printf '{"kind":"return","values":["ptr(%d, 0)"],"trace":[],"escaped":[],"memory":[' "$((n + 1))"
    for i in $(seq "$((n + 1))" -1 2); do
        printf '{"memory":0,"alloc":%d,"kind":"global","align":8,"size":8,"live":true,"units":[' "$i"
        for k in 0 1 2 3 4 5 6; do printf '"frag(0, ptr(%d, 0), %d)",' "$((i - 1))" "$k"; done
        printf '"frag(0, ptr(%d, 0), 7)"]},' "$((i - 1))"
    done
    printf '{"memory":0,"alloc":1,"kind":"global","align":8,"size":8,"live":true,"units":['
    printf '"poison","poison","poison","poison","poison","poison","poison","poison"]}],"choices":0}'
} >"$tmp/chain.want"
# shellcheck disable=SC2086
(ulimit -c 0 && LEAN_STACK_SIZE_KB=256 runs 0 "$(<"$tmp/chain.want")" $w "$tmp/chain.fir" @dev::@chain) ||
    status=1
# A work-group allocation of 100,000 units is reported with no stack per
# unit, on a 256 KiB stack. It follows @wide's own allocation.
{
    printf 'module @dev() {\n  dialects gpu\n\n  func @wide() -> ptr {\n  ^e:\n'
    printf '    %%p: ptr = gpu.work_group_alloca i8 100000 @0\n    ret %%p @0\n  }\n}\n'
    printf '\nlocs {\n  @0 = unknown\n}\n'
} >"$tmp/wide.fir"
units=$(printf '"poison",%.0s' $(seq 100000))
wide='{"kind":"return","values":["ptr(1, 0)"],"trace":[],"escaped":[],"memory":[{"memory":0,"alloc":1,"kind":"global","align":1,"size":100000,"live":true,"units":['"${units%,}"']}],"choices":0}'
# shellcheck disable=SC2086
(ulimit -c 0 && LEAN_STACK_SIZE_KB=256 runs 0 "$wide" $w "$tmp/wide.fir" @dev::@wide) || status=1
exit "$status"
