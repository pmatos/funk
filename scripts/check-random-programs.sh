#!/usr/bin/env bash
# Runs generated programs on fir-ref and as native code (#165,
# ADR-2026-11-08-2115), and has fir-ref fmt read random texts. The hook
# fir-random calls it on every pull request, and the manual-stage hook
# fir-random-nightly with --fresh (ADR-2026-11-08-2116).
#
# Usage: scripts/check-random-programs.sh [--fresh COUNT | SEED...]
#   (nothing)      seeds 0 to 499, and those of
#                  scripts/harness/regression_seeds.txt
#   --fresh COUNT  COUNT programs from a new first seed, which it prints
#   SEED...        replays exactly these seeds, each a program and a text
set -euo pipefail

usage() {
    echo "Usage: $0 [--fresh COUNT | SEED...]" >&2
    exit 2
}

programs=500
fresh=
seeds=()
if [[ ${1-} == --fresh ]]; then
    [[ $# -eq 2 && $2 =~ ^[0-9]+$ ]] || usage
    fresh=$2
else
    for s in "$@"; do
        [[ $s =~ ^[0-9]+$ ]] || usage
    done
    seeds=("$@")
fi

repo_root=$(git -C "$(dirname "${BASH_SOURCE[0]}")/.." rev-parse --show-toplevel)
cd "$repo_root"

# shellcheck source=scripts/rust-env.sh
source scripts/rust-env.sh
if ! python3 -c 'import sys; sys.exit(sys.version_info < (3, 11))'; then
    echo "The harness needs Python 3.11 or later, for tomllib." >&2
    exit 1
fi

if [[ -n $fresh ]]; then
    first=$(python3 -c 'import secrets; print(secrets.randbelow(2**62))')
    count=$fresh
    extra=()
    echo "fresh seeds: $count programs from seed $first"
elif [[ ${#seeds[@]} -gt 0 ]]; then
    first=0
    count=0
    extra=("${seeds[@]}")
else
    first=0
    count=$programs
    seeds_file=scripts/harness/regression_seeds.txt
    if [[ ! -r $seeds_file ]]; then
        echo "$0: cannot read $seeds_file" >&2
        exit 1
    fi
    mapfile -t extra < <(grep -Ev '^(#|$)' "$seeds_file" || true)
fi

scripts/build-spec.sh --lean
cargo build --quiet --locked -p funk
target_dir=$(cargo metadata --format-version 1 --no-deps --locked |
    python3 -c 'import json, sys; print(json.load(sys.stdin)["target_directory"])')

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
cargo run --quiet --locked -p funk-ir --example fir_programs -- \
    "$tmp" "$first" "$count" "${extra[@]}"

status=0
check=(python3 scripts/harness/programs.py --funk "$target_dir/debug/funk"
    --fir-ref "$repo_root/lean/.lake/build/bin/fir-ref"
    --programs "$tmp/programs" --texts "$tmp/texts")
"${check[@]}" | tee "$tmp/out" || status=$?
if [[ -n "${GITHUB_STEP_SUMMARY:-}" ]]; then
    read -r checks passed failed invalid < <(sed -nE \
        's/^([0-9]+) checks: ([0-9]+) passed, ([0-9]+) failed, ([0-9]+) invalid$/\1 \2 \3 \4/p' \
        "$tmp/out" | tail -1) || true
    python3 -I scripts/suite_summary.py counts "Generated programs" \
        "checks=${checks:-0}" "passed=${passed:-0}" "failed=${failed:-0}" "invalid=${invalid:-0}" ||
        status=$((status ? status : 1))
fi
exit "$status"
