#!/usr/bin/env bash
# Guards the speed of the Rust toolchain against regressions
# (ADR-2026-11-09-1645). The pre-commit hook rust-speed calls it, locally and
# in CI. It builds the release funk, generates large inputs into a temporary
# directory, counts the instructions that funk fmt --check, verify and build
# run on each one under cachegrind, and compares them with
# scripts/rust-speed-baseline.json through scripts/rust_speed.py. Instruction
# counts do not depend on the host's load. Children are not traced, so as and
# ld are not counted.
set -euo pipefail

if [[ $# -ne 0 ]]; then
    echo "Usage: $0" >&2
    exit 2
fi

repo_root=$(git -C "$(dirname "${BASH_SOURCE[0]}")/.." rev-parse --show-toplevel)
cd "$repo_root"

# shellcheck source=scripts/rust-env.sh
source scripts/rust-env.sh

if ! command -v valgrind >/dev/null; then
    echo "valgrind is not installed. Install it from your distribution." >&2
    exit 1
fi

rust_speed=(python3 -I "$repo_root/scripts/rust_speed.py")
sizes=$("${rust_speed[@]}" sizes)
read -r adds blocks <<<"$sizes"

cargo build --quiet --release --locked -p funk
target_dir=$(cargo metadata --format-version 1 --no-deps --locked |
    python3 -c 'import json, sys; print(json.load(sys.stdin)["target_directory"])')
funk=$target_dir/release/funk

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
cd "$tmp"

ending='}\n\nlocs {\n  @0 = unknown\n}\n'
awk -v n="$adds" -v end="$ending" 'BEGIN {
    printf "func @f(%%a: i32) -> i32 {\n^e:\n  %%v0: i32 = add %%a, %%a @0\n"
    for (i = 1; i < n; i++) printf "  %%v%d: i32 = add %%v%d, %%a @0\n", i, i - 1
    printf "  ret %%v%d @0\n%s", n - 1, end
}' >adds.fir
awk -v n="$blocks" -v end="$ending" 'BEGIN {
    printf "func @f(%%a: i32) -> i32 {\n^b0:\n  br ^b1(%%a) @0\n"
    for (i = 1; i < n - 1; i++) printf "^b%d(%%x%d: i32):\n  br ^b%d(%%x%d) @0\n", i, i, i + 1, i
    printf "^b%d(%%x%d: i32):\n  ret %%x%d @0\n%s", n - 1, n - 1, n - 1, end
}' >blocks.fir

measure() {
    local input=$1 name=$2
    shift 2
    if ! valgrind --tool=cachegrind --cache-sim=no \
        --cachegrind-out-file="$input-$name.cg" --log-file="$input-$name.vg" \
        "$funk" "$@" >"$input-$name.out" 2>&1; then
        echo "funk $name failed on the $input input, so its count means nothing:" >&2
        cat "$input-$name.out" "$input-$name.vg" >&2
        exit 1
    fi
    local count
    count=$(sed -n 's/^==[0-9]*== I[[:space:]]*refs:[[:space:]]*//p' "$input-$name.vg" | tr -d ,)
    if ! [[ $count =~ ^[0-9]+$ ]]; then
        echo "No instruction count in cachegrind's output for funk $name on $input:" >&2
        cat "$input-$name.vg" >&2
        exit 1
    fi
    echo "$input $name $count" >>counts
}

for input in adds blocks; do
    measure "$input" fmt fmt --check "$input.fir"
    measure "$input" verify verify "$input.fir"
    measure "$input" build build -o "$input.bin" "$input.fir"
done

echo "This host: $(getconf GNU_LIBC_VERSION 2>/dev/null || echo 'glibc unknown'), $(valgrind --version)."
mode=()
if [[ -z "${GITHUB_ACTIONS:-}" ]]; then
    mode=(--advisory)
fi
status=0
"${rust_speed[@]}" compare "${mode[@]}" <counts || status=$?
if [[ -n "${GITHUB_STEP_SUMMARY:-}" ]]; then
    mapfile -t rows < <(awk '{ print $1 "_" $2 "=" $3 }' counts)
    python3 -I "$repo_root/scripts/suite_summary.py" counts "funk's instruction counts" \
        "${rows[@]}" || status=$((status ? status : 1))
fi
exit "$status"
