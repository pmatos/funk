#!/usr/bin/env bash
# Fuzzes the Rust parser and verifier (#165, ADR-2026-11-08-2117), then has
# fir-ref fmt read every input the fuzzer kept. The manual-stage hook
# fir-fuzz calls it, in the nightly workflow.
#
# Usage: scripts/check-fuzz.sh [SECONDS]
#   SECONDS  how long to fuzz each target (default 600)
#
# It needs cargo-fuzz and the nightly toolchain below. A crash leaves its
# input in fuzz/artifacts/TARGET/. Fix the bug, then keep the input with
# scripts/harness/fuzz_to_corpus.py.
set -euo pipefail

toolchain=nightly-2026-10-01
seconds=${1:-600}
if [[ $# -gt 1 || ! $seconds =~ ^[0-9]+$ ]]; then
    echo "Usage: $0 [SECONDS]" >&2
    exit 2
fi

repo_root=$(git -C "$(dirname "${BASH_SOURCE[0]}")/.." rev-parse --show-toplevel)
cd "$repo_root"

# shellcheck source=scripts/rust-env.sh
source scripts/rust-env.sh
if ! python3 -c 'import sys; sys.exit(sys.version_info < (3, 11))'; then
    echo "The harness needs Python 3.11 or later, for tomllib." >&2
    exit 1
fi
if ! cargo "+$toolchain" fuzz --version >/dev/null; then
    echo "check-fuzz: needs cargo-fuzz and the toolchain $toolchain" >&2
    exit 1
fi
scripts/build-spec.sh --lean

status=0
texts=()
for target in parse verify; do
    mkdir -p "fuzz/corpus/$target"
    # New inputs go to the first directory; the corpus's modules only seed
    # the run, so that it starts from texts that parse.
    cargo "+$toolchain" fuzz run --sanitizer none "$target" "fuzz/corpus/$target" \
        tests/fir/canonical -- "-max_total_time=$seconds" || status=$?
    texts+=(--texts "fuzz/corpus/$target")
done
python3 scripts/harness/programs.py --fir-ref "$repo_root/lean/.lake/build/bin/fir-ref" \
    "${texts[@]}" || status=$?
exit "$status"
