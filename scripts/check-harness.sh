#!/usr/bin/env bash
# Runs the differential harness over tests/fir/ (#13, ADR-2026-10-30-2049):
# the one command for the whole corpus. The pre-commit hook fir-harness
# calls it, locally and in CI. It builds fir-ref (build-spec.sh --lean) and
# funk, has funk-ir's generator print its modules, and runs
# scripts/harness/main.py, which checks that funk verify and fir-ref validate
# give every text the same verdict, and runs every test of the corpus on
# fir-ref and as native code. Then scripts/harness/check_invalid.py runs the
# harness on the fixture corpus of scripts/harness/fixtures/invalid/ and
# checks that it reports #18's frozen divisor invalid (ADR-2026-10-31-0208).
set -euo pipefail

if [[ $# -ne 0 ]]; then
    echo "Usage: $0" >&2
    exit 2
fi

repo_root=$(git -C "$(dirname "${BASH_SOURCE[0]}")/.." rev-parse --show-toplevel)
cd "$repo_root"

# fir-ref, cargo and native code run code from this repository; keep CI
# tokens away.
unset GH_TOKEN GITHUB_TOKEN

# Before the Lean build, so that a missing cargo or Python fails at once.
# shellcheck source=scripts/rust-env.sh
source scripts/rust-env.sh
if ! python3 -c 'import sys; sys.exit(sys.version_info < (3, 11))'; then
    echo "The harness needs Python 3.11 or later, for tomllib." >&2
    exit 1
fi

# The only way to run Lake here: under the guards of ADR-2026-10-29-2135.
scripts/build-spec.sh --lean
cargo build --quiet --locked -p funk
target_dir=$(cargo metadata --format-version 1 --no-deps --locked |
    python3 -c 'import json, sys; print(json.load(sys.stdin)["target_directory"])')

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
cargo run --quiet --locked -p funk-ir --example fir_texts -- "$tmp/generated"

status=0
python3 scripts/harness/main.py --funk "$target_dir/debug/funk" \
    --fir-ref "$repo_root/lean/.lake/build/bin/fir-ref" \
    --generated "$tmp/generated" tests/fir || status=$?
invalid=0
python3 scripts/harness/check_invalid.py --funk "$target_dir/debug/funk" \
    --fir-ref "$repo_root/lean/.lake/build/bin/fir-ref" || invalid=$?
if [[ $status -eq 0 ]]; then
    status=$invalid
fi
exit "$status"
