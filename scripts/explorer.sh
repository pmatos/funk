#!/usr/bin/env bash
# Builds funk and fir-ref and starts the fir explorer on this machine
# (ADR-2026-11-08-1806). Usage: scripts/explorer.sh [--no-build] [--port N]
# [--timeout SECONDS]. --no-build uses the tools already built.
set -euo pipefail

repo_root=$(git -C "$(dirname "${BASH_SOURCE[0]}")/.." rev-parse --show-toplevel)
cd "$repo_root"

# It unsets CI tokens too: the explorer runs what is typed into it.
# shellcheck source=scripts/rust-env.sh
source scripts/rust-env.sh
if ! python3 -c 'import sys; sys.exit(sys.version_info < (3, 11))'; then
    echo "The explorer needs Python 3.11 or later, for tomllib." >&2
    exit 1
fi

if [[ "${1:-}" == --no-build ]]; then
    shift
else
    scripts/build-spec.sh --lean
    cargo build --quiet --locked -p funk
fi
target_dir=$(cargo metadata --format-version 1 --no-deps --locked |
    python3 -c 'import json, sys; print(json.load(sys.stdin)["target_directory"])')

PYTHONPATH=scripts/harness exec python3 -m explorer \
    --funk "$target_dir/debug/funk" \
    --fir-ref "$repo_root/lean/.lake/build/bin/fir-ref" "$@"
