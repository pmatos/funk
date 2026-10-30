#!/usr/bin/env bash
# Build fir's Lean package and render the spec document (ADR-2026-10-29-2135).
# Usage: scripts/build-spec.sh [OUTPUT_DIR]
# The rendered HTML goes to OUTPUT_DIR, by default docs/spec/_out.
set -euo pipefail

if [[ $# -gt 1 ]]; then
    echo "Usage: $0 [OUTPUT_DIR]" >&2
    exit 2
fi

# Git runs hooks with GIT_DIR, GIT_INDEX_FILE and similar variables set to
# this repository. Lake runs git inside its package clones, and with those
# variables set its git commands would act on this repository instead.
for var in $(git rev-parse --local-env-vars); do
    unset "$var"
done

repo_root=$(git -C "$(dirname "${BASH_SOURCE[0]}")/.." rev-parse --show-toplevel)
out=$(realpath -m "${1:-$repo_root/docs/spec/_out}")

# Lake treats a package as cloned when its `.git` exists. If that `.git` is
# broken, git skips it and climbs to this repository. The ceiling stops git
# at the package directories, so Lake's git calls fail instead.
export GIT_CEILING_DIRECTORIES="$repo_root/lean/.lake/packages:$repo_root/docs/spec/.lake/packages"

# Lakefiles and elaboration run arbitrary code; keep CI tokens away from them.
unset GH_TOKEN GITHUB_TOKEN

# Verso's includeLiterate runs `elan run`, so elan must be on PATH.
if ! command -v elan >/dev/null && [[ -x "$HOME/.elan/bin/elan" ]]; then
    PATH="$HOME/.elan/bin:$PATH"
fi
if ! command -v elan >/dev/null; then
    echo "elan is not installed; see https://github.com/leanprover/elan" >&2
    exit 1
fi

cd "$repo_root/lean"
lake build

cd "$repo_root/docs/spec"
lake build
lake exe firspec --output "$out"
echo "Rendered the spec to $out/html-multi/index.html"
