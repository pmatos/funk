#!/usr/bin/env bash
# Build fir's Lean package and render the spec document (ADR-2026-10-29-2135).
# Usage: scripts/build-spec.sh [--update] [OUTPUT_DIR]
#        scripts/build-spec.sh --lean
# The rendered HTML goes to OUTPUT_DIR, by default docs/spec/_out. Every page
# names the commit it was built from (ADR-2026-10-30-1046).
# --update first runs `lake update` in docs/spec/, under the same guards, for
# a toolchain bump. Never run a bare `lake update` there.
# --lean builds only the Lean package in lean/: the spec's definitions, the
# fir-ref executable and the Lean tests, without the document
# (ADR-2026-10-30-1250).
set -euo pipefail

update=false
lean_only=false
if [[ "${1:-}" == --update ]]; then
    update=true
    shift
elif [[ "${1:-}" == --lean ]]; then
    lean_only=true
    shift
fi
if [[ $# -gt 1 || "${1:-}" == -* || ( "$lean_only" == true && $# -gt 0 ) ]]; then
    echo "Usage: $0 [--update] [OUTPUT_DIR]" >&2
    echo "       $0 --lean" >&2
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

# For the firspec executable. Changes not yet committed, untracked files
# included, mark the build -dirty. No optional locks: a hook runs while git
# holds the index.
commit=$(git -C "$repo_root" rev-parse HEAD)
export FIRSPEC_COMMIT=${commit:0:12}
if [[ -n "$(git --no-optional-locks -C "$repo_root" status --porcelain)" ]]; then
    FIRSPEC_COMMIT+=-dirty
fi
if [[ -n "${GITHUB_SERVER_URL:-}" && -n "${GITHUB_REPOSITORY:-}" ]]; then
    export FIRSPEC_COMMIT_URL="$GITHUB_SERVER_URL/$GITHUB_REPOSITORY/commit/$commit"
fi

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

if [[ "$update" == true ]]; then
    (cd "$repo_root/docs/spec" && lake update)
fi

cd "$repo_root/lean"
lake build
if [[ "$lean_only" == true ]]; then
    exit 0
fi

cd "$repo_root/docs/spec"
lake build
lake exe firspec --output "$out"
echo "Rendered the spec to $out/html-multi/index.html"
