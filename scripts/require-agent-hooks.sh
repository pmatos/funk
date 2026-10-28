#!/usr/bin/env bash
# Claude PreToolUse: exit 2 blocks the tool when the worktree's hooks are not installed.
set -euo pipefail

repo_root=$(git rev-parse --show-toplevel) || exit 2
"$repo_root/scripts/ensure-hooks.sh" --check >/dev/null 2>&1 && exit 0

# Let through the setup commands that lift this gate.
command=$(jq -r '.tool_input.command // empty' 2>/dev/null) || command=
case "$command" in
    ./scripts/ensure-hooks.sh* | "$repo_root/scripts/ensure-hooks.sh"* | "uv tool install pre-commit"*)
        exit 0
        ;;
esac

echo "Blocked: this worktree's pre-commit and commit-msg hooks are not installed. Run ./scripts/ensure-hooks.sh (install pre-commit first with 'uv tool install pre-commit' if needed)." >&2
exit 2
