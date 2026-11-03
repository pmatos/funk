#!/usr/bin/env bash
# Runs Verus on every crate of the workspace that opts in with
# `[package.metadata.verus] verify = true`, and fails when a proof fails
# (ADR-2026-11-03-0808, ADR-2026-11-03-0809). The verus-proof pre-commit
# hook calls it, locally and in CI.
set -euo pipefail

if [[ $# -ne 0 ]]; then
    echo "Usage: $0" >&2
    exit 2
fi

cd "$(git -C "$(dirname "${BASH_SOURCE[0]}")/.." rev-parse --show-toplevel)"

# shellcheck source=scripts/rust-env.sh
source scripts/rust-env.sh

# The Verus release that checks the proofs. CI installs the same one; change
# both, and vstd's version in crates/funk-start-fds/Cargo.toml, together.
pinned=0.2026.11.02.8bf68ee

for tool in verus cargo-verus; do
    if ! command -v "$tool" >/dev/null; then
        echo "$tool is not on PATH. Unzip Verus $pinned from" >&2
        echo "https://github.com/verus-lang/verus/releases and put its directory on PATH." >&2
        exit 1
    fi
done

about=$(verus --version)
version=$(sed -n 's/^ *Version: *//p' <<<"$about")
if [[ "$version" != "$pinned" ]]; then
    echo "verus on PATH is ${version:-unknown}, not $pinned as $0 pins." >&2
    exit 1
fi
# Verus runs on one Rust toolchain; it must be the one that the workspace pins.
toolchain=$(sed -n 's/^ *Toolchain: *\([^ ]*\).*/\1/p' <<<"$about")
rust=$(sed -n 's/^channel = "\(.*\)"$/\1/p' rust-toolchain.toml)
if [[ "$toolchain" != "$rust"-* ]]; then
    echo "Verus $pinned runs on Rust ${toolchain:-unknown}, but rust-toolchain.toml pins $rust." >&2
    echo "Pin a Verus release that runs on Rust $rust, or move both pins together." >&2
    exit 1
fi

# Its own target directory, so that the wrapper's builds do not churn the
# ones that the other hooks share. --check-toolchain fails when vstd's
# version is not the one that this Verus release ships.
exec cargo verus verify --workspace --locked --check-toolchain --target-dir target/verus
