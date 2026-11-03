#!/usr/bin/env bash
# Runs Verus on every crate of the workspace that opts in with
# `[package.metadata.verus] verify = true`, and fails when a proof fails or
# when Verus did not verify each function of such a crate that
# scripts/verus_report.py names (ADR-2026-11-03-0808, ADR-2026-11-03-0809). The verus-proof pre-commit hook calls it, locally
# and in CI.
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
# Use the official release zip: a source build's cargo-verus lacks the vstd
# compatibility row for its own release and fails with "Components are
# incompatible".
pinned=0.2026.11.02.8bf68ee

if ! verus=$(command -v verus); then
    echo "verus is not on PATH. Unzip the official release zip of Verus $pinned from" >&2
    echo "https://github.com/verus-lang/verus/releases and put its directory on PATH." >&2
    exit 1
fi
# The release's own cargo-verus, not another one on PATH or in ~/.cargo/bin,
# found beside the real binary when `verus` on PATH is a symlink.
cargo_verus="$(dirname "$(readlink -f "$verus")")/cargo-verus"
if [[ ! -x "$cargo_verus" ]]; then
    echo "$cargo_verus is missing: reinstall Verus $pinned, whose zip holds it." >&2
    exit 1
fi

if ! about=$(verus --version); then
    echo "verus --version failed: reinstall Verus $pinned for this host." >&2
    exit 1
fi
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

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

cargo metadata --no-deps --format-version 1 --locked >"$work/metadata.json"
mapfile -t crates < <(python3 -I - "$work/metadata.json" <<'EOF'
import json, sys
for package in json.load(open(sys.argv[1]))["packages"]:
    if (package["metadata"] or {}).get("verus", {}).get("verify") is True:
        print(package["name"])
EOF
)

# Its own target directory, so that the wrapper's builds do not churn the
# ones that the other hooks share. Cleaning each crate that opts in makes
# Verus verify it again and report what it verified, in JSON on stdout.
# --check-toolchain fails when vstd's version is not the one that this
# Verus release ships.
for crate in "${crates[@]}"; do
    cargo clean --locked --quiet --target-dir target/verus -p "$crate"
done
if ! "$cargo_verus" verus verify --workspace --locked --check-toolchain \
    --target-dir target/verus -- --output-json >"$work/results.json" \
    2>"$work/verus.err"; then
    cat "$work/verus.err" >&2
    if grep -q "Components are incompatible" "$work/verus.err"; then
        echo "The verus-proof hook needs the official release zip of Verus $pinned," >&2
        echo "from https://github.com/verus-lang/verus/releases: a source build's" >&2
        echo "cargo-verus lacks the vstd compatibility row for its own release." >&2
    fi
    exit 1
fi
cat "$work/verus.err" >&2

# Each crate that opts in must have verified the functions that
# scripts/verus_report.py names: a cfg that hides a verified module from
# Verus, but not from cargo, leaves them out.
python3 -I scripts/verus_report.py "$work/results.json" "${crates[@]}"
