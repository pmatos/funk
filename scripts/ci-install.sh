#!/usr/bin/env bash
# Installs rustup, elan or Verus in a CI setup step (ADR-2026-11-05-1954).
# Usage: scripts/ci-install.sh rustup|elan|verus
# The step's env pins the installer: RUSTUP_VERSION and RUSTUP_SHA256,
# ELAN_VERSION and ELAN_SHA256, or VERUS_VERSION and VERUS_SHA256. The
# installer is downloaded to RUNNER_TEMP only when the step before restored
# no copy from the cache, and its SHA-256 is checked in either case, before
# it is used, so a bad cached file fails the step. The tool's directory is
# appended to GITHUB_PATH.
set -euo pipefail

# Downloads URL to FILE unless FILE exists, then checks FILE against SHA256.
# A download retries 5 times, 10 s apart, on any error (#151).
fetch() {
    local file=$1 sha256=$2 url=$3
    if [[ -f $file ]]; then
        echo "$file: restored from the cache, not downloaded"
    else
        echo "$file: not in the cache, downloading $url"
        curl -sSfL --retry 5 --retry-delay 10 --retry-all-errors -o "$file" "$url"
    fi
    echo "$sha256  $file" | sha256sum -c -
}

case "${1-}" in
    rustup)
        fetch "$RUNNER_TEMP/rustup-init" "$RUSTUP_SHA256" \
            "https://static.rust-lang.org/rustup/archive/$RUSTUP_VERSION/x86_64-unknown-linux-gnu/rustup-init"
        chmod +x "$RUNNER_TEMP/rustup-init"
        "$RUNNER_TEMP/rustup-init" -y --no-modify-path --profile minimal --default-toolchain none
        echo "$HOME/.cargo/bin" >>"$GITHUB_PATH"
        ;;
    elan)
        fetch "$RUNNER_TEMP/elan.tar.gz" "$ELAN_SHA256" \
            "https://github.com/leanprover/elan/releases/download/$ELAN_VERSION/elan-x86_64-unknown-linux-gnu.tar.gz"
        tar -xzf "$RUNNER_TEMP/elan.tar.gz" -C "$RUNNER_TEMP"
        "$RUNNER_TEMP/elan-init" -y --no-modify-path --default-toolchain none
        echo "$HOME/.elan/bin" >>"$GITHUB_PATH"
        ;;
    verus)
        fetch "$RUNNER_TEMP/verus.zip" "$VERUS_SHA256" \
            "https://github.com/verus-lang/verus/releases/download/release/$VERUS_VERSION/verus-$VERUS_VERSION-x86-linux.zip"
        unzip -q "$RUNNER_TEMP/verus.zip" -d "$RUNNER_TEMP/verus"
        "$RUNNER_TEMP/verus/verus-x86-linux/verus" --version
        echo "$RUNNER_TEMP/verus/verus-x86-linux" >>"$GITHUB_PATH"
        ;;
    *)
        echo "Usage: $0 rustup|elan|verus" >&2
        exit 2
        ;;
esac
