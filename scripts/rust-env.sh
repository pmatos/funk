# shellcheck shell=bash
# Sourced, from the repository root, by the scripts that run cargo:
# check-rust.sh and check-fir-ref.sh (ADR-2026-10-30-1030). It puts rustup's
# cargo on PATH and checks that cargo and rustc are the version that
# rust-toolchain.toml pins.

# The pin, not the environment, picks the toolchain, so a local pass predicts
# a CI pass.
unset RUSTUP_TOOLCHAIN

if ! command -v cargo >/dev/null; then
    if [[ -x "$HOME/.cargo/bin/cargo" ]]; then
        PATH="$HOME/.cargo/bin:$PATH"
    else
        echo "cargo is not installed. Install rustup as https://rustup.rs says." >&2
        exit 1
    fi
fi

pinned=$(sed -n 's/^channel = "\(.*\)"$/\1/p' rust-toolchain.toml)
for tool in cargo rustc; do
    version=$("$tool" --version | cut -d' ' -f2)
    if [[ "$version" != "$pinned" ]]; then
        echo "$tool on PATH is $version, not $pinned as rust-toolchain.toml pins." >&2
        echo "Put rustup's cargo and rustc first on PATH: they follow the pin." >&2
        exit 1
    fi
done
