# funk's Rust code is one Cargo workspace on a pinned stable toolchain, checked by pre-commit hooks

Status: accepted; refined by ADR-2026-11-05-1408
Tier: direction; area: rust-ir-and-tools

## Decision

- **One virtual workspace.** The root `Cargo.toml` lists the crates, all
  under `crates/`. Edition 2024, resolver 3. Shared package fields and
  lints live in `[workspace.package]` and `[workspace.lints]`;
  `unsafe_code` is forbidden. `Cargo.lock` is committed.
- **Shared fir texts live outside the crates**, in `tests/fir/`, so that
  the Lean side and the harness read the same files.
- **No third-party crates.** JSON output, argument parsing, big integers
  and the generator's random numbers are small modules of funk's own.
  Dependabot watches the `cargo` ecosystem for the first one.
- **One pin.** `rust-toolchain.toml` pins an exact stable release, with the
  `minimal` profile and the `rustfmt` and `clippy` components.
  `rust-version` in the workspace is the pin's minor release. No nightly
  and no floating `stable`. A bump is one PR that changes the pin, fixes
  what the new lints find, and passes every check.
- **Three hooks run the checks**, in `.pre-commit-config.yaml`:
  `rust-fmt`, `rust-clippy` with `-D warnings`, and `rust-test`. Each calls
  `scripts/check-rust.sh`, which fails when the cargo or rustc on `PATH` is
  not the pinned release. Every commit that touches Rust runs the whole
  test suite, so the tests stay fast.
- **CI installs the pinned toolchain** in the `rust` job, one of the suite
  jobs behind the `pre-commit` gate (ADR-2026-11-05-1408).
  `scripts/ci-install.sh` installs rustup from a `rustup-init` checked
  against the SHA-256 written in the workflow
  ([process-ci.md](../decisions/process-ci.md#installer-downloads)), then
  `rustup toolchain install` installs what `rust-toolchain.toml` names.
  `scripts/ensure-hooks.sh` warns when cargo is missing.

[rust-ir-and-tools.md](../decisions/rust-ir-and-tools.md#workspace-and-toolchain)
gives the hooks' commands and files and the caches.

## Why

The roadmap makes the whole toolchain Rust, with a backend and a
differential harness to come, so one workspace keeps every crate on one
toolchain and one lockfile. One file pins the toolchain and the lockfile
pins every crate, so builds are reproducible. AGENTS.md puts every check in
`.pre-commit-config.yaml`, so the Rust checks are hooks like any other.

## Rejected alternatives

- **A floating `stable` channel.** A new release's lints could turn CI red
  with no change in the repository.
- **`dtolnay/rust-toolchain` or another action.** A checksummed
  `rustup-init` needs no third-party action.
- **`proptest`, `serde_json` and `clap`.** Convenient, but funk needs little
  of each, and every dependency brings supply-chain risk and lockfile churn.
