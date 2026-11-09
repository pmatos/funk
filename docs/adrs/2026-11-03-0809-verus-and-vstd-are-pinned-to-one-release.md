# Verus is pinned to one release, and vstd to the version it ships

Status: accepted; refined by ADR-2026-11-05-1408, ADR-2026-11-05-1954 and ADR-2026-11-09-1540

## Context

ADR-2026-11-03-0808 makes Verus prove the workspace's unsafe code in a
pre-commit hook, and so in CI. Verus ships weekly, as a zip per platform on
[GitHub](https://github.com/verus-lang/verus/releases). Each release runs
on one Rust toolchain. `cargo verus`, its Cargo front end, verifies a crate
that depends on `vstd`, Verus's standard library, from crates.io, at the
version that the release ships. vstd's `verus!` macro keeps the proof when
Verus checks the crate and erases it when cargo builds it, so the code that
ships is the code that Verus proves.

ADR-2026-10-30-1030 pins Rust 1.99.1, has no third-party crates yet, and
asks the PR that adds the first one to add the `cargo` ecosystem to
Dependabot.

Facts, checked on 2026-11-03: the latest Verus release is
0.2026.11.02.8bf68ee. It runs on Rust 1.99.1, funk's pin, and ships vstd
0.0.0-2026-11-01-0251.

## Decision

- **One Verus release**, 0.2026.11.02.8bf68ee. `scripts/check-verus.sh`
  pins it. It fails when `verus` on `PATH` is another release, or runs on
  another Rust than `rust-toolchain.toml` pins, and it runs the
  `cargo-verus` that sits beside that `verus`. It is the first release
  with verus-lang/verus#3362, which rejects `link_section`, `no_mangle` and
  `export_name` inside `verus!`, and #3350, which shrinks the x86-64 Linux
  zip from 487 MB to 36 MB; the release before it, 0.2026.10.26.d17fbd0,
  also runs on Rust 1.99.1 but has neither. It is a day old, so it does
  not wait out the week that Dependabot's cooldown gives a release: the
  Verus project's CI built it from upstream `main`, and the workflow pins
  its SHA-256, so it cannot change under us.
- **CI installs it**: the `pre-commit` job downloads
  `verus-0.2026.11.02.8bf68ee-x86-linux.zip`, checks it against the SHA-256
  written in the workflow, and puts it on `PATH`. AGENTS.md lists Verus as a
  prerequisite, and `scripts/ensure-hooks.sh` warns when it is missing.
- **The `verus-proof` hook** runs `cargo verus verify --workspace --locked
  --check-toolchain`, in its own target directory, `target/verus`. It
  verifies every crate that opts in, and vstd. `--check-toolchain` fails
  when vstd's version is not the release's. It cleans each crate that opts
  in first, so that Verus verifies it again and reports, as JSON, what it
  verified; `scripts/verus_report.py` reads that, and the hook fails
  unless Verus proved each function that it names. It runs when a file
  under `crates/`, a Cargo file, the Rust pin or one of its scripts
  changes.
- **vstd `=0.0.0-2026-11-01-0251`**, from crates.io, is a dependency of
  `funk-start-fds` only. `Cargo.lock` pins what it brings, all from
  crates.io: `verus_builtin`, `verus_builtin_macros`,
  `verus_state_machines_macros`, `verus_syn` and `verus_prettyplease`,
  which the Verus project publishes with vstd's version, and `syn`,
  `quote`, `proc-macro2`, `unicode-ident`, `synstructure`, `convert_case`,
  `indexmap`, `hashbrown` and `equivalent`. vstd and `verus_builtin` are
  normal dependencies, linked into funk: about 2 KB of generic code that
  vstd instantiates, such as drop glue, ends up in the binary.
  `verus_builtin_macros` and `verus_state_machines_macros` are proc
  macros, and the other 11 crates are libraries that only they use, at
  build time. Four have build scripts: vstd's sets `RUST_MIN_STACK`,
  `proc-macro2`'s and `quote`'s probe rustc, and `verus_prettyplease`'s
  sets cfgs.
- **A bump is one PR.** It moves the release and its SHA-256 in the
  workflow, the pin in `scripts/check-verus.sh` and vstd's version together,
  and the Rust pin when the new release runs on another toolchain.
- **Dependabot watches the `cargo` ecosystem**, as ADR-2026-10-30-1030
  asks, but ignores vstd and the `verus_*` crates: they move only with the
  Verus pin. vstd is the only direct dependency, so the entry yields
  security updates for the other nine crates and no version updates. An
  advisory against vstd or a `verus_*` crate needs a bump by hand.

This refines ADR-2026-10-30-1030 with the workspace's first third-party
crates.

## Alternatives

- **The `verus` binary on the crate's source, with no dependency.** cargo
  would then need the proof hidden behind `cfg(verus_keep_ghost)`, which
  Verus's guide warns can hide code from the proof.
- **Verus's rolling release**: it changes every day.
- **Building Verus from source in CI**: slower, for the same code.

## Consequences

- Every build of funk compiles vstd and its proc-macro crates once.
  funk's behaviour does not change.
- A clean CI run verifies vstd too, which takes about half a minute.
- A Rust bump waits for a Verus release on the new toolchain, and a Verus
  bump may bring a Rust bump.
