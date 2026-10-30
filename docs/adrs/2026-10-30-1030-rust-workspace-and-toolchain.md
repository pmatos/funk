# funk's Rust code is one Cargo workspace on a pinned stable toolchain, checked by pre-commit hooks

Status: accepted

## Context

[#9](https://github.com/pmatos/funk/issues/9) adds the first Rust code: the
`funk-ir` library and the `funk` driver. The roadmap makes the whole
toolchain Rust, and later tickets add a backend and a differential harness.
`AGENTS.md` puts every check in `.pre-commit-config.yaml`, which CI runs on
every file, and limits every text file to 20,000 bytes
(ADR-2026-10-28-0724).

Facts, checked on 2026-10-30: the latest stable Rust is 1.99.1, released on
2026-10-15. The latest rustup is 1.29.2. Rust's release server publishes a
SHA-256 for each `rustup-init`.

## Decision

- **One virtual workspace.** The root `Cargo.toml` lists the crates, all
  under `crates/`: `crates/funk-ir`, the library (IR, op registry, builder,
  parser, printer, verifier and module generator), and `crates/funk`, the
  binary `funk`. Later crates, such as a backend, go under `crates/` too.
  Edition 2024, resolver 3. Shared package fields and lints live in
  `[workspace.package]` and `[workspace.lints]`; `unsafe_code` is forbidden.
  `Cargo.lock` is committed.
- **Shared fir texts live outside the crates**, in `tests/fir/`, so that the
  Lean side (#10) and the harness (#13) read the same files.
- **`funk-ir` has a module per layer**: `ir`, `registry`, `dialects`, `text`,
  `verify` and `generate`. Each op family of the core dialect has its own
  file in `dialects/core/` (ADR-2026-10-30-1146).
- **No third-party crates yet.** JSON output, argument parsing, the big
  integers that check constants and the generator's random numbers are small
  modules of their own. The PR that adds the first dependency also adds the
  `cargo` ecosystem to `.github/dependabot.yml`.
- **One pin.** `rust-toolchain.toml` pins an exact stable release, now
  `1.99.1`, with the `minimal` profile and the `rustfmt` and `clippy`
  components. `rust-version` in the workspace is the pin's minor release,
  `1.99`. No nightly and no floating `stable`. A bump is one PR that changes
  the pin, fixes what the new lints find, and passes every check.
- **Three hooks run the checks**, as default-stage hooks in
  `.pre-commit-config.yaml`: `rust-fmt` (`cargo fmt --all --check`),
  `rust-clippy` (`cargo clippy --workspace --all-targets --locked -- -D
  warnings`) and `rust-test` (`cargo test --workspace --locked`). Each calls
  `scripts/check-rust.sh` as an `unsupported_script`, like `fir-spec`. They
  run when a file under `crates/`, a Cargo file, the pin or the script
  changes, and on every CI run; `rust-test` also runs when a file under
  `tests/fir/` changes. The script ignores `RUSTUP_TOOLCHAIN` and fails when
  the cargo or rustc on `PATH` is not the pinned release. rustfmt uses its
  default style.
- **CI installs the pinned toolchain.** The `pre-commit` job downloads
  `rustup-init` 1.29.2 and checks it against the SHA-256 written in the
  workflow, installs rustup with no default toolchain, then runs `rustup
  toolchain install`, which installs what `rust-toolchain.toml` names. It
  caches `~/.rustup/toolchains`, keyed on `rust-toolchain.toml`, except the
  `stable-*` toolchain that the runner image ships.
- **Setup checks for cargo.** `scripts/ensure-hooks.sh` warns when cargo is
  neither on `PATH` nor in `~/.cargo/bin`, as it does for elan.

## Alternatives

- **A floating `stable` channel.** A new release's lints could turn CI red
  with no change in the repository.
- **`dtolnay/rust-toolchain` or another action.** A checksummed
  `rustup-init` needs no third-party action, as for elan
  (ADR-2026-10-29-2135).
- **`proptest`, `serde_json` and `clap`.** Convenient, but the tracer needs
  little of each, and every dependency brings supply-chain risk and
  lockfile churn.

## Consequences

- Builds are reproducible: one file pins the toolchain, and the lockfile pins
  every crate.
- A cold CI run downloads the toolchain once; later runs restore it.
- Every commit that touches Rust runs the whole test suite, so the tests must
  stay fast: the property tests run in about a second.
