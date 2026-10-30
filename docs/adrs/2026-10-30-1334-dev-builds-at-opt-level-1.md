# Dev builds, and so the tests, are compiled at opt-level 1

Status: accepted

## Context

The `rust-test` hook runs `cargo test --workspace --locked` on every commit
that touches Rust, locally and in CI, so the tests must stay fast
(ADR-2026-10-30-1030). The tests of ADR-2026-10-30-1333 walk texts nested
ten million levels deep.

Measured on 2026-10-30, on one machine: the whole suite took 177 s
unoptimized and 38 s at `opt-level = 1`. The attribute test alone took
24.5 s unoptimized, 5.9 s at `opt-level = 1` and 6.1 s in a release build.

`cargo test` compiles a workspace library that the integration tests link
with the `dev` profile, not the `test` profile, and generic code, such as a
`Hash` impl over a test's hasher, with the profile of the crate that uses
it.

## Decision

The root `Cargo.toml` sets `[profile.dev] opt-level = 1`. The `test` profile
inherits it. Debug assertions and overflow checks stay on: `opt-level` does
not change them. Release builds are unchanged.

## Alternatives

- **No optimization, shallower tests.** The tests would run far less deep
  than #36 asks, or take minutes on every commit.
- **`[profile.dev.package.funk-ir]` only.** Generic code that a test
  instantiates would still be compiled unoptimized, in the test.
- **`opt-level` 2 or 3.** No faster on these tests, slower to compile, and
  harder to debug.

## Consequences

- Dev builds compile a little slower, and a debugger steps through them
  less exactly.
- The existing tests run faster too: the unit tests of `funk-ir` went from
  3.7 s to 1.3 s.
