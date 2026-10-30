# The Lean build in lean/ fails on any warning

Status: accepted

## Context

The axiom check of ADR-2026-10-30-1452 fails the build on any declaration in
`lean/` that rests on `sorry` or another untrusted axiom. Lean does not keep
an `example`, so the check never sees one. A `sorry` inside an `example` was
therefore not caught. Lean reports it as a warning, and plain `lake build`
prints warnings without failing.

`lean/` has no dependencies (ADR-2026-10-29-2135), so every warning in its
build comes from our own code. `docs/spec/` depends on Verso, whose build can
warn about code that we do not own.

The human ruled on this in [#52](https://github.com/pmatos/funk/issues/52)
on 2026-10-30.

## Decision

- [`scripts/build-spec.sh`](../../scripts/build-spec.sh) builds `lean/` with
  `lake build --wfail`. Any warning in `lean/` fails the build. The
  `fir-spec`, `fir-ref-test` and `fir-round-trip` hooks build `lean/` through
  that script, so each of them fails too.
- The build in `docs/spec/` stays a plain `lake build`.

## Consequences

- A `sorry` anywhere in `lean/`, in an `example` too, fails the build.
- Warnings that have nothing to do with soundness fail it as well, such as an
  unused variable, a deprecated name or a linter's report. They are fixed
  before a change lands.
- A toolchain bump that deprecates a name used in `lean/` fixes those uses in
  the same PR.
- Lean gives no warning for native evaluation (`native_decide`,
  `decide +native`, `bv_decide`). ADR-2026-10-30-1838 allows it anywhere, an
  `example` included, so nothing more is needed for examples.
