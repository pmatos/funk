# A closed standard stream stays on /dev/null, and the Verus tooling waits at a tag

Status: accepted
Tier: direction; area: rust-ir-and-tools

## Context

ADR-2026-11-02-2253 added `funk-start-fds`, a start-up constructor, so
that funk exits with 2, as `fir-ref` does, when a standard stream is
closed at start-up. It was the workspace's only unsafe code, so
ADR-2026-11-03-0808 and ADR-2026-11-03-0809 gave it a Verus proof.
Guarding its 246 lines took about 2,150 lines of Python checkers, a Verus
release downloaded in CI, a `vstd` dependency and four hooks, and every
pull request paid for them.

The human ruled on 2026-11-09 (#168, option 2, comment 6736849889): drop
the crate and the tooling, keep the rule, and tag the tooling.

## Decision

- **A closed standard stream is `/dev/null`.** Before `main`, Rust's
  standard library opens `/dev/null` on each of descriptors 0 to 2 that is
  closed. funk does not look behind that:
  - it reads a closed standard input as an empty text, so `-` is a parse
    error with exit 1;
  - it writes a closed standard output to `/dev/null` and exits with its
    verdict;
  - it writes a closed standard error to `/dev/null` and exits with its
    verdict.
- **funk differs from `fir-ref` here.** `fir-ref` exits with 2 when it
  needs a closed stream. The harness never closes a standard stream, so it
  never compares them.
- **No exception to `forbid`.** `crates/funk-start-fds` is gone, and
  `unsafe_code = "forbid"` applies to the whole workspace again.
- **The tooling goes with it**: the `verus-proof`, `verus-report-test`,
  `unsafe-code` and `unsafe-code-test` hooks, their scripts, the Verus
  download in CI and the `vstd` dependency.
- **The rule stays.** Any unsafe Rust needs a Verus proof, as
  ADR-2026-11-03-0808 says. AGENTS.md states it.
- **The tag.** `verus-tooling-m0` marks commit `0f070ff`, on `main`, which
  still has the crate and the tooling. The first real unsafe code, likely
  the M6 JIT, restores the tooling from that tag instead of rebuilding it.

This supersedes ADR-2026-11-02-2253. It refines ADR-2026-11-03-0808: the
rule stands, and its verified module, trusted base, digests and hooks wait
at the tag. It refines ADR-2026-11-03-0809 too: the Verus and `vstd` pins
wait at the tag. It refines ADR-2026-11-03-0107: its "Closed at start"
item no longer holds, and its handling of a stream open in the wrong mode
does not change.

## Alternatives

- **Keep the crate and its proof**, option 1 of #168: every pull request
  keeps paying for 246 lines that only serve a case the harness never
  runs.
- **Keep the crate and park the tooling**, option 3 of #168: it breaks the
  ruling that unsafe Rust needs a proof.

## Consequences

- funk and `fir-ref` give different verdicts and exit codes on a closed
  standard stream. A caller that closes one gets no report of it from
  funk.
- The workspace depends on no third-party crates again, and a build no
  longer compiles `vstd`.
- Contributors and CI no longer need Verus.
- Restoring the tooling is work: its checkers name `funk-start-fds`, and
  its Verus pin must run on the Rust toolchain of that day.
