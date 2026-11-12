# The IR is completed in a milestone of its own, M1, before the full backend

Status: accepted
Tier: direction; area: process

## Decision

- **M1 is "Complete the fir IR".** It takes fir from M0's integer core to an
  IR that the frontends can lower to. Its scope is in `docs/roadmap.md`: the
  M0 close-out audit issues first, then memory (S3), effect classes (H7),
  globals and external functions (H3), floating point (S5), aggregates, and
  dialects and extensions (H4, H5) with a second dialect in tree. Each item
  goes through every layer at once, including a naive backend lowering so
  that the harness checks it natively.
- **The later milestones shift by one.** Old M1 to M6 are now M2 to M7: full
  x86-64 backend (M2), Vow frontend (M3), C and C++ frontend (M4), compile the
  Linux kernel (M5), JIT compilation (M6), x86 to arm64 binary translation
  (M7).
- **Earlier text keeps the old numbers.** Accepted ADRs, spike reports, issues
  and comments written before this ADR keep their wording; in them, M1 to M6
  mean today's M2 to M7. Living docs (`docs/roadmap.md`, `README.md`, the
  spec's prose) use the new numbers, and the roadmap carries a note on the old
  ones.
- **The epics follow.** #177 is the M1 epic, and the audit issues block it.
  #164 is the M2 epic, and #177 blocks it. The GitHub milestones are renamed
  to match.
- **Out of M1:** concurrency (S6), exceptions and unwinding, vectors, contract
  ops and structured control flow (H6) stay with the milestones that need
  them. S8 is M9, which runs after M2 (the human, 2026-11-12, in #341).

The human ruled on 2026-11-05: "before we have a full x86 backend, we will
need to have a complete IR spec. Getting the IR right is one of the most
important parts of this project."

## Why

Every backend, pass and frontend is built against the IR, so a late change to
it costs the most. The real backend then starts on a settled IR with memory
and floating point in it, and register allocation and instruction selection
are designed once, for the whole IR.

## Rejected alternatives

- **Grow the IR inside the backend milestone.** The old roadmap put S3 and H7
  at step 2 of six in the backend milestone, so the register allocator would
  have been built before fir had loads and stores, and the IR would have grown
  piecemeal on the backend's schedule.
