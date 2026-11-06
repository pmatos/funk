# The IR is completed in a milestone of its own, M1, before the full backend

Status: accepted

## Context

The roadmap had M0 build fir's integer core with a naive x86-64 backend,
and M1 grow that backend into a real one. Memory (S3), effect classes
(H7), floating point (S5), globals and external functions (H3), aggregates
and dialects (H4, H5) were all deferred past M0, and the roadmap put S3 and
H7 inside the backend milestone, as step 2 of six. So the backend's
register allocator would have been built before fir had loads and stores,
and the IR would have grown piecemeal under the backend's schedule.

On 2026-11-05 the human ruled that fir must be complete before the full
backend: "before we have a full x86 backend, we will need to have a
complete IR spec. Getting the IR right is one of the most important parts
of this project." Every backend, pass and frontend is built against the
IR, so a late change to it costs the most.

## Decision

- **M1 is now "Complete the fir IR".** It takes fir from M0's integer core
  to an IR that real programs and the frontends can lower to. Its scope is
  in `docs/roadmap.md`: the M0 close-out audit issues first, then memory
  (S3), effect classes (H7), globals and external functions (H3), floating
  point (S5), aggregates, and dialects and extensions (H4, H5) with a
  second dialect in tree. Each item goes through every layer at once, as
  M0's op families did, including a naive backend lowering so that the
  harness checks it natively.
- **The later milestones shift by one.** Old M1 to M6 are now M2 to M7:

  - old M1, full x86-64 backend, is M2;
  - old M2, Vow frontend, is M3;
  - old M3, C and C++ frontend, is M4;
  - old M4, compile the Linux kernel, is M5;
  - old M5, JIT compilation, is M6;
  - old M6, x86 to arm64 binary translation, is M7.

- **Earlier text is read with the old numbers.** Accepted ADRs, spike
  reports, issues and comments written before this ADR keep their
  wording. In them, M1 to M6 mean today's M2 to M7. Living docs
  (`docs/roadmap.md`, `README.md`, the spec's prose) use the new numbers.
- **The epics follow.** #177 is the M1 epic, and the audit issues block
  it. #164, filed as the M1 backend epic, is the M2 epic and is blocked by
  #177.
- **Out of M1:** concurrency (S6), exceptions and unwinding, vectors,
  contract ops and structured control flow (H6) stay with the milestones
  that need them. S8 stays with M2's optimizer track, which needs it first.

## Consequences

- The real backend starts on a settled IR with memory and floating point
  in it, so register allocation and instruction selection are designed
  once, for the whole IR.
- The frontends move one milestone later.
- An old ADR that says "M1" or "M3" needs the list above to read. The
  roadmap carries a note that says so.
- GitHub milestones are renamed to match, and a new milestone holds M1.
