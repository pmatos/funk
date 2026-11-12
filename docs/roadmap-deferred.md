# Decisions deferred past M0

This page belongs to the [roadmap](roadmap.md). It lists the decisions
that the fir v0 decision record left open, and which milestone is likely
to need each one. Changing it is a direction call, like the roadmap.

Open in the fir v0 decision record, and out of M0 on purpose. Do not design
around a guess for any of these. If work needs one, open a `human-ready` issue.
The human decided S3, S5, H4, H5 and H7 for M1 on 2026-11-09; the table names
their ADRs.

S3, S8, H4 and H7 are marked Foundational in the record, which means decided
before the code that depends on them. M0 has no memory, no optimization passes
and no dialects, so none of its code depends on them. Each must be decided
before the first step that does, as the table says.

| ID | Decision | Likely needed by |
| --- | --- | --- |
| S3 | Memory model (Foundational; G0: several memories and address spaces) | Decided: ADR-2026-11-09-1542 |
| S5 | Floating point | Decided: ADR-2026-11-09-1549 |
| S6 | Concurrency | M4 at the latest (C and C++ atomics) |
| S8 | SMT equivalence checking (Foundational) | M2, before its first optimizer pass: [#341](https://github.com/pmatos/funk/issues/341) |
| H4, H5 | Dialects and extensions (H4 Foundational; G0: extensions add types and attributes, not only ops) | Decided: ADR-2026-11-09-1543, ADR-2026-11-09-1544 |
| H6 | Structured control flow | When a frontend or pass needs it |
| H7 | Effect classes beyond "pure" and "call" (Foundational) | Decided: ADR-2026-11-09-1541 |
| P2 | Public API shape | At the start of M3 (ADR-2026-11-09-1554) |

For S8 the record proposes three stages: a hand-written Rust SMT encoder,
tested against `fir-ref`; then an encoder written in Lean and proven against
the semantics; then `bv_decide` as the bar for admitting rewrite rules.

The record also leaves these out of v0, each with a hook in the format so it
can come back without a break:

| Left out of v0 | Likely needed by |
| --- | --- |
| Exceptions and unwinding | M4 (C++) |
| Vectors and SIMD | M5 and M7 (SSE and AVX); not M2, as the human ruled on 2026-11-12 |
| Contract ops (`assume`, `assert`, `requires`, `ensures`) | M3 (Vow) |
| Garbage-collected or managed memory | A frontend that needs it |
| Non-default FP rounding and FP exceptions | M4 or M5 |
| A binary format | When text parsing becomes a bottleneck |

Inline assembly and volatile accesses, which the record did not cover, join M1
(ADR-2026-11-09-1548).

## Open gaps

- **arm64 backend.** M7 needs one, and no milestone covers it.
- **Non-CPU targets.** G0 keeps the door open for GPUs, NPUs, TPUs and more,
  but no milestone targets one yet.
- **Wasm and LLVM IR frontends.** The record used a Wasm frontend as its first
  strawman and plans LLVM IR import. Neither has a milestone. M0 starts from
  fir text directly, so the Wasm strawman is not needed for M0.
