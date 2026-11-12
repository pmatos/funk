# Current decisions: semantics, dialects in M1

This page continues semantics-m1-design.md. It says what the ADRs decide about
dialects in M1: how levels and lowering work, and the second dialect in tree.
It is the record: when this page and an ADR disagree, the page wins, and the
ADR is fixed or deleted (ADR-2026-11-09-1610).

These are decided designs, and the spec and the tools do not implement them
all yet. semantics-dialects.md says what holds of dialects today.

## Dialects

How dialects extend fir, the sum, kinds of item, region kinds and a module's
dialect set are on semantics-dialects.md (ADR-2026-11-09-1543). M1 builds on
them: globals and external declarations register their kinds of item through
the hook, and a `module` item nests a symbol table with its own dialect set, so
a host module holds a device module (#211). No region kind beyond the core's
CFG region runs in M1. The round-trip and validation proofs are restated over
sums of dialects and over registered kinds of item (ADR-2026-11-09-1543).

## Levels and lowering

In v0 a module holds ops of one abstraction level, and lowering takes a whole
module from one level to the next. Levels mix only through nested modules: a
host module at one level may hold a device module at another
(ADR-2026-11-09-1544).

A lowering that funk performs, from one dialect set to another, must produce a
module that refines its input. It is proved once in Lean, or checked per compile
once S8 exists (ADR-2026-11-09-1544).

A dialect is not required to lower to core. A terminal dialect is lowered only
by its own backend, to its own hardware. Its programs are still checked by its
semantics in `fir-ref`. Its backend is checked against `fir-ref` like the x86-64
backend, by refinement of observed runs (ADR-2026-11-09-1544).

This is H5 of the fir v0 decision record, and the human ruled it on 2026-11-09,
on #202. Rejected: a closed core that admits extensions only with a verified
lowering to core, as the record proposed. A quantum or photonic dialect cannot
lower to a CPU-shaped core, so it would fail G0.

## The second dialect

The second dialect in tree is shaped like a GPU kernel language
(ADR-2026-11-09-1545):

- A host module holds a nested device module whose dialect set includes the GPU
  dialect. Kernel functions live in the device module.
- It adds ops of its own, such as work-item and work-group ids and sizes, and at
  least one type or attribute of its own.
- It adds a memory in a non-default address space, such as work-group shared
  memory, with effects named by that memory.

`fir-ref` runs one work-item of a kernel, with its ids given as inputs. Ops
whose meaning needs other work-items, such as barriers, are left out or
admitted without execution rules
([fir-ref.md](fir-ref.md#an-op-without-rules)). A launch op in host code is out
of M1. M1's results are not a model of a whole kernel. The semantics grows into
a full kernel model only when S6 decides concurrency (ADR-2026-11-09-1545).

The dialect is terminal. It has no lowering to core and no native backend in M1
(ADR-2026-11-09-1544, ADR-2026-11-09-1545).

The G0 checks show these things with it (ADR-2026-11-09-1545):

- Generic code in `funk-ir` and `lean/Fir` loads it with no change but its
  registration.
- A host module with a device module round-trips byte for byte across Rust and
  Lean, and both sides validate it the same way, must-reject cases included.
- Its kernels run in `fir-ref` one work-item at a time, and `funk` and `fir-ref`
  agree on its corpus.
- The generic results (round trip, refinement, congruence) are restated for a
  dialect set that includes it.

Use-once (linear) values stay covered by the toy test of #167. The
implementation of this dialect, in #212, waits for memory
(ADR-2026-11-09-1545). Nested modules have landed (#211).

The human ruled this on 2026-11-09, on #202. Rejected: a small quantum-style
dialect, which tests neither nested modules nor several memories; it remains a
candidate for a later G0 check. Rejected too: a CPU-shaped dialect such as
checked arithmetic, which tests little of what G0 is about.
