# Roadmap

What we build next, and in what order. The spec (`docs/spec/`) says what funk
is; the ADRs (`docs/adrs/`) say what we decided and why. This file sets the
sequence. Changing it is a direction call: propose it in its own PR and flag it
for the human (see [`AGENTS.md`](../AGENTS.md)).

Milestones have no due dates. Each one is a GitHub milestone, and the work
inside it is tracked as issues, starting from an epic.

## What funk is

Funk is a reusable compiler toolchain in the spirit of LLVM: a library that
production compilers are built on. Its intermediate representation is **fir**.
Funk is verification-first: the meaning of fir is defined formally, and the
toolchain is tested and, over time, proven against that definition. Funk is
also agent-native: agents build it and use it, so its core fits in an agent's
context, its tools speak structured JSON as well as text, and every change an
agent proposes is checked by refinement.

## Ground rules that shape every milestone

These hold across the whole roadmap. Each is, or will be, an ADR.

- **fir must be able to reach any kind of hardware (G0).** CPUs first, but
  also GPUs, NPUs, TPUs and hardware we cannot predict yet, such as photonic or
  quantum processors. The core stays a small CPU-shaped dialect, and other
  targets come in as extension dialects, so the openness lives in how fir is
  built, not in what the core contains. Every decision is checked against this
  rule, and none may close that door. Set on 2026-10-29; the G0 section of the
  fir v0 decision record checks each decided row against it.
- **The semantics of fir lives in Lean, and only there.** Lean holds the
  definition of fir, a reference interpreter, its own `.fir` parser and
  printer, and later rule proofs and a proven SMT encoder. The interpreter is a
  test oracle for development and CI. It never ships inside a compiler.
- **The spec is formal and readable, from one source.** Great documentation of
  fir is a first-class deliverable, not an afterthought. Every chapter of the
  spec (abstract syntax, validation, execution, text format) is both formal
  and readable by a person, and both views come from one source so they cannot
  drift. Decision P1 settles how: the spec is literate Lean, rendered with
  Verso. This holds in every milestone: no change to fir's semantics merges
  without its spec section, formal and readable.
- **The toolchain is Rust.** The IR library, verifier, passes, backends and
  driver are all Rust. There is no Rust interpreter in M0. A Rust evaluator may
  come later if fuzzing throughput or the JIT needs one, and then only as a copy
  tested against Lean, never as the definition.
- **The text format is the interface between Lean and Rust.** Rust prints a
  module, Lean parses and reprints it, and the bytes must match. Within each
  side, `print(parse(t)) == t` and `parse(print(m)) == m`.
- **Every piece of Rust is either generated from Lean or checked against it.**
  Rewrite rules proven in Lean are emitted as Rust. Hand-written parts, such as
  backends, register allocation and scheduling, are checked by differential
  tests against the Lean interpreter now, and by per-compile refinement checks
  later.
- **Correctness means refinement.** A target is correct if each of its
  observable behaviours is allowed by the source. Source UB allows anything; a
  poison result is refined by any value.
- **Diagnostics are structured.** Every tool reports errors with IR locations,
  as text for people and as JSON on request for agents.
- **Each step leaves something runnable.** We grow funk one piece at a time and
  check every new piece against the oracle before building on it.

## Milestones

| Milestone | Goal | GitHub |
| --- | --- | --- |
| M0 | fir compiler with a basic x86-64 backend | [milestone 1](https://github.com/pmatos/funk/milestone/1) |
| M1 | Full x86-64 backend | [milestone 2](https://github.com/pmatos/funk/milestone/2) |
| M2 | Vow frontend | [milestone 3](https://github.com/pmatos/funk/milestone/3) |
| M3 | C and C++ frontend | [milestone 4](https://github.com/pmatos/funk/milestone/4) |
| M4 | Compile the Linux kernel | [milestone 5](https://github.com/pmatos/funk/milestone/5) |
| M5 | JIT compilation | [milestone 6](https://github.com/pmatos/funk/milestone/6) |
| M6 | x86 to arm64 binary translation | [milestone 7](https://github.com/pmatos/funk/milestone/7) |

### M0: fir compiler with a basic x86-64 backend

**Goal.** The first end-to-end slice: a tiny fir core with a formal semantics
in Lean, a Rust library that parses, verifies and prints it with byte-exact
round trips, and a naive x86-64 backend whose output is checked against the
Lean interpreter on every test. Epic: [#5](https://github.com/pmatos/funk/issues/5).

**Scope.** Integers only (`i1` to `i128` in the backend; any width in the IR
and interpreter), arithmetic, bitwise ops and shifts, compares, `select`, width
changes, `freeze`, branches with block arguments, calls (including recursion)
and return. No memory: `ptr` is reserved as a type but has no ops. The full op
set is in the epic. A function's observable behaviour in M0 is its return
value, UB, or fuel exhaustion. That is narrower than S4's full definition,
which also counts calls to external symbols and reachable memory, because
every M0 callee is inside the module. The `i128` division helper is the one
exception, and it is tested on its own.

**Decisions already made** for M0, recorded in the fir v0 decision record on
2026-10-29: E0 (CFG with ordering by position), S1 (poison plus `freeze`, no
`undef`), S2 (`iN` bitvectors, signedness on ops, `i128` in M0), S4
(refinement), S7 (semantics in Lean, monadic interpreter with fuel), H1 (block
arguments), H2 (functions isolated from above), H3 (globals by symbol), H8
(required source locations, printed as `@N` with a `locs` table), P3 (one
canonical text format) and P1 (below). The epic spells each one out; the first
M0 task turns each into an ADR.

**What G0 asks of M0.** The core op set stays small, but the structures that
hold it must not be closed. Following the G0 check in the decision record, the
Rust IR represents ops generically (a name, operands, attributes, result types
and regions, checked through a registry) rather than as a closed Rust enum,
the Lean semantics is parameterized over the dialect, and the text format uses
one grammar for every op, so a new dialect needs no parser change.

**`freeze` in the oracle**, decided on 2026-10-29 and recorded in #7. `freeze`
of poison makes a function's behaviour a set of outcomes. The interpreter has a
choice effect, and `fir-ref` has an exhaustive mode (the whole set, within a
budget) and a scripted mode (one outcome for a given choice sequence). A
native result passes when it is in the set, and a test whose set contains UB
is invalid. That is what "native results refine the Lean results" means below.

**P1: the spec is literate Lean, rendered with Verso.** Decided on
2026-10-29. The spec keeps the Wasm spec's chapters: abstract syntax,
validation, execution and text format. Its formal content is the Lean
definitions themselves, and its prose sits beside them as literate Lean.
Verso, Lean's documentation tool, renders the two together as the readable
document, and CI builds it on every PR. So the readable spec can never drift
from the formal one. The Rust verifier stays hand-written and is tested
against Lean. A spec DSL in the style of Wasm's SpecTec, generating Lean, the
Rust verifier and the document from one source, was the alternative; it can
still come later if the hand-written verifier starts to drift.

**Order of work.** Each step is one or more PRs, and each ends with something
we can run. We first build a thin path through every layer, then widen it one
op family at a time. That way the harness exists before most of the backend,
and every new piece is checked against the oracle as it lands.

1. **Record the direction.** One ADR per decision above. Alongside it, a spike
   ([#24](https://github.com/pmatos/funk/issues/24)) decides whether the Lean
   semantics builds on LeanMLIR's SSA framework or on our own calculus. It
   prototypes a small piece of fir both ways, and its ADR goes to the human.
   Then the v0 spec as literate Lean with Verso, built on the spike's
   decision: the full concrete grammar, the abstract syntax of every M0 op,
   and the general definitions of execution (outcomes, observable behaviour,
   refinement). The concrete syntax goes to the human for review before code
   depends on it.
2. **Tracer bullet through every layer.** One tiny program (parameters,
   `const`, `add` and `ret`) goes through each layer in turn. First the Rust
   IR crate (`funk-ir`), with `funk fmt`, `funk verify` and round trips that
   are checked in both directions and fuzzed. Then the Lean reference
   interpreter (`fir-ref`) and the cross-language round trip. Then the naive
   x86-64 backend behind `funk build`, and finally the differential harness.
   Whether to emit assembly or ELF directly is an ADR, and spilling every
   value is the baseline register allocation. From this step on, CI builds
   the readable spec from its source, so it always matches the formal
   definitions.
3. **Widen one op family at a time.** The families are arithmetic with poison
   and `freeze`, bitwise ops and shifts, compares and `select`, width changes,
   division, branches with block arguments, and calls. Each family goes
   through every layer at once: its validation and execution rules in the
   spec (which are the Lean semantics), the round-trip proof, the Rust IR and
   verifier, the backend, and corpus tests checked against `fir-ref`.
4. **`i128` in the backend.** Register pairs for every op, then division
   through a runtime helper.
5. **Audit.** Check that the corpus covers each op, flag and width, port LLVM
   tests to fir by hand, and check the spec against the implementation.

**CI** grows with each step. Every check lives in `.pre-commit-config.yaml`,
and it lands in the same PR as the code it checks.

**Done when** every M0 decision is an accepted ADR, the spec is complete enough
to implement from, its readable document (formalization included) is
generated from the same source as the formal definitions, round trips hold in
Rust and across Rust and Lean under fuzzing, native results refine the Lean
results on the whole corpus, and CI runs all of it.

### M1: Full x86-64 backend

**Goal.** Grow the naive backend into a real one that handles real-world
programs. We improve one piece at a time, checking each against the Lean
interpreter before starting the next:

1. **Real register allocation**, replacing spill-everything.
2. **Memory, loads and stores.** This needs the memory model (S3) decided
   first, then added to the Lean semantics, the spec and the IR.
3. **Proper instruction selection** and broader instruction coverage.
4. **Instruction scheduling.** Last, because a correct backend does not need
   it.

Calling conventions grow with the IR: aggregates, varargs and whatever the
memory model brings in. As hand-written passes multiply, per-compile refinement
checks (SMT, S8) start to matter here.

**Optimizer track.** M1 also starts the mid-end, as a track that runs beside
the backend work: rewrite rules proven in Lean and emitted as Rust matchers by
a generator, a growing rule library, verified DCE and CSE, an aegraph view of
pure ops (H7), and location propagation by the rewrite engine (H8). Each rule
or pass is checked against the Lean semantics before it lands, and S8 and H7
must be decided before the first pass that depends on them.

### M2: Vow frontend

A frontend for [Vow](https://github.com/vow-lang/vow) that lowers to fir, so
Vow programs compile to x86-64 through funk. Vow runs on Cranelift today, so
moving it to funk is how we dogfood the toolchain.

### M3: C and C++ frontend

A C and C++ frontend that lowers to fir, compiling C and C++ to x86-64 through
funk.

### M4: Compile the Linux kernel

Build the Linux kernel with the funk C frontend and the funk toolchain.

### M5: JIT compilation

Compile fir to native code in memory at runtime. Useful on its own, and the
base for M6.

### M6: x86 to arm64 binary translation

An x86 assembly frontend that lowers to fir, with the M5 JIT targeting arm64,
in the style of FEX-Emu. This needs an arm64 backend, which no milestone covers
yet.

## Decisions deferred past M0

Open in the fir v0 decision record, and out of M0 on purpose. Do not design
around a guess for any of these. If work needs one, open a `human-ready` issue.

S3, S8, H4 and H7 are marked Foundational in the record, which means decided
before the code that depends on them. M0 has no memory, no optimization passes
and no dialects, so none of its code depends on them. Each must be decided
before the first step that does, as the table says.

| ID | Decision | Likely needed by |
| --- | --- | --- |
| S3 | Memory model (Foundational; G0: several memories and address spaces) | Before M1's memory step |
| S5 | Floating point | M1 or the first frontend that needs it |
| S6 | Concurrency | M3 at the latest (C and C++ atomics) |
| S8 | SMT equivalence checking (Foundational) | Before the first hand-written pass needs per-compile checks |
| H4, H5 | Dialects and extensions (H4 Foundational; G0: extensions add types and attributes, not only ops) | Before M2 adds frontend-level ops |
| H6 | Structured control flow | When a frontend or pass needs it |
| H7 | Effect classes beyond "pure" and "call" (Foundational) | Before M1's memory step |
| P2 | Public API shape | Before external users build on funk |

For S8 the record proposes three stages: a hand-written Rust SMT encoder,
tested against `fir-ref`; then an encoder written in Lean and proven against
the semantics; then `bv_decide` as the bar for admitting rewrite rules.

The record also leaves these out of v0, each with a hook in the format so it
can come back without a break:

| Left out of v0 | Likely needed by |
| --- | --- |
| Exceptions and unwinding | M3 (C++) |
| Vectors and SIMD | M1 or M4, and M6 (SSE and AVX) |
| Contract ops (`assume`, `assert`, `requires`, `ensures`) | M2 (Vow) |
| Garbage-collected or managed memory | A frontend that needs it |
| Non-default FP rounding and FP exceptions | M3 or M4 |
| A binary format | When text parsing becomes a bottleneck |

M4 will also need inline assembly and volatile accesses, which the record does
not cover yet.

## Open gaps

- **arm64 backend.** M6 needs one, and no milestone covers it.
- **Non-CPU targets.** G0 keeps the door open for GPUs, NPUs, TPUs and more,
  but no milestone targets one yet.
- **Wasm and LLVM IR frontends.** The record used a Wasm frontend as its first
  strawman and plans LLVM IR import. Neither has a milestone. M0 starts from
  fir text directly, so the Wasm strawman is not needed for M0.
