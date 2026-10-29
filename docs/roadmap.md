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
toolchain is tested and, over time, proven against that definition.

## Ground rules that shape every milestone

These hold across the whole roadmap. Each is, or will be, an ADR.

- **The semantics of fir lives in Lean, and only there.** Lean holds the
  definition of fir, a reference interpreter, its own `.fir` parser and
  printer, and later rule proofs and a proven SMT encoder. The interpreter is a
  test oracle for development and CI. It never ships inside a compiler.
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
- **Each step leaves something runnable.** We grow funk one piece at a time and
  check every new piece against the oracle before building on it.

## Milestones

| Milestone | Goal | GitHub |
| --- | --- | --- |
| M0 | fir compiler with a basic x86-64 backend | [milestone 1](https://github.com/pmatos/funk/milestone/1) |
| M1 | Full x86-64 backend | [milestone 2](https://github.com/pmatos/funk/milestone/2) |
| M2 | VAU frontend | [milestone 3](https://github.com/pmatos/funk/milestone/3) |
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
set is in the epic.

**Decisions already made** for M0, recorded in the fir v0 decision record on
2026-10-29: E0 (CFG with ordering by position), S1 (poison plus `freeze`, no
`undef`), S2 (`iN` bitvectors, signedness on ops, `i128` in M0), S4
(refinement), S7 (semantics in Lean, monadic interpreter with fuel), H1 (block
arguments), H2 (functions isolated from above), H3 (globals by symbol), H8
(required source locations, printed as `@N` with a `locs` table) and P3 (one
canonical text format). The epic spells each one out; the first M0 task turns
each into an ADR.

**Order of work.** Each step is one or more PRs, and each ends with something
we can run. We first build a thin path through every layer, then widen it one
op family at a time. That way the harness exists before most of the backend,
and every new piece is checked against the oracle as it lands.

1. **Record the direction.** One ADR per decision above, and a small v0 spec in
   `docs/spec/fir/`: abstract syntax, validation, execution and text format,
   with the concrete grammar. Small enough to finish in days. The concrete
   syntax goes to the human for review before code depends on it.
2. **Tracer bullet through every layer.** One tiny program (parameters,
   `const`, `add` and `ret`) goes through each layer in turn. First the Rust
   IR crate (`funk-ir`), with `funk fmt`, `funk verify` and round trips that
   are checked in both directions and fuzzed. Then the Lean reference
   interpreter (`fir-ref`) and the cross-language round trip. Then the naive
   x86-64 backend behind `funk build`, and finally the differential harness.
   Whether to emit assembly or ELF directly is an ADR, and spilling every
   value is the baseline register allocation.
3. **Widen one op family at a time.** The families are arithmetic with poison
   and `freeze`, bitwise ops and shifts, compares and `select`, width changes,
   division, branches with block arguments, and calls. Each family goes
   through every layer at once: the spec, the Lean semantics and round-trip
   proof, the Rust IR and verifier, the backend, and corpus tests checked
   against `fir-ref`.
4. **`i128` in the backend.** Register pairs for every op, then division
   through a runtime helper.
5. **Audit.** Check that the corpus covers each op, flag and width, port LLVM
   tests to fir by hand, and check the spec against the implementation.

**CI** grows with each step. Every check lives in `.pre-commit-config.yaml`,
and it lands in the same PR as the code it checks.

**Done when** every M0 decision is an accepted ADR, the spec is complete enough
to implement from, round trips hold in Rust and across Rust and Lean under
fuzzing, native results refine the Lean results on the whole corpus, and CI
runs all of it.

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

### M2: VAU frontend

A VAU frontend that lowers to fir, so VAU programs compile to x86-64 through
funk.

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

| ID | Decision | Likely needed by |
| --- | --- | --- |
| S3 | Memory model | M1 (memory, loads and stores) |
| S5 | Floating point | M1 or the first frontend that needs it |
| S6 | Concurrency | M3 at the latest (C and C++ atomics) |
| S8 | SMT equivalence checking | When hand-written passes need per-compile checks |
| H4, H5 | Dialects and extensions | M2 (frontend-level ops) |
| H6 | Structured control flow | When a frontend or pass needs it |
| H7 | Effect classes beyond "pure" and "call" | M1 (memory) |
| P2 | Public API shape | Before external users build on funk |

## Open gaps

- **arm64 backend.** M6 needs one, and no milestone covers it.
