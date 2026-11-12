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
  side, `parse(print(m)) == m` for every well-formed module `m`, and
  `print(parse(t)) == t` for every text `t` printed from one. Every valid
  module is well formed. A text that does not decode, such as one with an
  undefined operand or a type mismatch, is a parse error with a location
  (ADR-2026-10-29-2014).
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
| M1 | Complete the fir IR | [milestone 8](https://github.com/pmatos/funk/milestone/8) |
| M2 | Full x86-64 backend | [milestone 2](https://github.com/pmatos/funk/milestone/2) |
| M3 | Vow frontend | [milestone 3](https://github.com/pmatos/funk/milestone/3) |
| M4 | C and C++ frontend | [milestone 4](https://github.com/pmatos/funk/milestone/4) |
| M5 | Compile the Linux kernel | [milestone 5](https://github.com/pmatos/funk/milestone/5) |
| M6 | JIT compilation | [milestone 6](https://github.com/pmatos/funk/milestone/6) |
| M7 | x86 to arm64 binary translation | [milestone 7](https://github.com/pmatos/funk/milestone/7) |
| M8 | WebAssembly backend | [milestone 9](https://github.com/pmatos/funk/milestone/9) |
| M9 | Per-compile refinement checks (S8) | [milestone 10](https://github.com/pmatos/funk/milestone/10) |

The milestones were renumbered on 2026-11-05, when the IR got a milestone of
its own ahead of the backend (ADR-2026-11-05-2255). In an ADR, issue or
comment written before then, M1 to M6 mean today's M2 to M7.

### M0: fir compiler with a basic x86-64 backend

**Status.** Done. The epic closed on 2026-11-05 with every "Done when" item
met, and [`m0-audit.md`](m0-audit.md) records the evidence.

**Goal.** The first end-to-end slice: a tiny fir core with a formal semantics
in Lean, a Rust library that parses, verifies and prints it with byte-exact
round trips, and a naive x86-64 backend whose output is checked against the
Lean interpreter on every test. Epic: [#5](https://github.com/pmatos/funk/issues/5).

**Scope.** Integers only (`i1` to `i128` in the backend; any width up to
16,777,215 in the IR and interpreter), arithmetic, bitwise ops and shifts,
compares, `select`, width changes, `freeze`, branches with block arguments,
calls (including recursion) and return. No memory: `ptr` is reserved as a type
but has no ops. The full op set is in the epic. A function's observable
behaviour in M0 is its returned values, UB, or fuel exhaustion. A function may
return any number of values, none included (ADR-2026-10-30-0816). That is
narrower than S4's full definition, which also counts calls to external
symbols and reachable memory, because every M0 callee is inside the module.
The `i128` division helper is the one exception, and it is tested on its own.

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
   spec (which are the Lean semantics), the Rust IR and verifier, the
   backend, and corpus tests checked against `fir-ref`. The Lean round-trip
   proof does not grow with each family: it is proved once, for every core
   op ([#11](https://github.com/pmatos/funk/issues/11)).
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

### M1: Complete the fir IR

**Goal.** Settle fir before we build a real backend or a frontend on it. The
IR is the contract that every backend, pass and frontend is built against, so
it is decided, specified and checked first. M1 takes fir from M0's integer
core to an IR that the M3 to M5 frontends can lower their sequential code to,
with concurrency, exceptions and contracts arriving through hooks M1 leaves in
the format (ADR-2026-11-09-1548): decided, in the spec (formal and readable),
run by `fir-ref`, held by `funk-ir`, and checked by the differential harness.
Epic: [#177](https://github.com/pmatos/funk/issues/177).

**Scope.** Each item goes through every layer at once, as M0's op families
did: its decision as an ADR, its rules in the spec (which are the Lean
semantics), `fir-ref`, the Rust IR, verifier, parser and printer, the corpus,
and the naive backend, which lowers each new op the simplest correct way so
that the harness checks it natively. Making that code good is M2's job.

1. **The M0 close-out audit.** The issues it filed come first: the readable
   spec (#161), random differential testing (#165) and the rest of the list
   on the IR epic.
2. **Memory (S3, ADR-2026-11-09-1542).** Logical blocks in typed memories,
   as G0 asks; `ptr` gets its ops; loads and stores, volatile ones included;
   stack allocation; memory intrinsics (ADR-2026-11-09-1551); and what a run
   shows an observer once memory exists (S4, ADR-2026-11-09-1540).
3. **Effect classes (H7, ADR-2026-11-09-1541).** Each op's set of effects,
   named by memory and proved sound, so passes and the backend know what they
   may reorder.
4. **Globals, external functions and calls (H3).** Module-level globals by
   symbol (ADR-2026-11-09-1546); declarations of functions that funk did not
   compile, variadic ones included, with sign- and zero-extension markers
   (ADR-2026-11-09-1547); indirect calls, `unreachable` and proper tail calls
   (ADR-2026-11-09-1548, ADR-2026-11-09-1553); and inline assembly, whose
   native lowering waits for M4 (ADR-2026-11-09-1552). An observer sees
   external calls, as S4 says.
5. **Floating point (S5, ADR-2026-11-09-1549)**, over a generic family of
   formats, with round to nearest even and three fast-math flags.
6. **Aggregates (ADR-2026-11-09-1550)**, as layouts over memory for calling
   conventions and the frontends.
7. **Dialects and extensions (H4, H5; ADR-2026-11-09-1543,
   ADR-2026-11-09-1544).** How a dialect adds ops, types, attributes and kinds
   of item, made real with a GPU-kernel-shaped second dialect in tree
   (ADR-2026-11-09-1545), so that G0's openness is tested, not only promised.

**Out of M1.** Concurrency (S6), exceptions and unwinding, defining variadic
functions, vectors, contract ops, structured control flow (H6) and the rest of
the [deferred list](roadmap-deferred.md) stay with the milestones that need
them; M1 leaves
hooks for the first three (ADR-2026-11-09-1548). S8 is M9, after M2.

**Done when** every M1 decision is an accepted ADR; the spec covers each item,
formal and readable; `fir-ref` runs it; the Rust tools agree with `fir-ref` on
the whole corpus and on random programs; native results from the naive backend
refine `fir-ref`'s; the G0 checks pass with the second dialect; and CI runs all
of it.

### M2: Full x86-64 backend

**Goal.** Grow the naive backend into a real one that handles real-world
programs, on the IR that M1 settled (epic
[#164](https://github.com/pmatos/funk/issues/164)). We improve one piece at a
time, checking each against the Lean interpreter before starting the next:

1. **Real register allocation**, replacing spill-everything.
2. **Proper instruction selection** and broader instruction coverage,
   memory and floating point included.
3. **Instruction scheduling.** Last, because a correct backend does not need
   it.

Calling conventions grow with the IR: aggregates, varargs and what the memory
model brought in.

**Optimizer track.** M2 also starts the mid-end, as a track that runs beside
the backend work: rewrite rules proven in Lean and emitted as Rust matchers by
a generator, a growing rule library, DCE and CSE, an aegraph view of pure ops
(H7), and location propagation by the rewrite engine (H8). Each rule or pass is
tested against `fir-ref` before it lands. S8 checks them per compile later, in
M9.

**Rulings for M2**, from the human on 2026-11-12
([#164](https://github.com/pmatos/funk/issues/164#issuecomment-6820504273)):

- M2 may start before M1 closes, as long as the foundations that each step
  needs are in place.
- The backend is checked by differential tests against `fir-ref`, on the
  corpus and on random programs. A formal model of x86 waits for later.
- Register allocation starts as linear scan, behind an interface that lets
  other allocators be tried. funk writes its own allocator. The allocator,
  scheduling and the optimizer live in generic crates, not in the x86 crate
  (ADR-2026-10-30-1228).
- CPU extensions come in through a `--cpu` flag, a few at a time. The default
  stays baseline x86-64.
- Vectors and SIMD are not part of M2.
- Nothing is called proven unless it is. A Lean proof of a pass covers the
  transformation, not the hand-written Rust that performs it. In M2 that Rust
  is checked by tests only. S8 checks it later, in M9.

**Done when** the register-allocating backend has replaced spill-everything
for every op of M1, every sub-issue of the epic is closed, and native results
refine `fir-ref`'s on the whole corpus and on random programs, with CI running
all of it. The bar is correctness only: M2 sets no target for the speed or
size of the generated code, and optimization comes later.

### M3: Vow frontend

A frontend for [Vow](https://github.com/vow-lang/vow) that lowers to fir, so
Vow programs compile to x86-64 through funk. Vow runs on Cranelift today, so
moving it to funk is how we dogfood the toolchain.

### M4: C and C++ frontend

A C and C++ frontend that lowers to fir, compiling C and C++ to x86-64 through
funk.

### M5: Compile the Linux kernel

Build the Linux kernel with the funk C frontend and the funk toolchain.

### M6: JIT compilation

Compile fir to native code in memory at runtime. Useful on its own, and the
base for M7.

### M7: x86 to arm64 binary translation

An x86 assembly frontend that lowers to fir, with the M6 JIT targeting arm64,
in the style of FEX-Emu. This needs an arm64 backend, which no milestone covers
yet.

### M8: WebAssembly backend

**Goal.** A second backend that compiles fir to WebAssembly. It tests G0 on a
target that is not x86-64 or arm64: a stack machine with structured control
flow, several memories, and values owned by the host. Epic:
[#293](https://github.com/pmatos/funk/issues/293).

**Scope**, as the human ruled on 2026-11-11 (ADR-2026-11-11-1450):

- The most recent WebAssembly version, with the proposals accepted into it.
- Two targets: wasm32, with 32-bit pointers, and wasm64 (memory64), with
  64-bit pointers.
- Host references such as `externref` and `funcref` are target extension
  types, as in LLVM ([#292](https://github.com/pmatos/funk/issues/292)).
- The harness runs the output with wasmtime and checks that its results
  refine `fir-ref`'s, as it does for native code.

The epic will be split into tasks later. Open questions include how fir's
control-flow graph lowers to Wasm's structured blocks and loops, irreducible
control flow included. Its order relative to M2 to M7 is not set.

### M9: Per-compile refinement checks (S8)

**Goal.** After an optimizer pass changes a function, an SMT solver checks
that the new function refines the old one (S8). M9 runs after M2, whose passes
it checks. The human split it out of M2 on 2026-11-12. Its decisions wait on
[#341](https://github.com/pmatos/funk/issues/341).

## Decisions deferred past M0

The decisions that the fir v0 decision record left open, and the milestone
likely to need each one, are listed in
[`roadmap-deferred.md`](roadmap-deferred.md).
