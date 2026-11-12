# Status

This file is the account of what exists on `main` today and what does
not. The [README](../README.md#status) lists funk's milestones, and the
[roadmap](roadmap.md) plans them.

M0 is done. Issue [#5](https://github.com/pmatos/funk/issues/5) was its
epic, and it closed on 2026-11-05 with every "Done when" item met. The
[M0 audit](m0-audit.md) records the evidence. M1 has started, and issue
[#177](https://github.com/pmatos/funk/issues/177) is its epic. These parts
of funk are on `main`:

- The decisions that M0 starts from, each recorded as an ADR.
- A [spike report](spikes/leanmlir.md) that compared two ways to write
  fir's Lean semantics. One builds on
  [LeanMLIR](https://github.com/opencompl/lean-mlir), an SSA framework in
  Lean. The other is fir's own calculus. The project's human lead chose fir's
  own calculus
  ([ADR-2026-10-29-2030](adrs/2026-10-29-2030-fir-lean-semantics-own-calculus.md)).
- The fir v0 spec. Its chapters are Lean modules in `lean/`, with prose beside
  each definition. [Verso](https://github.com/leanprover/verso), Lean's
  documentation tool, renders them as HTML from `docs/spec/`. The spec gives
  fir's abstract syntax, its validation rules and the check that decides
  them. It gives execution: outcomes, refinement, poison, the interpreter,
  the rules of every core op, the three modes of `fir-ref run` and the
  proofs about runs. And it gives the text format: its grammar, its printer
  and its parser. CI builds the spec on every pull request, and every push
  to `main` publishes it at <https://p.ocmatos.com/funk/>.
- The Rust IR library `funk-ir` and the driver `funk`
  ([#9](https://github.com/pmatos/funk/issues/9)). `funk-ir` holds fir in
  memory, with a parser, a printer and a verifier that follow the spec. Its
  ops and types are checked through a registry of dialects
  ([ADR-2026-10-30-1146](adrs/2026-10-30-1146-generic-ops-and-registry.md)),
  and the core dialect registers `const`, `add`, `sub`, `mul`, their flags
  `nuw` and `nsw`, `freeze`, `poison`, the bitwise ops `and`, `or` and
  `xor`, the shifts `shl`, `lshr` and `ashr`, the width changes `zext`,
  `sext` and `trunc`, `sdiv` and `udiv` with their flag `exact`, `srem`,
  `urem`, `icmp` with its ten predicates, `select`, the branches `br` and
  `cond_br`, `ret`, the terminator `unreachable`, and `call` of any
  function of the module, with any number of arguments and results
  ([#14](https://github.com/pmatos/funk/issues/14),
  [#15](https://github.com/pmatos/funk/issues/15),
  [#16](https://github.com/pmatos/funk/issues/16),
  [#17](https://github.com/pmatos/funk/issues/17),
  [#18](https://github.com/pmatos/funk/issues/18),
  [#19](https://github.com/pmatos/funk/issues/19),
  [#20](https://github.com/pmatos/funk/issues/20),
  [#122](https://github.com/pmatos/funk/issues/122),
  [#228](https://github.com/pmatos/funk/issues/228)). The verifier checks
  dominance across blocks, block arguments, that every block is
  reachable from the entry, and that each call matches its callee's
  signature. `funk fmt` prints fir
  in its canonical form, and `funk verify` checks it. Both report as text,
  or as JSON with `--json`.
- The Lean parser, a section of the spec, and the first command of the
  reference interpreter's executable, `fir-ref fmt`
  ([#10](https://github.com/pmatos/funk/issues/10)). The parser reads every
  op of every dialect. Lean reprints what Rust prints, byte for byte, on the
  shared texts and on modules from the Rust generator. Lean proves that
  parsing a printed well-formed module gives the module back, and that
  every module the parser gives is well formed
  ([#11](https://github.com/pmatos/funk/issues/11),
  [#105](https://github.com/pmatos/funk/issues/105)).
- The naive x86-64 backend, `funk-x86-64`
  ([#12](https://github.com/pmatos/funk/issues/12)). `funk build` compiles
  `const`, `add`, `sub` and `mul` with their flags, `freeze`, `poison`,
  the bitwise ops and shifts, `zext`, `sext`, `trunc`, `sdiv` and `udiv`
  with or without `exact`, `srem`, `urem`, `icmp`, `select`, `br`,
  `cond_br`, `ret`, `unreachable` and `call` at `i1`, `i8`, `i16`, `i32`,
  `i64` and `i128` into an object file and an executable for Linux. An
  `i128` is a pair of eightbytes, and each op lowers it through a pair of
  registers
  ([ADR-2026-11-03-010730](adrs/2026-11-03-010730-an-i128-is-a-pair-of-eightbytes.md)).
  Native code holds no poison: a broken `nuw` or `nsw` gives the
  wrapped result, a broken `exact` the plain quotient, a shift by `N` or
  more gives what x86's masked shift gives (at `i128`, what the pair's
  shift sequence gives for the amount's low 7 bits), and `freeze` copies
  its operand
  ([ADR-2026-10-30-2248](adrs/2026-10-30-2248-native-code-holds-no-poison.md)).
  A `poison` writes zero into each eightbyte of its result's slot
  ([ADR-2026-11-03-1616](adrs/2026-11-03-1616-the-x86-64-backend-lowers-poison-to-zero-in-every-eightbyte.md)).
  A division is one bare `div` or `idiv` of its own size, with no guard
  ([ADR-2026-10-31-0050](adrs/2026-10-31-0050-division-is-one-bare-sized-div.md)),
  and at `i128` a call of a System V routine, with no guard either, of a
  hand-written helper that the module's object file carries under local
  symbols
  ([ADR-2026-11-03-0414](adrs/2026-11-03-0414-the-i128-division-helper-lives-in-the-module-s-object-file.md),
  [ADR-2026-11-03-0415](adrs/2026-11-03-0415-the-i128-division-routines-are-system-v-functions.md)).
  A `select` tests bit 0 of its condition and is one `cmov`, with no
  branch
  ([ADR-2026-10-31-0215](adrs/2026-10-31-0215-select-is-one-cmov-on-bit-0.md)).
  Blocks keep their order, a branch jumps unless its block comes next,
  and a `cond_br` tests bit 0 of its condition
  ([ADR-2026-10-31-0334](adrs/2026-10-31-0334-blocks-keep-their-order-and-branches-jump-to-labels.md)).
  A branch copies the values it passes into its block's arguments as one
  parallel move
  ([ADR-2026-10-31-0335](adrs/2026-10-31-0335-block-arguments-are-one-parallel-move.md)).
  A call follows System V and extends no argument
  ([ADR-2026-10-30-1232](adrs/2026-10-30-1232-funk-function-abi.md),
  [ADR-2026-11-02-1021](adrs/2026-11-02-1021-a-funk-caller-extends-no-argument.md)),
  and passes an `i128` in two registers or in 16 aligned bytes of the
  stack
  ([ADR-2026-11-03-0108](adrs/2026-11-03-0108-an-i128-passes-in-two-registers-or-sixteen-aligned-bytes.md)).
  Functions and calls return any number of results, as System V returns
  a structure: one or two eightbytes in `%rax` and `%rdx`, so one `i128`
  in `%rdx:%rax`, and more in a result area that the caller provides
  ([ADR-2026-11-03-0109](adrs/2026-11-03-0109-results-return-as-a-system-v-structure.md)).
  The executable runs one function from the command line and prints its
  results as JSON
  ([ADR-2026-10-30-1233](adrs/2026-10-30-1233-build-and-run-a-function.md)).
  It runs the function on a stack that covers every call the function
  makes, or for a recursive function up to the process's stack limit
  (`ulimit -s`), and a run that outgrows its stack says so in one line
  ([ADR-2026-11-02-1132](adrs/2026-11-02-1132-a-run-s-stack-covers-its-calls.md)).
- Generated programs and fuzzing
  ([#165](https://github.com/pmatos/funk/issues/165)).
  `./scripts/check-random-programs.sh` runs 500 generated programs on
  `fir-ref` and as native code on every pull request
  ([ADR-2026-11-08-2115](adrs/2026-11-08-2115-generated-programs-run-on-fir-ref-and-native-code.md)).
  A nightly workflow runs fresh seeds and fuzzes the Rust parser and verifier
  ([ADR-2026-11-08-2116](adrs/2026-11-08-2116-fresh-seeds-run-only-in-a-manual-stage-nightly-hook.md),
  [ADR-2026-11-08-2117](adrs/2026-11-08-2117-fuzz-the-rust-parser-and-verifier-without-a-sanitizer.md)).
- The differential harness ([#13](https://github.com/pmatos/funk/issues/13)).
  `./scripts/check-harness.sh` checks that `funk verify` and
  `fir-ref validate` give the same verdict on every text of
  [`tests/fir/`](../tests/fir/) and on modules from the Rust generator. It
  runs each test of the corpus on `fir-ref` and, where the backend can
  build it, as native code, and checks that the native result refines
  one of `fir-ref`'s outcomes. A test whose run chooses more than the
  choice budget declares its results, each with a witness that the
  harness checks, and seeded runs sample the rest
  ([ADR-2026-10-30-2049](adrs/2026-10-30-2049-differential-harness-in-python.md),
  [ADR-2026-10-30-2135](adrs/2026-10-30-2135-harness-judges-tests-by-refinement.md),
  [ADR-2026-10-31-0003](adrs/2026-10-31-0003-harness-judges-differential-tests-by-outcome-sets.md)).
  A test may pass `poison` as an argument, which `fir-ref run` takes as
  it is, and native code then runs on stand-ins in its place, the
  boundary bit patterns of its type
  ([#123](https://github.com/pmatos/funk/issues/123),
  [fir-ref.md](decisions/fir-ref.md#poison-arguments)).
- The execution rules of `const`, `add`, `sub`, `mul`, their flags, the
  bitwise ops and shifts, the width changes `zext`, `sext` and `trunc`,
  `freeze` and `ret` in Lean
  ([#10](https://github.com/pmatos/funk/issues/10),
  [#14](https://github.com/pmatos/funk/issues/14),
  [#15](https://github.com/pmatos/funk/issues/15),
  [#17](https://github.com/pmatos/funk/issues/17)). `fir-ref run` runs a
  function in scripted mode, along the path that its choices name, in
  exhaustive mode, which lists every outcome, or in sampled mode, which
  draws its choices from a seed; Lean proves all three sound
  ([fir-ref.md](decisions/fir-ref.md#the-tree-of-choices),
  [fir-ref-command-line.md](decisions/fir-ref-command-line.md#scripted-and-exhaustive-modes),
  [fir-ref-command-line.md](decisions/fir-ref-command-line.md#sampled-mode)).
- The execution rules of `sdiv`, `udiv`, `srem` and `urem`, with `exact`, in
  Lean ([#18](https://github.com/pmatos/funk/issues/18)). `fir-ref run`
  reports their immediate UB, a zero or poison divisor and the signed
  minimum or poison divided by `-1`, with a reason that names the case.
- The execution rules of `icmp`, with its ten predicates, and `select` in
  Lean ([#16](https://github.com/pmatos/funk/issues/16)).
- The execution rules of `br` and `cond_br` in Lean
  ([#19](https://github.com/pmatos/funk/issues/19)). `fir-ref run` runs
  functions with loops, and reports a branch on poison as immediate UB.
- The execution rules of `call` in Lean
  ([#20](https://github.com/pmatos/funk/issues/20)). `fir-ref run` runs
  any function of a module, named as text names it, and the functions it
  calls, recursion included. A callee runs on the fuel that its caller
  has left, so recursion without end runs out of fuel. Lean proves that
  no path of a run of a function of a valid module is stuck, and that the
  run has an outcome at every budget, and that a call refines when its
  arguments do, and when its callee's body is replaced so that the
  callee, run in the new module, refines the old one. Every core op
  instance that validation accepts meets the poison obligations
  (`LawfulDialectPoison CoreDialect`); a call has no op-level rule, since
  its meaning is its callee's run
  ([ADR-2026-11-02-1514](adrs/2026-11-02-1514-a-call-has-no-op-level-rule.md),
  [ADR-2026-11-02-1515](adrs/2026-11-02-1515-poison-obligations-cover-valid-op-instances.md)).
- The execution rule of `poison` in Lean
  ([#122](https://github.com/pmatos/funk/issues/122)): it gives the
  poison of its type on every run
  ([ADR-2026-11-03-1615](adrs/2026-11-03-1615-the-core-dialect-writes-poison-with-a-constant-op-that-propagates-poison.md)).
- A `fir-ref` that gives its verdict on a text nested to any depth and
  runs a function for any number of steps, with no stack per level of
  nesting, per step or per level of calls, that reads an operand in time
  that does not grow with the values defined after it, and that prints in
  time linear in the text it writes
  ([#47](https://github.com/pmatos/funk/issues/47)). It runs
  implementations of the spec's parser, readers, decoder, printer,
  validation walk and interpreter that are proved equal to them and
  registered with `@[csimp]`, on Lean's standard axioms only
  ([ADR-2026-10-30-1450](adrs/2026-10-30-1450-fir-ref-runs-proved-implementations.md),
  [how `fir-ref` runs the check](decisions/validation-fir-ref.md#how-fir-ref-runs-the-check),
  [fir-ref-fast-paths.md](decisions/fir-ref-fast-paths.md#lexing-and-reading),
  [fir-ref-fast-paths.md](decisions/fir-ref-fast-paths.md#running),
  [fir-ref-fast-paths.md](decisions/fir-ref-fast-paths.md#the-bindings-map)).
  On a 256 KiB stack, `scripts/check-fir-ref-deep.sh` checks `fir-ref fmt`
  and `fir-ref validate` on texts nested a million levels deep and on a
  block of a million ops, and `scripts/check-fir-ref-run.sh` checks
  `fir-ref run` on a loop and a recursion of a million steps.

The open sub-issues of [#177](https://github.com/pmatos/funk/issues/177) list
the parts of M1 that do not exist yet.
