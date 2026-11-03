# Funk

Funk is a compiler toolchain in the spirit of LLVM: a library to build
production compilers on. Its intermediate representation (IR) is called fir.
fir's meaning is being defined formally in [Lean](https://lean-lang.org), a
proof assistant.

Two aims shape funk. First, funk's code will be checked against fir's formal
definition. Second, agents build funk, and they are meant to use it.

Funk is at an early stage. Today the repository holds fir's specification,
written in Lean, and the decisions behind it. It also holds the first Rust
code: a library that reads, prints and checks fir, a naive x86-64 backend,
and a driver, `funk`, that compiles fir to an executable for x86-64 Linux.
See [status](#status) for what exists and what does not. Agents should read
[`AGENTS.md`](AGENTS.md) before they start a task.

## Goals and direction

Three documents set funk's direction:

- The [spec](docs/spec/) says what fir is. It is written in Lean, and its
  chapters are in [`lean/Fir/`](lean/Fir/). Read it as a web page at
  <https://p.ocmatos.com/funk/>, or build it as
  [Build the spec](#build-the-spec) shows.
- The [roadmap](docs/roadmap.md) says what we build next, and in what order.
- The [architecture decision records (ADRs)](docs/adrs/) say what we decided,
  and why. The spec's web page holds them too, as an appendix at
  <https://p.ocmatos.com/funk/adrs/>, and every ADR it cites is a link.

The glossary, [`CONTEXT.md`](CONTEXT.md), defines the terms they use.

The roadmap sets these goals:

- **Verification first.** We will test the toolchain against fir's Lean
  semantics and, over time, prove it correct.
- **Agent native.** Agents build funk and are meant to use it. Its core should
  fit in an agent's context, and its tools should report in JSON as well as in
  text.
- **Any hardware.** fir must be able to reach any kind of hardware. CPUs come
  first. Other targets are meant to come in as extension dialects.

The roadmap's ground rules also settle these points:

- The semantics of fir lives in Lean, and only there. A Lean reference
  interpreter will serve as a test oracle. It never ships inside a compiler.
- The toolchain is to be written in Rust. Each piece of Rust will be either
  generated from Lean or checked against it.
- The fir text format is the interface between Lean and Rust. Both sides must
  print a module as the same bytes.
- A compiled program is correct when it refines its source: each of its
  observable behaviours is one the source allows.

Some decisions are still open, such as the memory model, floating point,
concurrency, and how dialects and extensions are defined. The roadmap lists
them under [decisions deferred past M0](docs/roadmap.md#decisions-deferred-past-m0).
M0 is funk's first milestone. No work should assume an answer to any of these
decisions.

## What fir looks like

This function comes from the spec's example,
[`lean/Fir/Text/Example.lean`](lean/Fir/Text/Example.lean). It adds the
integers from 0 up to, but not including, `%n`. Each op ends with a location
reference such as `@1`. The full module ends with a `locs` table, not shown
here. That table gives the source location that each reference stands for.

```
func @sum(%n: i32) -> i32 {
^entry:
  %zero: i32 = const 0 @1
  br ^loop(%zero, %zero) @1
^loop(%i: i32, %acc: i32):
  %done: i1 = icmp sge %i, %n @2
  cond_br %done, ^exit(%acc), ^body @2
^body:
  %acc1: i32 = add nsw %acc, %i @3
  %one: i32 = const 1 @3
  %i1: i32 = add nsw %i, %one @3
  br ^loop(%i1, %acc1) @3
^exit(%r: i32):
  ret %r @4
}
```

## Status

The roadmap plans seven milestones, and each one is a
[GitHub milestone](https://github.com/pmatos/funk/milestones). M0 is in
progress. M1 to M6 have not started.

| Milestone | Goal |
| --- | --- |
| M0 | fir compiler with a basic x86-64 backend |
| M1 | Full x86-64 backend |
| M2 | [Vow](https://github.com/vow-lang/vow) frontend |
| M3 | C and C++ frontend |
| M4 | Compile the Linux kernel |
| M5 | JIT compilation |
| M6 | x86 to arm64 binary translation |

Issue [#5](https://github.com/pmatos/funk/issues/5) is the M0 epic. Its
sub-issues track the work of M0, one issue for each piece. These parts of M0
are on `main`:

- The decisions that M0 starts from, each recorded as an ADR.
- A [spike report](docs/spikes/leanmlir.md) that compared two ways to write
  fir's Lean semantics. One builds on
  [LeanMLIR](https://github.com/opencompl/lean-mlir), an SSA framework in
  Lean. The other is fir's own calculus. The project's human lead chose fir's
  own calculus
  ([ADR-2026-10-29-2030](docs/adrs/2026-10-29-2030-fir-lean-semantics-own-calculus.md)).
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
  ([ADR-2026-10-30-1146](docs/adrs/2026-10-30-1146-generic-ops-and-registry.md)),
  and the core dialect registers `const`, `add`, `sub`, `mul`, their flags
  `nuw` and `nsw`, `freeze`, the bitwise ops `and`, `or` and `xor`, the
  shifts `shl`, `lshr` and `ashr`, the width changes `zext`, `sext` and
  `trunc`, `sdiv` and `udiv` with their flag `exact`, `srem`, `urem`,
  `icmp` with its ten predicates, `select`, the branches `br` and
  `cond_br`, `ret`, and `call` of any function of the module, with any
  number of arguments and results
  ([#14](https://github.com/pmatos/funk/issues/14),
  [#15](https://github.com/pmatos/funk/issues/15),
  [#16](https://github.com/pmatos/funk/issues/16),
  [#17](https://github.com/pmatos/funk/issues/17),
  [#18](https://github.com/pmatos/funk/issues/18),
  [#19](https://github.com/pmatos/funk/issues/19),
  [#20](https://github.com/pmatos/funk/issues/20)). The verifier checks
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
  `const`, `add`, `sub` and `mul` with their flags, `freeze`, the bitwise
  ops and shifts, `zext`, `sext`, `trunc`, `sdiv` and `udiv` with or
  without `exact`, `srem`, `urem`, `icmp`, `select`, `br`, `cond_br`,
  `ret` and `call` at `i1`, `i8`, `i16`, `i32`, `i64` and `i128` into
  an object file and an executable for Linux. An
  `i128` is a pair of eightbytes, and each op lowers it through a pair of
  registers
  ([ADR-2026-11-03-010730](docs/adrs/2026-11-03-010730-an-i128-is-a-pair-of-eightbytes.md)).
  Native code holds no poison: a broken `nuw` or `nsw` gives the
  wrapped result, a broken `exact` the plain quotient, a shift by `N` or
  more gives what x86's masked shift gives (at `i128`, what the pair's
  shift sequence gives for the amount's low 7 bits), and `freeze` copies
  its operand
  ([ADR-2026-10-30-2248](docs/adrs/2026-10-30-2248-native-code-holds-no-poison.md)).
  A division is one bare `div` or `idiv` of its own size, with no guard
  ([ADR-2026-10-31-0050](docs/adrs/2026-10-31-0050-division-is-one-bare-sized-div.md)),
  and at `i128` a call of a System V routine, with no guard either, of a
  hand-written helper that the module's object file carries under local
  symbols
  ([ADR-2026-11-03-0414](docs/adrs/2026-11-03-0414-the-i128-division-helper-lives-in-the-module-s-object-file.md),
  [ADR-2026-11-03-0415](docs/adrs/2026-11-03-0415-the-i128-division-routines-are-system-v-functions.md)).
  A `select` tests bit 0 of its condition and is one `cmov`, with no
  branch
  ([ADR-2026-10-31-0215](docs/adrs/2026-10-31-0215-select-is-one-cmov-on-bit-0.md)).
  Blocks keep their order, a branch jumps unless its block comes next,
  and a `cond_br` tests bit 0 of its condition
  ([ADR-2026-10-31-0334](docs/adrs/2026-10-31-0334-blocks-keep-their-order-and-branches-jump-to-labels.md)).
  A branch copies the values it passes into its block's arguments as one
  parallel move
  ([ADR-2026-10-31-0335](docs/adrs/2026-10-31-0335-block-arguments-are-one-parallel-move.md)).
  A call follows System V and extends no argument
  ([ADR-2026-10-30-1232](docs/adrs/2026-10-30-1232-funk-function-abi.md),
  [ADR-2026-11-02-1021](docs/adrs/2026-11-02-1021-a-funk-caller-extends-no-argument.md)),
  and passes an `i128` in two registers or in 16 aligned bytes of the
  stack
  ([ADR-2026-11-03-0108](docs/adrs/2026-11-03-0108-an-i128-passes-in-two-registers-or-sixteen-aligned-bytes.md)).
  Functions and calls return any number of results, as System V returns
  a structure: one or two eightbytes in `%rax` and `%rdx`, so one `i128`
  in `%rdx:%rax`, and more in a result area that the caller provides
  ([ADR-2026-11-03-0109](docs/adrs/2026-11-03-0109-results-return-as-a-system-v-structure.md)).
  The executable runs one function from the command line and prints its
  results as JSON
  ([ADR-2026-10-30-1233](docs/adrs/2026-10-30-1233-build-and-run-a-function.md)).
  It runs the function on a stack that covers every call the function
  makes, or for a recursive function up to the process's stack limit
  (`ulimit -s`), and a run that outgrows its stack says so in one line
  ([ADR-2026-11-02-1132](docs/adrs/2026-11-02-1132-a-run-s-stack-covers-its-calls.md)).
- The differential harness ([#13](https://github.com/pmatos/funk/issues/13)).
  `./scripts/check-harness.sh` checks that `funk verify` and
  `fir-ref validate` give the same verdict on every text of
  [`tests/fir/`](tests/fir/) and on modules from the Rust generator. It
  runs each test of the corpus on `fir-ref` and, where the backend can
  build it, as native code, and checks that the native result refines
  one of `fir-ref`'s outcomes. A test whose run chooses more than the
  choice budget declares its results, each with a witness that the
  harness checks, and seeded runs sample the rest
  ([ADR-2026-10-30-2049](docs/adrs/2026-10-30-2049-differential-harness-in-python.md),
  [ADR-2026-10-30-2135](docs/adrs/2026-10-30-2135-harness-judges-tests-by-refinement.md),
  [ADR-2026-10-31-0003](docs/adrs/2026-10-31-0003-harness-judges-differential-tests-by-outcome-sets.md)).
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
  ([ADR-2026-10-30-2217](docs/adrs/2026-10-30-2217-choice-tree-denotes-the-set-monad.md),
  [ADR-2026-10-30-2218](docs/adrs/2026-10-30-2218-fir-ref-run-modes.md),
  [ADR-2026-10-31-0002](docs/adrs/2026-10-31-0002-fir-ref-run-draws-choices-from-a-seed.md)).
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
  ([ADR-2026-11-02-1514](docs/adrs/2026-11-02-1514-a-call-has-no-op-level-rule.md),
  [ADR-2026-11-02-1515](docs/adrs/2026-11-02-1515-poison-obligations-cover-valid-op-instances.md)).

These parts of M0 do not exist yet:

- A `fir-ref` that reads texts nested to any depth: today its readers
  overflow their stack on texts nested millions of levels deep
  ([#47](https://github.com/pmatos/funk/issues/47)).

The epic's sub-issues list the open work in full.

## Repository layout

| Path | Contents |
| --- | --- |
| `lean/` | The Lean package `fir`: the spec's chapters as Lean modules with prose, `fir-ref` and the Lean tests |
| `docs/spec/` | The Lean package `firspec`: the Verso document that renders the spec |
| `docs/roadmap.md` | The roadmap: milestones M0 to M6 |
| `docs/adrs/` | The ADRs, one decision per file, and how to write one |
| `docs/spikes/` | Spike reports |
| `docs/agents/` | How agents use the issue tracker, the triage labels and the domain docs |
| `crates/` | The Rust crates: `funk-ir`, the IR library, `funk-x86-64`, the x86-64 backend, `funk-start-fds`, which records the standard descriptors that were closed at start-up, and `funk`, the driver |
| `tests/fir/` | The test corpus that the Rust and Lean sides share: canonical texts and their tests, inputs that format to them, and must-reject texts |
| `Cargo.toml`, `Cargo.lock` | The Cargo workspace and its locked dependencies |
| `rust-toolchain.toml` | The pinned Rust toolchain |
| `scripts/` | Scripts for the spec build, the Rust checks, the differential harness (`scripts/harness/`), the hooks and agent sessions |
| `.github/` | The CI and Pages workflows, the ruleset for `main` and the Dependabot settings |
| `.pre-commit-config.yaml` | Every check, for the local hooks and for CI |
| `.claude/settings.json` | Claude Code settings, which install the git hooks when a session starts |
| `CONTEXT.md` | The glossary |
| `AGENTS.md` | How the project is built, and the rules for every change |
| `LICENSE` | The MIT License |

## Build the spec

You need `elan`, the Lean toolchain manager, to build the spec. Install it as
the [elan README](https://github.com/leanprover/elan#installation) says. Then
run:

```sh
git clone https://github.com/pmatos/funk.git
cd funk
./scripts/build-spec.sh   # build the Lean code and render the spec
```

Open `docs/spec/_out/html-multi/index.html` in a browser to read the spec.
The build also makes `lean/.lake/build/bin/fir-ref` and runs the Lean tests;
`./scripts/build-spec.sh --lean` does only that.
elan uses the Lean version that `lean/lean-toolchain` pins. The first build in
a clone also builds Verso, so it takes longer. The rendered spec is a build
output, and git ignores it. [`docs/spec/README.md`](docs/spec/README.md) has
more detail.

The rendered spec is also published at <https://p.ocmatos.com/funk/>. It is
rebuilt and deployed from every push to `main`
([ADR-2026-10-30-1031](docs/adrs/2026-10-30-1031-publish-spec-to-github-pages.md)),
and each page names the commit it was built from.

## Build funk

You need `rustup`, the Rust toolchain manager, to build funk. Install it as
<https://rustup.rs> says. `funk build` and the tests also need GNU binutils
(`as` and `ld`) on an x86-64 Linux machine. Then run, in a clone:

```sh
cargo build --release                          # build the crates and funk
cargo test --workspace                         # run the tests
./target/release/funk verify tests/fir/canonical/add.fir
./target/release/funk build -o target/add tests/fir/canonical/add.fir
./target/add @add3 1 2 3                       # prints {"values":["6"]}
```

rustup installs the Rust version that `rust-toolchain.toml` pins the first
time cargo runs. `funk fmt FILE` prints a file in its canonical form;
`--check` lists the files that are not canonical, and `--write` rewrites
them. `funk verify FILE` checks a file, and prints nothing when it is valid.
`funk build -o OUTPUT FILE` compiles a file into the object file `OUTPUT.o`
and the executable `OUTPUT`, which runs one function: `OUTPUT @FUNCTION ARG...`.
`--json` reports one JSON line per file. `funk --help` lists the options.
[ADR-2026-10-30-1032](docs/adrs/2026-10-30-1032-funk-reports.md) and
[ADR-2026-10-30-1326](docs/adrs/2026-10-30-1326-funk-build-command.md)
give the reports and exit codes, and
[ADR-2026-10-30-1233](docs/adrs/2026-10-30-1233-build-and-run-a-function.md)
how the executable is run.

## How to contribute

A human sets the direction: the spec, the roadmap, and the calls only they can
make. Agents do the rest: design, code, tests, docs, ADRs, reviews and pull
requests. [`AGENTS.md`](AGENTS.md) gives the full rules.

Before you work in a clone, install `pre-commit` 4.4.0 or later. Install
`elan` and `rustup` too, GNU binutils on an x86-64 Linux host, Verus for the
`verus-proof` check (see `AGENTS.md`), and Python 3.11 or later. Four checks need elan: `fir-spec` builds the spec,
`fir-ref-test` runs the Lean tests, `fir-round-trip` has Lean reprint what
Rust prints, and `fir-harness` runs the differential harness. Five need
rustup: `rust-fmt`, `rust-clippy` and `rust-test` check the Rust code, and
`fir-round-trip` and `fir-harness` run it. `rust-test` and `fir-harness`
build and run native code, so they need binutils. Then install the git
hooks:

```sh
./scripts/ensure-hooks.sh   # install the pre-commit and commit-msg hooks
```

The rules, in short:

- Every change reaches `main` as a squash-merged pull request. A ruleset
  blocks direct pushes to `main`, for everyone.
- A pull request merges only when the `pre-commit` and `PR title` checks pass.
- Never bypass the hooks.
- Write commit messages and pull request titles as Conventional Commits, such
  as `docs: add a readme`. The title becomes the commit message on `main`.
- Keep every text file at most 20,000 bytes, so that an agent can read any
  file whole. Split a file that grows past that by responsibility.

To report a bug or propose work, open a
[GitHub issue](https://github.com/pmatos/funk/issues). Only issues are
triaged: a pull request is not treated as a request for work.

## Licence

Funk is licensed under the MIT License. See [`LICENSE`](LICENSE).
