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
See [`docs/status.md`](docs/status.md) for what exists and what does not.
Agents should read [`AGENTS.md`](AGENTS.md) before they start a task.

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

The roadmap plans eight milestones, and each one is a
[GitHub milestone](https://github.com/pmatos/funk/milestones). M0 is done.
M1 has started, and M2 to M7 have not.

| Milestone | Goal |
| --- | --- |
| M0 | fir compiler with a basic x86-64 backend |
| M1 | Complete the fir IR |
| M2 | Full x86-64 backend |
| M3 | [Vow](https://github.com/vow-lang/vow) frontend |
| M4 | C and C++ frontend |
| M5 | Compile the Linux kernel |
| M6 | JIT compilation |
| M7 | x86 to arm64 binary translation |

Issue [#177](https://github.com/pmatos/funk/issues/177) is the M1 epic. Its
sub-issues track the work of M1, one issue for each piece. Issue
[#5](https://github.com/pmatos/funk/issues/5) was the M0 epic.
[`docs/status.md`](docs/status.md) lists what is on `main` today.

## Repository layout

| Path | Contents |
| --- | --- |
| `lean/` | The Lean package `fir`: the spec's chapters as Lean modules with prose, `fir-ref` and the Lean tests |
| `docs/spec/` | The Lean package `firspec`: the Verso document that renders the spec |
| `docs/roadmap.md` | The roadmap: milestones M0 to M7 |
| `docs/status.md` | What exists on `main` today, and what does not |
| `docs/adrs/` | The ADRs, one decision per file, and how to write one |
| `docs/spikes/` | Spike reports |
| `docs/agents/` | How agents use the issue tracker, the triage labels and the domain docs |
| `crates/` | The Rust crates: `funk-ir`, the IR library, `funk-x86-64`, the x86-64 backend, and `funk`, the driver |
| `tests/fir/` | The test corpus that the Rust and Lean sides share: canonical texts and their tests, inputs that format to them, must-reject texts, and cases ported from LLVM |
| `Cargo.toml`, `Cargo.lock` | The Cargo workspace and its locked dependencies |
| `rust-toolchain.toml` | The pinned Rust toolchain |
| `scripts/` | Scripts for the spec build, the Rust checks, the differential harness and the fir explorer (`scripts/harness/`), the hooks and agent sessions |
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
`funk asm FILE` prints the assembly of its functions.
`--json` reports one JSON line per file. `funk --help` lists the options.
[ADR-2026-10-30-1032](docs/adrs/2026-10-30-1032-funk-reports.md) and
[ADR-2026-10-30-1326](docs/adrs/2026-10-30-1326-funk-build-command.md)
give the reports and exit codes, and
[ADR-2026-10-30-1233](docs/adrs/2026-10-30-1233-build-and-run-a-function.md)
how the executable is run.

## Explore fir in a browser

The fir explorer is a local web app, in the manner of Compiler Explorer. Write
fir and see whether Rust and Lean accept it, its round trip, its x86-64
assembly, the outcomes of a run on `fir-ref`, and whether native code refines
them. It needs what the spec and funk need, and Python 3.11 or later:

```sh
./scripts/explorer.sh                # build the tools and start the explorer
./scripts/explorer.sh --no-build     # start it with the tools already built
```

Then open <http://127.0.0.1:8017/>. It compiles and runs what you type, so it
listens only on this machine. `--port` and `--timeout` change its port and the
seconds that a tool or a native program may run.

## How to contribute

A human sets the direction: the spec, the roadmap, and the calls only they can
make. Agents do the rest: design, code, tests, docs, ADRs, reviews and pull
requests. [`AGENTS.md`](AGENTS.md) gives the full rules.

Before you work in a clone, install `pre-commit` 4.4.0 or later, `elan`,
`rustup`, GNU binutils on an x86-64 Linux host, and Python 3.11 or
later. Four checks need elan: `fir-spec` builds the spec, `fir-ref-test`
runs the Lean tests, `fir-round-trip` has Lean reprint what Rust prints,
and `fir-harness` runs the differential harness. Five need rustup:
`rust-fmt`, `rust-clippy` and `rust-test` check the Rust code, and `fir-round-trip` and `fir-harness` run it. `rust-test` and
`fir-harness` build native code, so they need binutils. Then install the
git hooks:

```sh
./scripts/ensure-hooks.sh   # install the pre-commit and commit-msg hooks
```

The rules, in short:

- Every change reaches `main` as a squash-merged pull request. A ruleset
  blocks direct pushes to `main`, for everyone.
- A pull request merges only when it is up to date with `main` and the
  `pre-commit` and `PR title` checks pass.
- Never bypass the hooks.
- Write commit messages and pull request titles as Conventional Commits, such
  as `docs: add a readme`. The title becomes the commit message on `main`.
- Keep every text file at most 20,000 bytes, so that an agent can read any
  file whole. Split a file that grows past that by responsibility.

To report a bug or propose work, open a
[GitHub issue](https://github.com/pmatos/funk/issues). Only issues are
triaged: a pull request is not treated as a request for work.

## Licence

Funk is licensed under the MIT License. See [`LICENSE`](LICENSE). The cases in
`tests/fir/llvm/` are under [LLVM's licence](tests/fir/llvm/README.md).
