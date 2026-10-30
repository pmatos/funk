# Funk

Funk is a compiler toolchain in the spirit of LLVM: a library to build
production compilers on. Its intermediate representation (IR) is called fir,
and fir has a formal semantics in Lean.

Funk is at an early stage. Today the repository holds fir's specification,
written in Lean, and the decisions behind it. It holds no compiler yet. See
[status](#status) for what exists and what does not.

## Goals and direction

Three documents set funk's direction. The [spec](docs/spec/) says what fir
is. The [roadmap](docs/roadmap.md) says what we build next, and in what order.
The [ADRs](docs/adrs/) record what we decided, and why. The glossary,
[`CONTEXT.md`](CONTEXT.md), defines the terms they use.

The roadmap sets these goals:

- **Verification first.** We will test the toolchain against fir's Lean
  semantics and, over time, prove it correct.
- **Agent native.** Agents build funk and are meant to use it. Its core should
  fit in an agent's context, and its tools should report in JSON as well as in
  text.
- **Any hardware.** fir must be able to reach any kind of hardware. CPUs come
  first. Other targets are meant to come in as extension dialects.

Its ground rules also fix these points:

- The semantics of fir lives in Lean, and only there. A Lean reference
  interpreter will serve as a test oracle. It never ships inside a compiler.
- The toolchain is to be written in Rust. Each piece of Rust will be either
  generated from Lean or checked against it.
- The fir text format is the interface between Lean and Rust. Both sides must
  print a module as the same bytes.
- A compiled program is correct when it refines its source: each of its
  observable behaviours is one the source allows.

Some decisions are still open, such as the memory model, floating point,
concurrency and how dialects are defined. The roadmap lists them under
[decisions deferred past M0](docs/roadmap.md#decisions-deferred-past-m0). No
work should assume an answer to any of them.

## What fir looks like

This function comes from the example in the spec's text-format chapter. It
adds the integers from 0 up to, but not including, `%n`. Each op ends with a
location reference such as `@1`. A `locs` table at the end of the module,
not shown here, gives the location that each reference stands for.

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

The roadmap plans seven milestones, and each one is a GitHub milestone. M0 is
in progress. M1 to M6 have not started.

| Milestone | Goal |
| --- | --- |
| M0 | fir compiler with a basic x86-64 backend |
| M1 | Full x86-64 backend |
| M2 | Vow frontend |
| M3 | C and C++ frontend |
| M4 | Compile the Linux kernel |
| M5 | JIT compilation |
| M6 | x86 to arm64 binary translation |

The M0 epic, [#5](https://github.com/pmatos/funk/issues/5), tracks M0 and its
sub-issues. These parts of M0 are on `main`:

- The decisions that M0 starts from, each recorded as an ADR.
- A [spike report](docs/spikes/leanmlir.md) that compared two ways to write
  fir's Lean semantics: on top of LeanMLIR, or as fir's own calculus. The
  human who guides funk chose fir's own calculus
  ([ADR-2026-10-29-2030](docs/adrs/2026-10-29-2030-fir-lean-semantics-own-calculus.md)).
- The fir v0 spec, as literate Lean in `lean/`, rendered with Verso from
  `docs/spec/`. It gives fir's abstract syntax and validation rules, the
  general definitions of execution (outcomes, observable behaviour and
  refinement), and the text format with its grammar and printer. CI builds
  it on every pull request.

These parts of M0 do not exist yet:

- The execution rules of the ops. The issue for each op family adds them.
- The Lean parser and the reference interpreter, `fir-ref`.
- The proof that parsing a printed module gives the module back.
- Any Rust code: the IR crate `funk-ir`, the `funk` driver and the x86-64
  backend.
- The differential tests that compare native results with `fir-ref`.

The epic lists the open work in full.

## Repository layout

| Path | Contents |
| --- | --- |
| `lean/` | The Lake package `fir`: the spec's chapters as literate Lean modules |
| `docs/spec/` | The Lake package `firspec`: the Verso document that renders the spec |
| `docs/roadmap.md` | The roadmap: milestones M0 to M6 |
| `docs/adrs/` | The ADRs, one decision per file, and how to write one |
| `docs/spikes/` | Spike reports |
| `docs/agents/` | How agents use the issue tracker, the triage labels and the domain docs |
| `scripts/` | Scripts for the spec build, the hooks and agent sessions |
| `.github/` | The CI workflows, the ruleset for `main` and the Dependabot settings |
| `.pre-commit-config.yaml` | Every check, for the local hooks and for CI |
| `.claude/settings.json` | Claude Code settings, which install the git hooks when a session starts |
| `CONTEXT.md` | The glossary |
| `AGENTS.md` | How the project is built, and the rules for every change |
| `LICENSE` | The MIT License |

## Build the spec

You need `elan`, the Lean toolchain manager, to build the spec. Install it as
the [elan README](https://github.com/leanprover/elan#installation) says. You
also need `pre-commit` 4.4.0 or later for the hooks and checks.

```sh
git clone https://github.com/pmatos/funk.git
cd funk
./scripts/ensure-hooks.sh   # install the git hooks
scripts/build-spec.sh       # build the Lean code and render the spec
```

Then open `docs/spec/_out/html-multi/index.html` in a browser. elan uses the
Lean version that `lean/lean-toolchain` pins. The first build in a clone also
builds Verso, so it takes longer. The rendered spec is a build output, and git
ignores it. [`docs/spec/README.md`](docs/spec/README.md) has more detail.

Issue [#28](https://github.com/pmatos/funk/issues/28) tracks publishing the
rendered spec on GitHub Pages. Until that is done, build the spec locally to
read it.

## How funk is built

A human sets the direction: the spec, the roadmap, and the calls only they can
make. Agents do the rest: design, code, tests, docs, ADRs, reviews and pull
requests. [`AGENTS.md`](AGENTS.md) gives the full rules. In short:

- Every change reaches `main` as a squash-merged pull request. A ruleset
  blocks direct pushes to `main`, for everyone.
- A pull request merges only when the `pre-commit` and `PR title` checks pass.
- Run `./scripts/ensure-hooks.sh` in each clone before you work in it. It
  installs the `pre-commit` and `commit-msg` hooks. Never bypass them.
- Write commit messages and pull request titles as Conventional Commits, such
  as `docs: add a readme`. The title becomes the commit message on `main`.
- Keep every text file at most 20,000 bytes, so that an agent can read any
  file whole. Split a file that grows past that by responsibility.
- Run `pre-commit run --all-files` before you push. CI runs the same checks.
- Record every significant decision as an ADR in `docs/adrs/`.
- A change to the spec or the roadmap is a direction call. Propose it in its
  own pull request, and flag it for the human.

To report a bug or propose work, open a
[GitHub issue](https://github.com/pmatos/funk/issues). The project triages
issues, not pull requests.

## Licence

Funk is licensed under the MIT License. See [`LICENSE`](LICENSE).
