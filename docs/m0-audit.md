# M0 audit: the evidence that #23's criteria and #5's "Done when" items hold

This file records the evidence that the acceptance criteria of
[#23](https://github.com/pmatos/funk/issues/23) and the four "Done when"
items of the M0 epic, [#5](https://github.com/pmatos/funk/issues/5), hold.
Four stages of #23 built what it checks: the spec against Lean and the
Rust side against the spec
([#113](https://github.com/pmatos/funk/pull/113)), the G0 check
([#114](https://github.com/pmatos/funk/pull/114)), the coverage matrix
([#115](https://github.com/pmatos/funk/pull/115)) and the ports of LLVM
tests ([#116](https://github.com/pmatos/funk/pull/116)). It records
evidence, not a decision, so it is not an ADR.

It was checked against `main` at `ca5fd9f`, the merge of #116. There,
every item held but two points, which the pull request that adds this
file, [#119](https://github.com/pmatos/funk/pull/119), mends:

- `tracer-i128`, a module at a width that the backend lowers, had only
  interpreter-only tests, so CI never ran it as native code (item 2).
  #119 adds its differential tests.
- No ADR recorded the human's ruling N3, which caps widths, so S2's ADR
  read wider than the spec (item 1). #119 adds ADR-2026-11-03-1000.

Line numbers are those of `ca5fd9f`; #119 changes none of the files they
point into. Corpus counts include #119's tests. #5 stayed open after #23
closed, until 2026-11-05: see the last section.

Addendum, 2026-11-03: [#122](https://github.com/pmatos/funk/issues/122)
came after this audit and changes five of its facts; the evidence below
is that of `ca5fd9f`, and #122 did not check it again. The core op set
has 25 ops: `poison` is a constant whose result is poison, of class
`propagates`, so 19 ops propagate and six are exceptions, and S1 and
ADR-2026-10-30-0818 are also refined by ADR-2026-11-03-1615. The
coverage matrix has 783 cells, each with a test (ADR-2026-11-03-0557).
The LLVM ports write LLVM's poison constant with `poison`, not
`shl %n, %n`
([testing-and-harness-corpus.md](decisions/testing-and-harness-corpus.md#how-cases-are-chosen-and-rewritten)). `poison` is a core word for the G0
checks (ADR-2026-11-03-1617).

Addendum, 2026-11-05: the close-out of #5 checked this audit again on
`main` at `28b6f37`, after all 43 sub-issues of #5 had closed, and found
every "Done when" item met; the
[rulings comment](https://github.com/pmatos/funk/issues/5#issuecomment-6506908304)
on #5 records its result. The figures below stay those of `ca5fd9f`.
At `28b6f37`, `scripts/check-harness.sh` ends with
`20818 checks: 20818 passed, 0 failed, 0 invalid`: 277 corpus texts
(273 modules and 4 non-canonical inputs), 877 modules that Rust printed
(600 from its generator and the 277 texts), 496 must-reject texts,
11,427 differential tests and 7,741 interpreter-only tests. The core op
set has 25 ops, and the coverage matrix 783 cells, each with a test.
`.github/workflows/ci.yml` runs `pre-commit run --all-files` at line
109, and CI run 42014416532 passed every hook at `28b6f37`. #117 added
four hooks in PR #118: `verus-proof`, `verus-report-test`, `unsafe-code`
and `unsafe-code-test` (ADR-2026-11-03-0808; the Verus pin is now on
[rust-ir-and-tools.md](decisions/rust-ir-and-tools.md#unsafe-code)). S7's
ADR is now refined by ADR-2026-10-29-2030, and H8's ADR,
ADR-2026-10-29-2013, now also records the human's choice 16, the spelling
of a source range.

## The Lean criteria

#23 asks that Lean have, with no `sorry`, the five items of the first
column. Each is on `main`:

| Criterion | Lean declaration | Where |
| --- | --- | --- |
| `LawfulDialectText CoreDialect` | `Fir.Core.lawfulDialectText`, and the instance `Fir.instLawfulDialectTextCoreDialect` made from it | `lean/Fir/Core/TextLaws.lean:348`, `:357` |
| `LawfulDialectPoison CoreDialect` | `Fir.Core.lawfulDialectPoison`, and the instance `Fir.instLawfulDialectPoisonCoreDialect` | `lean/Fir/Core/Lawful.lean:99`, `:106` |
| #11's proof of `PrintThenParse` | `Fir.printThenParse`, for every dialect whose text is lawful, and `Fir.Core.printThenParse` | `lean/Fir/Text/PrintParse.lean:51`, `:90`; the property is at `lean/Fir/Text/RoundTrip.lean:117` |
| `ValidIsWellFormed` for the core dialect, through `validIsWellFormed` | `Fir.Core.validIsWellFormed`, defined as `Fir.validIsWellFormed` | `lean/Fir/Core/TextLaws.lean:360`, `lean/Fir/Text/RoundTrip.lean:188`; the property is at `RoundTrip.lean:145` |
| `FuelMonotone`, `Progress` and `NeverStuck` for every valid function | `Fir.Core.fuelMonotone`, `Fir.Core.progress` and `Fir.Core.neverStuck`, from `Fir.Core.runsWell` | `lean/Fir/Core/ValidRuns.lean:90`, `:96`, `:102`, `:81`; the properties are at `lean/Fir/Execution/Fuel.lean:77`, `:87`, `:91` |

`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for each
of the 12 declarations of the second column, `Fir.Core.runsWell`
included: Lean's three standard axioms, with no `sorryAx` and no axiom of
native evaluation. To run it, build `lean/` with
`scripts/build-spec.sh --lean`, then run Lean 4.35.0's `lean`, with
`LEAN_PATH=lean/.lake/build/lib/lean`, on a file outside `lean/` that
imports `Fir` and prints the axioms of each name.

The check that keeps this true is `#check_axioms`, the last command of
`lean/FirTest.lean`. It fails the build of `lean/` when any of its
declarations depends on an axiom other than the three standard ones and
the axioms of native evaluation that it confirms by running their claims
again, so `sorryAx` fails it, and `lake build --wfail` fails on a `sorry` in
an `example` (ADR-2026-10-30-1452). The `fir-spec`
hook runs both on every pull request. The word `sorry` appears in `lean/`
only in the prose of `lean/FirTest/Axioms.lean`.

What the statements cover, against the criteria's words:

- `Core.fuelMonotone`, `Core.progress` and `Core.neverStuck` assume
  `M.Valid` and `f ∈ M.funcs`, and hold for every argument vector of
  `f`'s parameter types, poison included. So they hold for every function
  of every valid core module, branches, loops, calls and recursion
  included. They need the whole module to be valid, not only `f`, since a
  call runs its callee. The narrower theorems for #10's tracer subset
  (`Core.tracer_*`) and for functions with no call (`Core.callFree_*`)
  came first; they are not the evidence.
- `PrintThenParse` is about well-formed modules (ADR-2026-10-29-2014).
  Every valid module is well formed, so it holds for valid modules too
  (`Module.Valid.parse_print`, `lean/Fir/Text/PrintParse.lean:78`).
  `fir-ref` parses with `FirRef.parse`, which `FirRef.parse_eq_parse`
  proves equal to the spec's `Fir.parse` (ADR-2026-10-30-1450).
- `lean/FirTest/G0.lean` restates `PrintThenParse`, `ValidIsWellFormed`,
  `FuelMonotone`, `NeverStuck` and `Progress` for any dialect, so a change
  that narrows them to the core dialect fails the build (#114).

No item is missing, and none is weaker than #23 states it.

## Epic #5's "Done when" items

### 1. Every decision is an accepted ADR, and the spec is complete and rendered in CI

| Decision of #5 | ADR | Status line |
| --- | --- | --- |
| E0, effect ordering | ADR-2026-10-29-2005 | accepted |
| S1, poison and `freeze` | ADR-2026-10-29-2006 | accepted; refined by ADR-2026-10-30-0818 |
| S2, integers `iN` | ADR-2026-10-29-2007 | accepted; refined by ADR-2026-11-03-1000 |
| S4, refinement | ADR-2026-10-29-2008 | accepted; refined by ADR-2026-10-30-0816 |
| S7, semantics in Lean | ADR-2026-10-29-2009 | accepted |
| H1, block arguments | ADR-2026-10-29-2010 | accepted |
| H2, isolated from above | ADR-2026-10-29-2011 | accepted |
| H3, globals by symbol | ADR-2026-10-29-2012 | accepted |
| H8, source locations | ADR-2026-10-29-2013 | accepted |
| P3, one text format | ADR-2026-10-29-2014 | accepted |
| P1, literate Lean spec | ADR-2026-11-05-2012, which holds P1 now | accepted |
| G0, any hardware | ADR-2026-10-29-2016 | accepted; refined by ADR-2026-10-30-1146 and ADR-2026-11-03-0600 |

The decisions that the epic's work list asks for are ADRs too: `freeze`
in the oracle (ADR-2026-10-29-2017), fir's own Lean calculus after the
spike of #24 (ADR-2026-10-29-2030), assembly through GNU `as` and `ld`
(ADR-2026-10-30-1229) and spilling every value (ADR-2026-10-30-1230).
None of these ADRs is superseded.

S2's ADR says that the IR and the Lean interpreter accept any `N >= 1`,
but the human's ruling N3 (part 3 of the rulings on #8, 2026-10-30, in
the [rulings comment](https://github.com/pmatos/funk/issues/5#issuecomment-6506908304)
on #5) caps widths at 16,777,215, MLIR's limit. Lean (`maxWidth`,
`lean/Fir/Core/Types.lean:30`) and Rust (`MAX_WIDTH`,
`crates/funk-ir/src/dialects/core/types.rs:13`) follow N3, but no ADR
held it until #119 added ADR-2026-11-03-1000, which records N3 and
refines S2. It changes no semantics: the spec already said so.

The spec is literate Lean rendered with Verso. `docs/spec/FirSpec.lean`
renders 115 modules of `lean/` in the Wasm spec's four chapters (abstract
syntax at line 51, validation at 69, execution at 97, text format at
211), then the ADRs as an appendix (293). The Lean definitions are the
normative spec. It is complete enough to implement from:

- every op of the M0 op set, 24 in all at `ca5fd9f` and 25 since #122
  added `poison`, has its text (`Core.lawfulDialectText`
  covers each), its validation rule and its execution rule
  (`Core.lawfulDialectPoison` proves that every valid instance of every
  op but `call` is total; `call` runs its callee, ADR-2026-11-02-1514);
- `funk-ir`, `funk` and `funk-x86-64` implement it, and the harness checks
  them against it (item 2);
- #113 read every chapter's prose against its Lean definitions, and the
  Rust verifier, parser, printer and backend against the spec, and fixed
  each mismatch it found, all in prose and comments. No Rust behaviour
  disagreed with the spec.

The `fir-spec` hook (`scripts/build-spec.sh`) builds `lean/` with
`--wfail`, checks the axioms and renders the document on every pull
request. `.github/workflows/pages.yml` publishes it from every push to
`main` at <https://p.ocmatos.com/funk/>
([spec-site.md](decisions/spec-site.md#publishing-the-site)).

### 2. Lean and Rust agree on every corpus program, and native results refine Lean's

The steps of `scripts/check-harness.sh`, run on the corpus of #119, end
with `19697 checks: 19697 passed, 0 failed, 0 invalid`:

| Check | Count |
| --- | --- |
| `funk verify` and `fir-ref validate` accept a text of the corpus | 261: 257 modules, 4 non-canonical inputs |
| They accept a module that Rust printed (`crates/funk-ir/examples/fir_texts.rs`) | 861: 600 from its generator, and the corpus's 261 texts as Rust prints them |
| They give a must-reject text the same verdict, and a parse error the same line and column | 488 |
| A differential test: native code's result refines `fir-ref`'s | 11,031 |
| An interpreter-only test: `fir-ref` gives the expected result | 7,056 |

`scripts/harness/check_invalid.py` also passes: the harness reports the
fixture with a frozen divisor invalid
([testing-and-harness.md](decisions/testing-and-harness.md#the-invalid-verdict-is-itself-tested)). The
`fir-ref-test` and `fir-round-trip` hooks check that `fir-ref fmt`
reprints each text Rust prints, byte for byte (item 3).

The harness builds, with `funk build`, the 184 modules that have a
differential test, and no other (`scripts/harness/checks.py:78-80`). By
the corpus format, only `fir-ref` runs an interpreter-only test
(ADR-2026-10-30-2050). Why each one is interpreter-only, with each test
counted once, under the first reason in this order that applies:

| Reason | Tests |
| --- | --- |
| Its module has a width that the backend rejects, as S2 asks (`crates/funk/tests/build.rs:61`) | 3,935 |
| `fir-ref` gives UB, which any native behaviour refines; as a differential test it would be invalid | 669 |
| It names the choices of a path through `freeze` | 175 |
| `fir-ref` gives poison in a result, which any native value refines | 1,323 |
| The run never ends, so it runs out of fuel | 82 |
| A defined result, with a differential test of the same function on the same arguments | 658 |
| A defined result, with no such differential test | 214 |

Of those 214, 14 recurse deeper than 20 calls, in `recursion-i8` and
`recursion-i128`: the cap that #107 restated, which stays. Deeper
differential runs are an option, not a requirement
([comment](https://github.com/pmatos/funk/issues/23#issuecomment-6592996398)
on #23), since the human ruled on 2026-10-30 that no depth is an M0
acceptance bar. The other 200 fill interpreter-only cells of the coverage
matrix (#115). Each of them runs a function that a differential test of
the same module runs as native code on other arguments.

At `ca5fd9f`, `tracer-i128` held 52 more runs with a defined result and
no differential test, at `i128`, which the backend lowers. It was a
corpus program that CI never ran as native code. #119 repeats each of
those runs as a differential test, 51 in all, since two of them differ
only in their fuel, and native code gives `fir-ref`'s result on each.

Of the 257 modules, the harness does not build 73: 64 hold a width that
the backend rejects, `empty` has no test, and eight at the backend's
widths have only interpreter-only tests: `fuel` and `fuel-call` (every
run runs out of fuel) and the six `poison-div-iN` (every run gives UB or
poison). `funk build` accepts those eight too.

So `fir-ref` and the Rust tools agree on every text of the corpus, and
native code refines `fir-ref` on every one of the 11,031 runs that it
makes, in every module with a differential test. Every module at the
backend's widths with a run that has a defined result is one of them.

### 3. Round trips hold in Rust and across Rust and Lean, under fuzzing

- **Lean** proves both round trips for well-formed modules
  (`printThenParse`, `parseThenPrint`, above).
- **Rust**, in the `rust-test` hook: `crates/funk-ir/tests/corpus.rs`
  prints every canonical text, `llvm/` included, back byte for byte, and
  parses each non-canonical input to its canonical form.
  `crates/funk-ir/tests/property.rs` fuzzes: 600 generated modules
  (`generate::ROUND_TRIP_MODULES`) are valid and give
  `parse(print(m)) == m` and `print(parse(t)) == t` (line 18), and
  between them hold every op with every flag set, loops, block arguments,
  width changes, every location kind and zero, one and several results
  (lines 31 to 232); random layout parses to the same module (299);
  mutated texts and random token soup never make the parser panic, and
  every text it accepts round-trips (320, 352).
- **Across Rust and Lean**, in the `fir-round-trip` hook
  (`scripts/check-fir-ref.sh round-trip`): Rust prints the 261 texts of
  the corpus and the 600 generated modules
  (`crates/funk-ir/examples/fir_texts.rs`), and `fir-ref` parses and
  reprints each one, byte for byte.

### 4. CI runs all of it on every pull request

`.github/workflows/ci.yml` runs on every pull request and every push to
`main`, and its job runs `pre-commit run --all-files` (line 95). Every
check above is a hook of `.pre-commit-config.yaml`: `fir-spec`,
`rust-fmt`, `rust-clippy`, `rust-test`, `fir-ref-test`,
`fir-round-trip`, `fir-harness`, `fir-harness-test`, `coverage-matrix`,
`g0` and `g0-test`. The ruleset of `main`
(`.github/rulesets/main.json`, live and active as ruleset 26023009)
requires the checks `pre-commit` and `PR title` on every merge. CI run
41607172439 at `ca5fd9f` passed every hook.

## #23's acceptance criteria

| Criterion | Evidence |
| --- | --- |
| The coverage matrix, generated by a script, every cell covered | `docs/coverage/README.md`, written by `scripts/harness/coverage.py` (ADR-2026-11-03-0557). The `coverage-matrix` hook fails when it is stale or a cell has no test: 769 cells, 769 with a test. Its `ret`, `call` and `func` rows count functions and calls with no, one and several results, on both sides (#115). |
| The LLVM ports, each with its source and licence | `tests/fir/llvm/`: 34 modules and 1,501 tests (1,018 differential, 483 interpreter-only) from llvm-project `7a941dfb` (`llvmorg-23.1.4`), beside LLVM's `LICENSE.TXT` and a notice, `README.md`. Each sidecar names its source file and commit, and each test its LLVM function; `scripts/harness/corpus.py` checks both and the licence's SHA-256 (ADR-2026-11-03-0643, [testing-and-harness-corpus.md](decisions/testing-and-harness-corpus.md#how-cases-are-chosen-and-rewritten), #116). |
| The spec's prose matches Lean, and Rust matches the spec | #113, above. At `ca5fd9f` no prose in `lean/`, `docs/spec/` or `tests/fir/README.md` points ahead to a landed M0 ticket: "Until #20" in `lean/FirTest/Run.lean` and `Runs.lean`, and "until #31" in `tests/fir/README.md`, tell what came before. |
| The G0 check passes, each violation fixed | #114: the four points hold, and the one gap, a default poison class, is fixed. The checks are `crates/funk-ir/tests/g0.rs` (`rust-test`), `scripts/check_g0.py` (`g0`) with its tests (`g0-test`) and `lean/FirTest/G0.lean` (ADR-2026-11-03-0600). |
| The Lean criteria | The first section. |
| Every "Done when" item, with evidence | The second section. |
| `pre-commit run --all-files` passes | CI's `pre-commit` check runs exactly that: run 41607172439 at `ca5fd9f`, and the run of the pull request that adds this file. |

## What stays open

Nothing, as of #5's close-out on 2026-11-05, at `28b6f37`. This section
listed three points, and none stays open:

- #41, #47 and #55, the performance and depth work, and #117 (Verus),
  which this section listed as #5's other open sub-issues, are closed:
  by PRs #125, #144, #131 and #118. #5 has no open sub-issue.
- The 20-deep cap on differential recursion stays, as #107 restated it.
  It is a rule of the corpus (`tests/fir/README.md`), not open work.
- The human answered the question on the `typos` check in #124: no
  exception for `tests/fir/llvm/`. PR #127 ported the three functions of
  LLVM's `rem.ll` under the corrected spelling
  ([testing-and-harness-corpus.md](decisions/testing-and-harness-corpus.md#names-the-spelling-check-rejects)).
