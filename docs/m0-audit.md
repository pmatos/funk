# M0 audit: the evidence that #23's criteria and #5's "Done when" items hold

This file records the evidence that the acceptance criteria of
[#23](https://github.com/pmatos/funk/issues/23) and the four "Done when"
items of the M0 epic, [#5](https://github.com/pmatos/funk/issues/5), hold
on `main` at `ca5fd9f`, the merge of #116. Four stages of #23 built what
it checks: the spec against Lean and the Rust side against the spec
([#113](https://github.com/pmatos/funk/pull/113)), the G0 check
([#114](https://github.com/pmatos/funk/pull/114)), the coverage matrix
([#115](https://github.com/pmatos/funk/pull/115)) and the ports of LLVM
tests ([#116](https://github.com/pmatos/funk/pull/116)). It records
evidence, not a decision, so it is not an ADR. Line numbers are those of
`ca5fd9f`. #5 stays open after #23 closes: see the last section.

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
declarations depends on another axiom, `sorryAx` included
(ADR-2026-10-30-1452, ADR-2026-10-30-1838), and `lake build --wfail`
fails on a `sorry` in an `example` (ADR-2026-10-30-1837). The `fir-spec`
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
- `PrintThenParse` is about well-formed modules (ADR-2026-10-30-0815).
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
| S2, integers `iN` | ADR-2026-10-29-2007 | accepted |
| S4, refinement | ADR-2026-10-29-2008 | accepted; refined by ADR-2026-10-30-0816 |
| S7, semantics in Lean | ADR-2026-10-29-2009 | accepted |
| H1, block arguments | ADR-2026-10-29-2010 | accepted |
| H2, isolated from above | ADR-2026-10-29-2011 | accepted |
| H3, globals by symbol | ADR-2026-10-29-2012 | accepted |
| H8, source locations | ADR-2026-10-29-2013 | accepted |
| P3, one text format | ADR-2026-10-29-2014 | accepted; refined by ADR-2026-10-30-0815 |
| P1, literate Lean spec | ADR-2026-10-29-2015 | accepted |
| G0, any hardware | ADR-2026-10-29-2016 | accepted; refined by ADR-2026-10-30-1146 and ADR-2026-11-03-0600 |

The decisions that the epic's work list asks for are ADRs too: `freeze`
in the oracle (ADR-2026-10-29-2017), fir's own Lean calculus after the
spike of #24 (ADR-2026-10-29-2030), assembly through GNU `as` and `ld`
(ADR-2026-10-30-1229) and spilling every value (ADR-2026-10-30-1230).
None of these ADRs is superseded.

The spec is literate Lean rendered with Verso. `docs/spec/FirSpec.lean`
renders 115 modules of `lean/` in the Wasm spec's four chapters (abstract
syntax at line 51, validation at 69, execution at 97, text format at
211), then the ADRs as an appendix (293). The Lean definitions are the
normative spec. It is complete enough to implement from:

- every op of the M0 op set, 24 in all, has its text (`Core.lawfulDialectText`
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
`main` at <https://p.ocmatos.com/funk/> (ADR-2026-10-30-1031).

### 2. Lean and Rust agree on every corpus program, and native results refine Lean's

The steps of `scripts/check-harness.sh`, run at `ca5fd9f`, end with
`19646 checks: 19646 passed, 0 failed, 0 invalid`:

| Check | Count |
| --- | --- |
| `funk verify` and `fir-ref validate` accept a text of the corpus | 261: 257 modules, 4 non-canonical inputs |
| They accept a module that Rust's generator printed | 600 |
| They give a must-reject text the same verdict, and a parse error the same line and column | 488 |
| A differential test: native code's result refines `fir-ref`'s | 10,980 |
| An interpreter-only test: `fir-ref` gives the expected result | 7,056 |

`scripts/harness/check_invalid.py` also passes: the harness reports the
fixture with a frozen divisor invalid (ADR-2026-10-31-0208). The
`fir-ref-test` and `fir-round-trip` hooks check that `fir-ref fmt`
reprints each text Rust prints, byte for byte (item 3).

`funk build` builds the 183 modules that have a differential test. By the
corpus format, only `fir-ref` runs an interpreter-only test
(ADR-2026-10-30-2050). Why each one is interpreter-only:

| Reason | Tests |
| --- | --- |
| Its module has a width that the backend rejects, as S2 asks (`crates/funk/tests/build.rs:61`) | 3,935 |
| `fir-ref` gives UB, which any native behaviour refines; as a differential test it would be invalid | 669 |
| `fir-ref` gives poison in a result, which any native value refines | 1,323 |
| The run never ends, so it runs out of fuel | 82 |
| It names the choices of a path through `freeze` | 175 |
| A defined result, with a differential test of the same function on the same arguments | 606 |
| A defined result, with no such differential test | 266 |

Of those 266, 14 recurse deeper than 20 calls, in `recursion-i8` and
`recursion-i128`: the cap that #107 restated, which the human kept. 52
are in `tracer-i128`, which states what `fir-ref` gives for `const`,
`add` and `ret` at `i128`; `add-i128` runs the same additions
differentially. The other 200 fill interpreter-only cells of the coverage
matrix (#115), in modules whose other tests run natively. Nine modules at
the backend's widths are not built, since all their tests are
interpreter-only: `fuel` and `fuel-call` (every run runs out of fuel),
the six `poison-div-iN` (every run gives UB or poison) and `tracer-i128`.

So `fir-ref` and the Rust tools agree on every text of the corpus, and
native code refines `fir-ref` on every one of the 10,980 runs that it
makes, in every module that the backend builds.

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
| The LLVM ports, each with its source and licence | `tests/fir/llvm/`: 34 modules and 1,501 tests (1,018 differential, 483 interpreter-only) from llvm-project `7a941dfb` (`llvmorg-23.1.4`), beside LLVM's `LICENSE.TXT` and a notice, `README.md`. Each sidecar names its source file and commit, and each test its LLVM function; `scripts/harness/corpus.py` checks both and the licence's SHA-256 (ADR-2026-11-03-0643, ADR-2026-11-03-0644, #116). |
| The spec's prose matches Lean, and Rust matches the spec | #113, above. At `ca5fd9f` no prose in `lean/`, `docs/spec/` or `tests/fir/README.md` points ahead to a landed M0 ticket: "Until #20" in `lean/FirTest/Run.lean` and `Runs.lean`, and "until #31" in `tests/fir/README.md`, tell what came before. |
| The G0 check passes, each violation fixed | #114: the four points hold, and the one gap, a default poison class, is fixed. The checks are `crates/funk-ir/tests/g0.rs` (`rust-test`), `scripts/check_g0.py` (`g0`) with its tests (`g0-test`) and `lean/FirTest/G0.lean` (ADR-2026-11-03-0600). |
| The Lean criteria | The first section. |
| Every "Done when" item, with evidence | The second section. |
| `pre-commit run --all-files` passes | CI's `pre-commit` check runs exactly that: run 41607172439 at `ca5fd9f`, and the run of the pull request that adds this file. |

## What stays open

- #5 stays open. Its open sub-issues, #41, #47 and #55, are
  performance and depth work, which the human parked on 2026-10-30; no
  depth is an M0 acceptance bar. #117 (Verus) is not part of #23.
- The 20-deep cap on differential recursion stays, as #107 restated it.
- A question for the human, not part of #23: whether `tests/fir/llvm/`
  may get an exception from the `typos` check, so that the three
  functions of LLVM's `rem.ll` whose names it rejects can be ported
  (ADR-2026-11-03-0644).
