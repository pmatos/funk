# Current decisions: testing and the harness

This page states what holds today for testing and the harness. It summarizes
the ADRs it cites, and they remain the record. When this page and an ADR
disagree, the page is wrong (ADR-2026-11-09-1610).

## How a test is judged

The harness reports each test as passed, failed or invalid. An invalid test
never counts as a pass, and it fails the run (ADR-2026-10-30-2135). Correctness
is refinement: the native result must refine the result of `fir-ref`. Any value
refines poison (ADR-2026-10-29-2008).

### Differential tests

A differential test has no `expect` key. It runs on `fir-ref` and as native code
from `funk build`. `fir-ref` runs in exhaustive mode, at the test's fuel budget
and a choice budget of 16 bits (ADR-2026-10-31-0003).

A run that makes no choice has one outcome (ADR-2026-10-30-2135):

- Values pass when the lists have the same length and each native value matches.
  Where `fir-ref` returns poison, any value of the result type matches.
- UB makes the test invalid, since source UB allows any result.
- Fuel exhausted makes the test invalid, since the result depends on the budget.
- Stuck fails the test.
- A tool error fails the test. Examples are `fir-ref` exiting with 2, and an
  executable that exits with 2 or dies by a signal.
- A module that `funk build` does not build also fails the test.

UB reasons are for people, and the harness never compares them.

A run that makes choices is judged on its set of outcomes
(ADR-2026-10-31-0003). A stuck path fails the test, even in a set that also
holds UB. Otherwise, UB or fuel exhausted anywhere in the set makes the test
invalid. Native code passes when its result refines one outcome of the set. Past
the choice budget, a test that declares no results is invalid.

### Declared results

A differential test may declare `results`, each with its values and a witness
(ADR-2026-10-31-0003). Each witness runs with `--choices` and must give exactly
its values. Within the budget, the set must be exactly the declared results.
Past the budget, `fir-ref run --seed S` runs for each S from 0 to 31. Each must
give a declared result. Native code passes when its result refines one declared
result. UB or fuel exhausted on a witness or a seed makes the test invalid.
Seeded runs only sample, so a declaration can still miss a result.

### Interpreter-only tests

An interpreter-only test has an `expect` key and runs on `fir-ref` only. It
passes when `fir-ref` gives the expected result: the same values, poison
included, or UB with any reason, or fuel exhausted (ADR-2026-10-30-2135). Such a
test may name its path with `choices`. Without it, a run that chooses fails
(ADR-2026-10-31-0003).

### Poison arguments

A test's `args` may hold `poison`, which goes to `fir-ref` unchanged
(ADR-2026-11-03-1847). Native code runs on stand-ins in its place: 0, 1, all
ones, the signed minimum and the signed maximum. At a float type these are the
same bit patterns of its `1 + e + m` bits, spelled as its constants are
(ADR-2026-11-11-1438). It runs once on each combination. Each native result is judged against the outcomes of `fir-ref` on
the poison, and every result must pass. UB among those outcomes makes the test
invalid. Past the choice budget, a failing vector also runs on `fir-ref`. UB or
a path out of fuel there makes the test invalid.

### Where the judgement lives

`scripts/harness/differential.py` owns the complete judgement of a differential
test (ADR-2026-11-06-1218). Its `evaluate` operation takes an adapter for tool
runs, and returns the judgement and its explanation. `execution.py` supplies the
process adapter, and focused tests supply an in-memory one. The corpus runner
keeps validation, building, interpreter-only tests and the report. The rules
stay in `refine.py` and `sets.py`.

A judgement on the reference side wins over a native failure. A decided test
still runs native code once, when possible, for evidence. A recheck collects all
seeds and prefers UB to fuel exhaustion. Otherwise it keeps the original failure.
A recheck does not use the outcome-set rule, whose precedence differs.

### The invalid verdict is itself tested

`tests/fir/` cannot hold a test that is meant to be invalid, since it would fail
every run. No sidecar key declares a test invalid, as the harness must never
report such a test as passed (ADR-2026-10-31-0208).

`scripts/harness/fixtures/invalid/` is a separate corpus that the main run does
not read. It holds a differential test whose frozen divisor can be zero.
`scripts/harness/check_invalid.py` runs the harness on it with the real tools.
It passes only when that test is reported invalid for `sdiv by zero`, every other
check passed, and the harness exits with 1. `scripts/check-harness.sh` runs this
check after the main run. A change to the report's layout or to the wording it
reads must update `check_invalid.py`.

## The harness program

CI runs `fir-harness` and `fir-harness-test` as steps of its `cross` job
(ADR-2026-11-05-1408).

The differential harness is the Python package `scripts/harness/`. It uses the
standard library only and needs Python 3.11 or later (ADR-2026-10-30-2049). It
is a test tool, so the roadmap's rule that the toolchain is Rust does not bind
it. It judges two implementations, so it shares no code with either.

`scripts/check-harness.sh` is the one command. It builds `fir-ref` and `funk`,
prints the corpus's texts and the generator's modules, and runs `main.py`.

Each text goes through `funk verify --json` and `fir-ref validate`, one process
per text. Both tools must accept every corpus and generated module. A must-reject
text must get the verdict its file names from both. A parse error must be at the
same line and column in both. Counts and messages are never compared.

The tests of a module run only when both tools accept it. A module with a
differential test is built once. Each tool must print one JSON object on one line
and exit with the matching status. Anything else fails the check. A process that
runs for 120 seconds is stopped and fails its check.

The report has one line per check, starting `passed`, `failed` or `invalid`. The
exit status is 0 when every check passed, and 1 when one failed or was invalid.
It is 2 on a usage error or a tool that cannot be started.

The `fir-harness` hook runs `scripts/check-harness.sh`, and `fir-harness-test`
runs the unit tests (ADR-2026-10-30-2049). `fir-harness-test` runs through the
shared Python test runner (ADR-2026-11-05-1633).

### Native code runs under a data limit

Only the executable of a differential test runs under a limit
(ADR-2026-11-02-2250). `funk`, `fir-ref`, `as` and `ld` do not, because they are
not the code under test. The limit is 1 GiB, `tools.DATA_LIMIT`, on both
`RLIMIT_DATA` and `RLIMIT_AS`. It is one fixed size, so a verdict does not depend
on the machine. A lower limit that the harness inherits stays in force. Raising
`DATA_LIMIT` takes a new ADR.

The limit changes no verdict rule. A run that cannot reserve its stack reads as
a failure. The test is then invalid where `fir-ref` runs out of fuel, and fails
where it returns.

A run that outgrows its stack makes its test invalid (ADR-2026-11-09-1602).
`tools.native_values` returns `refine.OutOfStack(N)` for exit status 2, empty
standard output and exactly the runtime's stack message. fir has no depth limit,
so the run proves nothing, and invalid keeps the harness red. A test that
outgrows the machine's stack needs fewer calls or a larger `ulimit -s`.

## The fir explorer

The fir explorer is a local Python server over `funk` and `fir-ref`
(ADR-2026-11-08-1806). It is the package `scripts/harness/explorer/`, started by
`scripts/explorer.sh`. It imports the harness's modules, and the
`fir-harness-test` hook runs its tests. It has no dependencies and no build step.

It has no semantics of its own. It runs the tools and shows what they report. A
verdict on a native run comes from `differential.evaluate`. A native run is
reported as unavailable, with no alarm, in two cases. The backend cannot lower
the module, or `fir-ref` cannot run the call.

It binds to the loopback address, with no option to change that. Every request
must name a loopback `Host`. Every POST must carry the page's own `Origin` and be
`application/json`. It serves one request at a time, because native runs use
`preexec_fn`. Native runs keep the harness's data limit (ADR-2026-11-08-1806).
Each tool and native program has 10 seconds by default, set by `--timeout`.

## The test corpus

`tests/fir/` holds only these (ADR-2026-10-30-2050, ADR-2026-11-03-0643):

- `canonical/NAME.fir`: a canonical, valid module.
- `canonical/NAME.toml`: the tests of that module, if it has any.
- `noncanonical/NAME.fir`: an input whose canonical form is `canonical/NAME.fir`.
- `reject/*.toml`: must-reject texts, grouped by what they break.
- `llvm/`: the cases ported from LLVM.
- `README.md`, which documents the format for authors.

Test metadata stays outside the `.fir` text, since a comment would break the
round trip. The harness fails on a file the layout has no place for, and on a
sidecar key it does not know.

A test is one inline table in the sidecar's `tests` list. Its keys are `func`,
`args`, `fuel` (1,000,000 steps by default) and `expect`
(ADR-2026-10-30-2050). The keys `results` and `choices` come from
ADR-2026-10-31-0003.

A module with a differential test builds whole, since `funk build` is all or
nothing. A function that the backend does not lower goes in a module whose tests
are all interpreter-only. A corpus text uses only the ops that both tools have.

A must-reject text is a `[[reject]]` table with `verdict`, `rule` and `text`. The
verdict is `parse-error` or `validation-error`. The rule is the one it breaks, in
words. When the ops cannot break a rule alone, the text breaks a second rule too,
and `rule` names both.

A new test is a new line or file in `tests/fir/`, with no code change
(ADR-2026-10-30-2049).

ADR-2026-10-30-0818 forbids two rewrites of `select`, and each has a named test
(ADR-2026-10-31-0524). `select-and` tests the rewrite into `and`.
`select-cond-br`, and `FirTest.Branch` in Lean, test the rewrite into `cond_br`.

## The coverage matrix

A generated matrix counts the corpus's tests of each cell (ADR-2026-11-03-0557).
A hook fails when the matrix is stale or a cell has no test.

A cell is an op instance of the core dialect at a width, on one side. An op
instance is the op with its flag set, `exact` choice or `icmp` predicate. Width
changes are cells for each pair of widths. Passed and returned values are cells
for none, one or several values. `scripts/harness/cells.py` holds the exact set.

The differential side has `i1`, `i8`, `i16`, `i32`, `i64` and `i128`. The
interpreter-only side adds `i7` and `i33`. Ops at other widths count towards no
cell.

The float ops have a table of their own: a float constant, and `fcmp` with each
predicate, at each float format of a side. The differential side has `f32` and
`f64`, and the interpreter-only side `f16`, `bf16`, `f32`, `f64` and `f128`.
Passed and returned values are cells at each of these formats too
(ADR-2026-11-11-1141).

A test exercises each op of the function it runs and of every function it calls,
directly or through others. It also exercises the `func` cell of its results. The
count is static, so a block that the arguments skip still
counts. No check reads the outcome. So whoever fills a cell writes a test whose
path runs the op and whose outcome depends on what the op computes. A test that
only passes poison into the op checks how poison goes through it, not the op.

`scripts/harness/coverage.py` writes the matrix to `docs/coverage/README.md`, and
`coverage.py --write` rewrites it. A pull request that changes the corpus
regenerates it. A new op, flag or predicate fails the unit tests until `cells.py`
has its cells. The `coverage-matrix` hook then fails until the corpus tests them.
A new side or width is a change to ADR-2026-11-03-0557 and to `cells.py`.

`poison` has its own rule, since no differential test can tell it from `const 0`
(ADR-2026-11-03-1618). A differential test fills its cell when the op runs as
native code and the result refines that of `fir-ref`. An interpreter-only test
fills its cell when the outcome observes the poison. Authors and reviewers keep
at least one such test in each interpreter-only cell, since no check does.

## Generated programs and fuzzing

Every pull request runs generated programs on `fir-ref` and as native code
(ADR-2026-11-08-2115). The `fir-random` hook runs seeds 0 to 499, the regression
seeds and 500 random texts for `fir-ref fmt`.

`generate::program` makes a module of the backend's widths and argument vectors,
often at boundary values. Its functions are random, bounded, or planted to end in UB or
out of fuel. Arguments hold no `poison`, since each one multiplies native runs.

A generated run is judged differently from a corpus test:

- A planted run must end as planted on `fir-ref`. Each kind of UB has a near
  miss, one operand away, whose result the generator states.
- The first bounded function of each program, and half of the others, stay
  defined. A report of UB, poison, a choice or no fuel on their runs fails them.
- Any other run with UB or no fuel in its set is interpreter-only and passes.
  So is one that chooses past 10 bits.
- Otherwise the run is a differential test by the corpus's rules.
- A stuck path fails in every case.

Ordinary runs have 20,000 steps of fuel. Runs of the functions that stay
defined have 1,000,000, and planted fuel runs have 1,000 (ADR-2026-11-08-2115).
The hook also guards against an empty check. In
a run of 200 or more, at least half of the runs without an expected ending must
reach native code.

A false UB in a purely random function goes unnoticed. A second interpreter would
cover it, and that is a direction call. A change to the generator changes which
program each seed means.

### Fresh seeds

Pull requests run fixed seeds, so that a local pass predicts a CI pass. Only a
nightly workflow draws fresh ones (ADR-2026-11-08-2116, ADR-2026-11-05-1408).
`fir-random-nightly` and `fir-fuzz` are hooks of the `manual` stage, and
`.github/workflows/nightly.yml` runs them.

A failure prints the seeds to replay and fails the workflow. Nothing files an
issue. Each failure's seed joins `scripts/harness/regression_seeds.txt`, which
every pull request runs. A seed names a program only for the generator of its
day, so the failing program also joins `tests/fir/` as a test.

### Fuzzing

`fuzz/` is a crate outside the workspace with the targets `parse` and `verify`
(ADR-2026-11-08-2117). The `fir-fuzz` hook runs each target for 10 minutes on the
pinned nightly compiler, with no sanitizer. There is no Lean fuzzer.

Every input the fuzzers keep goes through `fir-ref fmt`, as do the random texts.
It must print a canonical form or report a parse error at a position.
`scripts/harness/fuzz_to_corpus.py` keeps a crash in `tests/fir/` once the bug is
fixed.

The round trip is also fuzzed over well-formed modules, a larger set than valid
ones (ADR-2026-11-05-1718). `generate::wellformed::module` makes them. Rust checks
both directions on the first 600 modules of each kind. `fir-ref fmt --check` must
reprint the first 600 core-dialect modules byte for byte, and nothing validates
them. `fir-ref` cannot read string attributes, applied attributes or other
dialects, so only Rust fuzzes those.

## Lean tests and the checks of fir-ref

CI runs `fir-spec` and `fir-ref-test` as steps of its `lean` job. It runs
`fir-round-trip` as a step of its `cross` job (ADR-2026-11-05-1408).

fir has no nesting limit, so depth must not cost `fir-ref` stack
(ADR-2026-10-30-1250). `fir-ref` runs implementations proved equal to the spec's
functions (ADR-2026-10-30-1450).

`lake build` in `lean/` builds the spec library `Fir`, the library `FirRef`, the
executable `fir-ref` and the test library `FirTest` (ADR-2026-10-30-1250). So it
runs the Lean tests. Unit tests are `#guard` checks in `lean/FirTest/`.

Tests over files run the built `fir-ref`, through `scripts/check-fir-ref.sh`. Its
`test` mode checks the canonical and non-canonical texts. Its `round-trip` mode
has Rust print every text of `tests/fir/` and the first 600 generated modules,
and `fir-ref fmt --check` must find each canonical.

`scripts/build-spec.sh --lean` is the one guarded build of `fir-ref`. Every
script and hook that needs `fir-ref` calls it, and none runs Lake itself.

`fir-round-trip` needs both toolchains. `lean/.lake` is not cached in CI.

The Lean tests that mix core and toy ops use the spec's sum of dialects,
`CoreDialect ⊞ e` (ADR-2026-11-09-2306). The toy, use-once and probe test
dialects are extensions of the core named `toy`, with no types of their own.
Their shared helpers are in `lean/FirTest/OverCore.lean`. A name that starts
with `toy.` goes to the test dialect, and every other name to the core
(ADR-2026-11-09-1543). The bit dialect, `lean/FirTest/Bit.lean`, is named
`bit`, so that `lean/FirTest/Deps.lean` can sum the core, the toy dialect and
the bit dialect, lifted into the sum of the other two (ADR-2026-11-10-1310).

## Tests ported from LLVM

Ported cases live in `tests/fir/llvm/` (ADR-2026-11-03-0643). Each is a canonical
valid module and its sidecar. LLVM's licence sits beside them as `LICENSE.TXT`,
and `README.md` is the notice that lists each module with its source.

A sidecar has `source`, and each test has `from`. Each function's ops carry a
location, a source range of the LLVM test file. Every module names one
llvm-project commit, `7a941dfb2877a0b8cf30323fefa85ad019e0b0f5`. Moving to a
newer commit means moving every module, or a new ADR. No LLVM file is in the
repository, only the hand translations. `scripts/harness/corpus.py` checks that
`LICENSE.TXT` and `README.md` are present, the licence's SHA-256, a sidecar for
each module, a well-formed `source`, a `from` on each test, that no other file
is there, and that at most one commit is named (ADR-2026-11-03-0643). The ported
modules are canonical texts, so every reader of the corpus reads
them.

A case comes in when fir's M0 ops can express it and it tests an integer edge
case (ADR-2026-11-03-0644). A function that uses a vector, floating point, a
pointer, memory, an intrinsic, `switch` or `undef` is left out. So is one that
calls a function its file does not define. From each file the port takes each
kind of fold, and each negative test that shows a flag or a bound at work. It
also takes every case at an odd width or at `i128`. A function that only repeats
one of those with other constants, commuted operands or another predicate is
left out.

A function whose name the repository's spelling check rejects is still ported. It
keeps LLVM's name with the misspelled word spelled correctly
(ADR-2026-11-03-1614). The misspelled word is written nowhere in the repository.
The spelling check gets no exception.

ADR-2026-11-03-0644 fixes how LLVM's text is rewritten into fir. LLVM's `poison`
constant of type `iN` becomes `%p: iN = poison`, at the location of the ops that
use it (ADR-2026-11-03-1619). A flag that fir's op lacks is dropped only where it
can never give poison in that function. Where it can, the function is left out.

Each fold becomes runs of the input function at chosen arguments. Where the
folded form has ops, it is ported as `@NAME.folded` and runs on the same
arguments. Every expected value comes from LLVM's statement or separate working,
never from a run of `fir-ref`. A run whose module builds and whose result is a
value is differential. A run that gives poison or UB, or has a width the backend
does not lower, is interpreter-only.

LLVM's CHECK lines fold some divisions that are UB to poison, where `fir-ref`
reports UB. LangRef makes those divisions UB too, so the poison is LLVM's
refinement of that UB, not a difference of semantics.
