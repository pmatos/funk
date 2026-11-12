# Current decisions: testing and the harness

This page states what holds today for testing and the harness. It is the record:
when this page and an ADR disagree, the page wins, and the ADR is fixed or
deleted (ADR-2026-11-09-1610). It continues in
[testing-and-harness-corpus.md](testing-and-harness-corpus.md) (the corpus, the
coverage matrix and the LLVM ports),
[testing-and-harness-generated.md](testing-and-harness-generated.md) (generated
programs and fuzzing) and
[testing-and-harness-floats.md](testing-and-harness-floats.md) (floating
point).

## How a test is judged

The harness reports each test as passed, failed or invalid. An invalid test
never counts as a pass, and it fails the run (ADR-2026-10-30-2135). Correctness
is refinement: the native result must refine the result of `fir-ref`. Any value
refines poison (ADR-2026-10-29-2008).

### Differential tests

A differential test has no `expect` key. It runs on `fir-ref` and as native code
from `funk build`. `fir-ref` runs in exhaustive mode, at the test's fuel budget
and a choice budget of 16 bits (ADR-2026-10-30-2135).

A run that makes no choice has one outcome (ADR-2026-10-30-2135):

- Values pass when the lists have the same length and each native value matches.
  Where `fir-ref` returns poison, any value of the result type matches. The
  harness reads the result types from the function's signature line in the
  canonical text.
- UB makes the test invalid, since source UB allows any result.
- Fuel exhausted makes the test invalid, since the result depends on the budget.
  The author raises the test's fuel, or makes it an interpreter-only test that
  expects fuel exhausted.
- Stuck fails the test.
- A tool error fails the test. Examples are `fir-ref` exiting with 2, and an
  executable that exits with 2 or dies by a signal.
- A module that `funk build` does not build also fails the test.

UB reasons are for people, and the harness never compares them.

A run that makes choices is judged on its set of outcomes
(ADR-2026-10-30-2135, ADR-2026-10-29-2017). A stuck path fails the test, even
in a set that also holds UB. Otherwise, UB or fuel exhausted anywhere in the set
makes the test invalid. Native code passes when its result refines one outcome
of the set. Past the choice budget, a test that declares no results is invalid.

Rejected: fuel exhausted as a pass or a failure. It says nothing about native
code, and neither tool is wrong: the test is. Also rejected: comparing UB
reasons, which refinement ignores (ADR-2026-10-30-2135).

### Declared results

A differential test may declare `results`, each with its values and a witness
(ADR-2026-10-30-2135). No two have the same values. Each witness runs with
`--choices` and must give exactly its values. Within the budget, the set must
be exactly the declared results. Past the budget, `fir-ref run --seed S` runs
for each S from 0 to 31. Each must give a declared result, and a failure names
the seed and the values it drew. Native code passes when its result refines one
declared result. UB or fuel exhausted on a witness or a seed makes the test
invalid. Seeded runs only sample, so a declaration can still miss a result.

Rejected: sampling on every declared test, since within the budget the set is
exact, and a choice budget per test, since a test past the budget declares its
results (ADR-2026-10-30-2135).

### Interpreter-only tests

An interpreter-only test has an `expect` key and runs on `fir-ref` only. It
passes when `fir-ref` gives the expected result: the same values, poison
included, or UB with any reason, or fuel exhausted (ADR-2026-10-30-2135). Such a
test may name its path with `choices`. Without it, a run that chooses fails.

### Poison arguments

The human ruled on 2026-11-03 that `fir-ref run` takes `poison` as an argument,
and that the harness uses it in differential tests too (#123). A test's `args`
may hold `poison`, which goes to `fir-ref` unchanged.

Native code holds no poison, so it runs on stand-ins in each poison argument's
place: 0, 1, all ones, the signed minimum and the signed maximum, the boundary
bit patterns that sampled mode favours. At a float type these are the same bit
patterns of its `1 + e + m` bits, spelled as its constants are
(ADR-2026-11-11-1438). It runs once on each combination, up to `5 ** k` runs
for `k` poison arguments (`scripts/harness/standins.py`). Each native result is
judged against the outcomes of `fir-ref` on the poison, and every result must
pass. UB among those outcomes makes the test invalid. Past the choice budget, a
failing vector also runs on `fir-ref`. UB or a path out of fuel there makes the
test invalid. The report names the first vector that fails, and past the budget
`fir-ref`'s outcome on it.

This is sound. A run with a value in place of poison refines the run with
poison (`Core.args_isRefinedBy`, calls and recursion included), and correct
native code refines `fir-ref` on defined values, so by transitivity
(`Core.behaviour_isRefinedBy_trans`) a correct result on stand-ins refines the
behaviour on the poison. Within the budget a failure is a bug of native code on
the vector it names. Past it, seeded runs may miss UB that a stand-in reaches,
hence the run on the vector. The test is weaker than one on the stand-ins' own
values: where the poison reaches a result, any value passes.

Rejected: one stand-in, such as 0, which `poison` lowers to. Bugs gather at the
boundary bit patterns. Also rejected: random stand-ins, whose failures would not
reproduce.

### Where the judgement lives

`scripts/harness/differential.py` owns the complete judgement of a differential
test. Its `evaluate` operation takes the test, its result and parameter types,
and an adapter for tool runs, and returns the judgement and its explanation.
`execution.py` supplies the process adapter, and focused tests supply an
in-memory one that records every run. The corpus runner keeps validation,
building once per module, interpreter-only tests and the report. The rules stay
in `refine.py` and `sets.py`.

A judgement on the reference side wins over a native failure. A decided test
still runs native code once, when possible, for evidence. A recheck collects all
seeds, ignores seed tool errors and prefers UB to fuel exhaustion. Otherwise it
keeps the original failure, stuck included. A recheck does not use the
outcome-set rule, whose precedence differs.

Rejected: optional `pre`, `judge` and `recheck` callbacks in the runner. One
test's judgement had to be followed across the runner and its rule functions.

### The invalid verdict is itself tested

`tests/fir/` cannot hold a test that is meant to be invalid, since it would fail
every run. No sidecar key declares a test invalid, as the harness must never
report such a test as passed (#13).

`scripts/harness/fixtures/invalid/` is a separate corpus that the main run does
not read. Its `div-frozen` test divides by `freeze` of poison, so the divisor
can be zero. `scripts/harness/check_invalid.py` runs the harness on it with the
real tools. It passes only when that test is reported invalid for `sdiv by
zero`, `funk build` did not fail, every other check passed, and the harness
exits with 1. A native crash is allowed, since UB in the set allows any result.
`scripts/check-harness.sh` runs this check after the main run. A change to the
report's layout, to the wording `the set holds UB` in `sets.py` or to the
reason `sdiv by zero` must update `check_invalid.py`. The fixtures are corpora
in the format of `tests/fir/`, so a change to that format must keep them valid.
The round-trip hooks and `crates/funk-ir/tests/corpus.rs` read `tests/fir/`
only, so only the harness's run on a fixture checks that both tools accept it.

Rejected: an `invalid = "ub"` key that passes such a test, which would report
an invalid test as passed. Also rejected: expecting exit status 1 alone, which
says that something did not pass, not which test or why.

## The harness program

CI runs `fir-harness` and `fir-harness-test` as steps of its `cross` job
(ADR-2026-11-05-1408).

The differential harness is the Python package `scripts/harness/`. It uses the
standard library only and needs Python 3.11 or later, for `tomllib`. It is a
test tool, so the roadmap's rule that the toolchain is Rust does not bind it.
It judges two implementations, so it shares no code with either.

Rejected: a Rust crate in the workspace, which would need a JSON reader of its
own and would read the corpus with the parser it checks. Also rejected: shell,
which has no JSON or TOML reader.

`scripts/check-harness.sh` is the one command. It builds `fir-ref` and `funk`,
prints the corpus's texts and the generator's modules, and runs `main.py`.

Each text goes through `funk verify --json` and `fir-ref validate`, one process
per text, so that a crash loses no other verdict. Both tools must accept every
corpus and generated module. A must-reject text must get the verdict its file
names from both. A parse error must be at the same line and column in both.
Counts and messages are never compared.

The tests of a module run only when both tools accept it. A module with a
differential test is built once. Each tool must print one JSON object on one
line and exit with the matching status, and native code prints nothing on
standard error. Anything else fails the check. A process that runs for 120
seconds is stopped and fails its check.

The report has one line per check, starting `passed`, `failed` or `invalid`.
Passed generated modules are counted, not listed. The exit status is 0 when
every check passed, and 1 when one failed or was invalid. It is 2 on a usage
error or a tool that cannot be started.

The `fir-harness` hook runs `scripts/check-harness.sh`, and `fir-harness-test`
runs the unit tests. `fir-harness-test` runs through the shared Python test
runner ([process-ci.md](process-ci.md#the-python-test-runner)).

### Native code runs under a data limit

Only the executable of a differential test runs under a limit. `funk`,
`fir-ref`, `as` and `ld` do not, because they are not the code under test. The
limit is 1 GiB, `tools.DATA_LIMIT`, soft and hard, on both `RLIMIT_DATA` and
`RLIMIT_AS`. It is one fixed size, so a verdict does not depend on the machine.
A lower limit that the harness inherits stays in force. A runaway recursion
then ends long before memory and swap fill (#92). `tools.limit_data` sets the
limit as the `preexec_fn` of the run, between `fork` and `exec`, which Python
documents as unsafe in a process with threads, so the harness runs none.
Raising `DATA_LIMIT` changes this rule, on this page, in the same pull request.

Under `ulimit -s unlimited` the runtime halves its stack request until
`RLIMIT_AS` lets one fit, and the harness relies on that. The limit changes no
verdict rule. A run that cannot reserve its stack reads as a failure. The test
is then invalid where `fir-ref` runs out of fuel, and fails where it returns.

Rejected: the limit on every tool, which would fail a check for what a tool
needs. Also rejected: a cgroup limit, which needs a systemd manager, and a size
from the machine's memory, which would make a verdict depend on the host.

### A run that outgrows its stack

A run that outgrows its stack makes its test invalid. `tools.native_values`
returns `refine.OutOfStack(N)` for exit status 2, empty standard output and
exactly the runtime's stack message. Anything else, such as a stack that cannot
be reserved, stays a failure. fir has no depth limit (ADR-2026-10-30-1549), so
the run proves nothing, and invalid keeps the harness red. A test that outgrows
the machine's stack needs fewer calls or a larger `ulimit -s`.
`scripts/harness/fixtures/out-of-stack/` holds one such test, and
`check_invalid.py` runs it under an 8 MiB stack (#172).

Rejected: a pass, which would hide a runaway recursion, and a failure, which is
the mismatch #172 forbids.

## The fir explorer

The human asked on 2026-11-08 for a local web app to write fir and see what it
compiles to and means (#216). The fir explorer is a local Python server over
`funk` and `fir-ref`: the package `scripts/harness/explorer/`, started by
`scripts/explorer.sh`. It imports the harness's modules, and the
`fir-harness-test` hook runs its tests. It has no dependencies and no build step.

It has no semantics of its own. It runs the tools and shows what they report. A
verdict on a native run comes from `differential.evaluate`. A native run is
reported as unavailable, with no alarm, in two cases. The backend cannot lower
the module, or `fir-ref` cannot run the call.

It binds to the loopback address, with no option to change that. Every request
must name a loopback `Host`, which stops DNS rebinding. Every POST must carry
the page's own `Origin` and be `application/json`. It serves one request at a
time, because native runs use `preexec_fn`. Native runs keep the harness's data
limit. Each tool and native program has 10 seconds by default, set by
`--timeout`.

Rejected: a Rust server, which would need a web dependency and a second copy of
the harness's judgement.

## Lean tests and the checks of fir-ref

CI runs `fir-spec` and `fir-ref-test` as steps of its `lean` job. It runs
`fir-round-trip` as a step of its `cross` job (ADR-2026-11-05-1408).

fir has no nesting limit: the human ruled on 2026-10-30 (#36) that every tool,
`fir-ref` included, gives a verdict on a text nested to any depth
(ADR-2026-10-30-1549). So depth must not cost `fir-ref` stack, and `fir-ref`
runs implementations proved equal to the spec's functions
(ADR-2026-10-30-1450). No specific depth is an acceptance bar: the human ruled
that on 2026-10-30, on #47. Lean-side speed is a rough guide, not a gate: the
human ruled on 2026-11-05 that about 10x of the Rust side on the same job is
fine, and hours on a simple example is not
([fir-ref.md](fir-ref.md#when-a-new-fast-path-is-allowed)). So the CPU-time
limits of `scripts/check-fir-ref.sh` stop a hang or a clearly too slow case.

`lake build` in `lean/` builds the spec library `Fir`, the library `FirRef`, the
executable `fir-ref` and the test library `FirTest`
([spec-site-lean-build.md](spec-site-lean-build.md)). So it runs the Lean
tests. Unit tests are `#guard` checks in `lean/FirTest/`.

Tests over files run the built `fir-ref`, through `scripts/check-fir-ref.sh`. Its
`test` mode checks the canonical and non-canonical texts. Its `round-trip` mode
has Rust print every text of `tests/fir/` and the first 600 generated modules,
and `fir-ref fmt --check` must find each canonical.

`check-fir-ref.sh test` keeps its own table of `fir-ref run` results, which
tests `fir-ref`'s command line. New expected results go in the corpus's
sidecars.

`scripts/build-spec.sh --lean` is the one guarded build of `fir-ref`. Every
script and hook that needs `fir-ref` calls it, and none runs Lake itself.

Rejected: `lake test` with a test driver, a second Lake entry point to guard.
Also rejected: tests at elaboration time with file I/O, which would depend on
Lake's working directory and would not run the `fir-ref` binary.

`fir-round-trip` needs both toolchains. `lean/.lake` is not cached in CI.

The Lean tests that mix core and toy ops use the spec's sum of dialects,
`CoreDialect ⊞ e` (ADR-2026-11-09-2306). The toy, use-once and probe test
dialects are extensions of the core named `toy`, with no types of their own.
Their shared helpers are in `lean/FirTest/OverCore.lean`. A name that starts
with `toy.` goes to the test dialect, and every other name to the core
(ADR-2026-11-09-1543). The bit dialect, `lean/FirTest/Bit.lean`, is named
`bit`, so that `lean/FirTest/Deps.lean` can sum the core, the toy dialect and
the bit dialect, lifted into the sum of the other two (ADR-2026-11-09-2306).
