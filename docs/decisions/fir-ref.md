# Current decisions: fir-ref

This page states what holds today for `fir-ref`, the reference interpreter's
executable. It summarizes the ADRs it cites. When this page and an ADR
disagree, the page is wrong (ADR-2026-11-09-1610).

## What a run means

`freeze` of poison is a choice. The interpreter's monad has a `choose w`
effect, and `freeze` of poison calls it. Every use of the result sees the
same bits. In the set instance of the monad, the interpreter defines the
semantics: the set of behaviours over all choices (ADR-2026-10-29-2017).

The same interpreter backs every mode. Exhaustive mode tries every choice
sequence within a budget and prints the set of outcomes. Scripted mode takes
one choice sequence and prints one outcome. Lean proves that exhaustive mode,
within its budget, returns exactly the semantic set. Lean also proves that
scripted mode returns a member of it. So the oracle the harness runs is the
semantics the spec defines (ADR-2026-10-29-2017).

Every op takes one step of fuel, a call included. A callee runs with the
fuel its caller has left, and the caller goes on with what the callee gives
back. A callee that runs out of fuel ends the run that way. Its UB and stuck
paths are its caller's (ADR-2026-11-02-0836).

A call has no op-level rule. Its meaning is its callee's run. The interpreter
runs the callee of every op that has one before it looks at `denote`.
`Core.Op.denote?` gives `none` for `call`, but `call` does not count as an op
without rules (ADR-2026-11-02-1514).

The spec's meaning of a run is `Func.run` in the set monad `SetM`. A program
cannot list a predicate's members, so the spec also has `ChoiceTree`, a monad
whose computations are trees (`lean/Fir/Execution/ChoiceTree.lean`). A leaf
ends a path with a result, with UB, or with no outcome for a reason.
A node `choose w k` has a subtree for each `w` bits. The core dialect's rules
are written once for any monad, and run in `ChoiceTree Core.Op`.

`ChoiceTree.toSet` maps a tree to the set of ways its paths end. It is a
monad morphism, and a path with no outcome adds nothing. `Func.run_map`
proves that such a morphism carries a run in one monad to the run in the
other. `Core.mapsDenote` proves that the core rules in the tree map to those
in `SetM`. `ChoiceTree.explore` and `ChoiceTree.script` are the two walks,
proved sound once for any tree. `Core.exhaustive_outcomes` and
`Core.scripted_outcomes` state the results for the core dialect
(ADR-2026-10-30-2217).

A new op family adds its rule to `Core.Op.denote?` or `Core.Op.exit?`, and
`Core.mapsDenote` covers it. A new effect needs its node in the tree, its
image in the set monad, and its case in the morphism's proofs
(ADR-2026-10-30-2217). Calls need none of these, since the interpreter's
call path uses only `pure`, `bind` and `liftExcept` (ADR-2026-11-02-0836).

`Core.Op.denote?` and `Core.Op.exit?` give each core op its family's rule, or
`none` while its family has not landed. `call` gives `none` too, but its
meaning is its callee's run (ADR-2026-11-02-1514). In `DialectDenote CoreDialect SetM`,
an op without rules has no outcome: the empty set on every operand vector.
Only totality, `ReturnsOnDefined`, progress and the lawful class reject a
missing rule. `PropagatesPoison`, `OpMonotone`, `NeverStuck` and
`FuelMonotone` hold trivially there. So none of them is stated of such an op,
or of a function that reaches one (ADR-2026-10-30-1855).

## What the harness takes from a run

A native result passes when it refines one outcome of the run's set. A poison
outcome matches any native value (ADR-2026-10-29-2017, ADR-2026-10-31-0003). A stuck path or a
tool error fails a differential test. UB, or fuel exhausted on any path,
makes it invalid (ADR-2026-10-30-2135, ADR-2026-10-31-0003).

Every differential test runs in exhaustive mode at its fuel budget and the
default choice budget. A test past that budget is invalid unless it declares
its allowed results. Each declared result carries a witness choice sequence,
and scripted mode must reproduce the values from it. Within the budget, the
set must be exactly the declared results. Past the budget, seeds 0 to 31 run
in sampled mode, and each must give a declared result (ADR-2026-10-31-0003).
The seeded checks are by sampling, so they can miss a rare outcome
(ADR-2026-10-29-2017). The full rules belong to the testing-and-harness area.

A poison argument works in differential tests too. Native code holds no
poison, so it runs on stand-ins in each poison argument's place. The
stand-ins are the boundary bit patterns: 0, 1, all ones, the signed minimum
and the signed maximum. Native code runs once on each combination, up to
`5 ** k` runs for `k` poison arguments. Each result is judged against
`fir-ref`'s outcomes on the poison. The test passes when every result passes
(ADR-2026-11-03-1847).

Past the choice budget, a failing vector gets one more check. The harness
runs `fir-ref` on that vector, exhaustively or on each seed. UB or a path out
of fuel there makes the test invalid. Otherwise the failure stands
(ADR-2026-11-03-1847).

## How fir-ref stays equal to the spec

fir has no nesting limit. So `fir-ref` must give a verdict on a text nested
to any depth, without a stack overflow. The spec's functions stay readable
recursive definitions in `lean/Fir/`, and the proofs about them hold for what
`fir-ref` runs (ADR-2026-10-30-1450).

Some spec functions on its path take stack per level or more than linear
time. For each of them, `fir-ref` runs an implementation proved equal to it.
The implementation is a loop whose recursive calls are all tail calls. It keeps
what is left to do on an explicit stack of frames. It writes its output into
one accumulator. It is defined by well-founded recursion on a measure of its
frames, so it is total and has no fuel (ADR-2026-10-30-1450).

Each implementation is registered with `@[csimp] theorem : @specFn =
@fastFn`. The proofs use no `sorry`, `partial`, `unsafe`, `implemented_by` or
`native_decide`. They use only `propext`, `Classical.choice` and
`Quot.sound`, which the Lean build checks. The implementations live in
`lean/FirRef/`, which the document does not render. `lean/Fir/` does not
change for them (ADR-2026-10-30-1450).

`@[csimp]` acts only on code compiled after the theorem is in scope. So
compile order is part of the rule (ADR-2026-10-30-1450):

- `FirRef.Fast` imports every module that registers such a theorem, and
  `FirRef.Utf8` imports `FirRef.Fast`.
- `FirRef.Main` and `FirTest` import `FirRef.Utf8`.
- A module of `FirRef` that calls the spec's parser or printer must import
  `FirRef.Fast`, directly or through `FirRef.Utf8`.
- A theorem reaches an implementation only if the implementation's own module
  imports it.

The run modes are an exception to the `FirRef.Fast` rule. Their theorems
name the core dialect, and in `lean/FirRef/` only `fir-ref`'s command line
may (ADR-2026-11-03-0600). So they sit in `FirRef.Run`, which `FirRef.Fast`
does not import (ADR-2026-11-04-2132).

A change to a spec function breaks its theorem's proof, and so the build,
until the implementation follows. The `#guard` checks and `#eval`s of
`FirTest` run the implementations. The checks inside `lean/Fir/` run the
spec's definitions. The evidence that `fir-ref` runs an implementation is in
the C that Lean emits under `lean/.lake/build/ir/FirRef/`
(ADR-2026-10-30-1450, ADR-2026-11-04-2132).

A new fast path needs the depth rule or a case that is clearly too slow. The
existing speed-only ones stay: each is proved equal to the spec, and removing
one makes `fir-ref` far slower (ADR-2026-11-09-1941).

### Printing

`FirRef.printAttr` stands for `Attr.print`, and `FirRef.printModule` stands
for `Module.print` (ADR-2026-10-30-1450). `FirRef.printDecimal` stands for
`printInt`, through `@[csimp] theorem printInt_eq_printDecimal`. It splits a
number at powers of ten and computes each power once, as a square. Every
integer that `fir-ref` writes in a module or a run result goes through it.
`FirRef.PrintAttr` imports `FirRef.PrintInt`, so that `printAttrs` is compiled
after the theorem. The text grows in one accumulator, appended to in place
(ADR-2026-11-03-1603).

`scripts/check-fir-ref.sh test` checks the limit: it computes `2^16777214 - 1`
and reprints a module with it. Some spec functions still take time quadratic
in an integer's digits: `Tok.describe`, `readNat` and `Ty.decode`. They meet a
long integer only in a text that does not parse or decode
(ADR-2026-11-03-1603). `fir-ref` does not run the spec's `lexAt`, because it
lexes over positions (ADR-2026-11-03-1810).

### Lexing and reading

`FirRef.parse` replaces `Fir.parse`, which the spec compiles before any
theorem of `FirRef` (ADR-2026-10-30-1450). `FirRef.parse` is `readText` then
`Text.decodeModule`. `parse_eq_parse` is proved from `readText_eq`
(ADR-2026-11-03-1810).

`fir-ref` lexes tokens from `String` positions as the readers reach them. It
keeps neither a `List Char` nor a `List Token`. A `LexCursor` holds its next
token, already lexed, so each token is lexed once. The readers are written
once over a `Cursor` class, and each is proved to give what the spec's reader
gives, errors included. On a `List Token` they give `FirRef.readModule`, and
on a `LexCursor` they give `FirRef.readText` (ADR-2026-11-03-1810).

Accepted texts take one pass. Only when the readers fail does `FirRef.lexCheck`
run the lexer over the whole text. Its error, if any, is the parse error, and
otherwise the readers' error is. So a lexer error is still reported before
any reader error. A text with a late lexer error is slower than with the
spec's lexer and readers. The human accepted that cost (ADR-2026-11-03-1810).

`fir-ref run` reads each argument and each choice with `FirRef.argAttrP`, over
positions. It lexes at most two tokens and takes no stack per character.
`@[csimp] theorem argAttr_eq_argAttrP` proves it equal to `FirRef.argAttr`,
the reading by the spec's lexer. No function of the spec's lexer is reachable
from `fir-ref`'s `main` (ADR-2026-11-05-0806).

### Running

`FirRef.Machine.advance` runs the steps of a run in a loop of tail calls. Its
state is what the running function has left to do, plus one frame for each
waiting caller. Each step is one case of `Func.runOps`'s definition and calls
the same functions. `Machine.advance_tree` proves that where the machine
stops stands for the spec's tree of the state (ADR-2026-11-04-2132).

`Machine.scripted`, `Machine.exhaustive` and `Machine.sampled` walk the
machine's states in loops of tail calls. For every dialect, each is proved to
give what `ChoiceTree.script`, `explore` or `sample` gives on the tree of the
run. `FirRef.Run` registers them for the core dialect, over `Core.scripted`,
`Core.exhaustive` and `Core.sampled`. `fir-ref run` reports fuel exhaustion
at any budget. Its frames and environments are on the heap, so a deep
recursion costs memory, not stack (ADR-2026-11-04-2132).

A new mode of `fir-ref run` needs its own walk of the machine and its own
`@[csimp]` theorem. Code that calls the spec's modes and does not import
`FirRef.Run` still runs the spec's code (ADR-2026-11-04-2132).

The machine keeps its values in `FirRef.Bindings`. `young` is a list of the
latest values, in front of `old`, a `Std.TreeMap` that binds each name once.
A lookup searches `young`, then `old`. A lookup that passes more than `deep`
= 128 entries adds every entry it passed to a debt. When the debt exceeds `rent` = 32 times
the length of `young`, `young` moves into `old`. `rent` and `deep` are not
rules of fir, and any values give the same results (ADR-2026-11-05-0442).

Each operation on `Bindings` is proved to fit the spec's operation on `Env`,
with the same errors and messages. `Machine.runOps_congr` proves that a run
depends on its environment only through lookups. Some inputs are slower than
on the spec's list, and the human accepted that (ADR-2026-11-05-0442).

## The command line

`fir-ref`'s command line follows `funk`'s, so the harness compares the two
with no translation. A change to `funk`'s exit status or parse-error line
needs the same change in `fir-ref` (ADR-2026-10-30-1425). A change to
`funk`'s report schema needs the same change in `fir-ref validate`, and a new
ADR (ADR-2026-10-30-1741).

The form is `fir-ref COMMAND ...`. In every command, a FILE of `-` is standard
input, and `--` ends the options. In `fmt` and `run`, a parse error is one line
on standard error, `FILE:LINE:COL: parse error: REASON`. `fir-ref validate`
reports it as a JSON diagnostic on standard output (ADR-2026-10-30-1741). Bytes
that are not UTF-8 are a
parse error at the first byte of the first sequence that is not well formed
(ADR-2026-10-30-1425).

### fmt

`fir-ref fmt [--check] FILE...` parses each file with the core dialect. It
prints it in canonical form with the spec's printer. `--check` prints the name
of each file that is not canonical instead. The exit status is 0 when every
file is accepted, and canonical under `--check`. It is 1 when one is rejected,
or not canonical under `--check`. It is 2 on a usage or I/O error
(ADR-2026-10-30-1425).

### validate

`fir-ref validate FILE...` parses each file with the core dialect and runs
`Module.problems`. A FILE of `-` may appear at most once. It has no options,
and its output is always JSON (ADR-2026-10-30-1741).

It writes one object per file, on one line, in the order of the files:
`{"file": ..., "verdict": ..., "diagnostics": [...]}`. This is the schema of
`funk verify --json`. `verdict` is `accepted`, `parse-error`,
`validation-error` or `io-error` (ADR-2026-10-30-1741).

A diagnostic has a `kind` and a `message`. A parse error adds `line` and
`column`, in UTF-8 bytes from 1, and only the parser's first error appears. A
validation error adds `func`, `block`, `op` and `loc`, each `null` when it
does not apply. There is one validation error for each problem the check
finds, in the check's order (ADR-2026-10-30-1741).

The exit status is 0 when every file is accepted and 1 when one is rejected.
It is 2 on a usage or I/O error, and the largest status over the files wins.
A file that cannot be read still gets its report, with `io-error`
(ADR-2026-10-30-1741). The harness compares verdicts. On a text with one
parse error it also compares `line` and `column`. Messages and placement are
for people (ADR-2026-10-30-1741).

### run

The full form is `fir-ref run [--fuel N] [--choices C,C,...] [--seed S]
[--exhaustive [--choice-bits B]] FILE @FUNC [ARG...]`. Options come anywhere
before `--`, and each takes the next argument as its value
(ADR-2026-10-30-2218, ADR-2026-10-31-0002).

`fir-ref run` parses FILE with the core dialect, without validating it, and
runs the function. A `return`, `ub` or `fuel-exhausted` result means something
only for a module that `fir-ref validate` accepts. `@FUNC` is the symbol as
fir's text writes it, quoted exactly when it is not a word
(ADR-2026-10-30-1856).

**Arguments.** There is one per parameter, spelled as a `const` of the
parameter's type: `true` or `false` at `i1`, and signed decimal at every other
width. Decimals have no leading zeros, no `+` and no `-0`, and are in the
type's range (ADR-2026-10-30-1856). A float of `float<e,m>` is spelled as its
constants are, as `1.0` or `0x7fc00000`, and a float result is written the same
way (ADR-2026-11-11-1438). `poison`, spelled exactly so, is an argument of any `iN`
and of any float type. It is no argument of `ptr`, which has no values. It is
not a choice either, since `freeze` chooses a value (ADR-2026-11-03-1847).

**Fuel.** `--fuel N` gives N steps, one for each op run, terminators included.
N is ASCII decimal digits, and anything else is a usage error. The default is
1,000,000 (ADR-2026-10-30-1856).

**Scripted mode** is the default. `--choices` gives the sequence, in the order
the run makes the choices, separated by commas with no spaces. Each is spelled
as a constant of its choice's type. `freeze` at `iN` makes a choice of type
`iN`. The empty text is the empty sequence, which is the default
(ADR-2026-10-30-2218).

The result is one JSON object on one line, with a `kind`. Its `choices` field
counts the choices the path made (ADR-2026-10-30-1856, ADR-2026-10-30-2218):

- `{"kind":"return","values":["V1","V2"],"choices":N}`: each value is spelled
  as the arguments are, or is `"poison"`.
- `{"kind":"ub","reason":"...","choices":N}`: immediate UB.
- `{"kind":"fuel-exhausted","choices":N}`: the run used all its fuel.
- `{"kind":"stuck","reason":"...","choices":N}`: the run reached a case that
  validation rules out.

Reasons are for people. Tools compare the kind and the values only
(ADR-2026-10-30-1856).

**A sequence that does not fit** is an argument error, never an outcome. It is
one line on standard error, `fir-ref: @f: the choices do not fit the run:
REASON`, nothing on standard output, and exit status 2. The sequence may be
too short or too long, or hold a value that is not a constant of its choice's
type (ADR-2026-10-30-2218).

**Exhaustive mode** is `--exhaustive`. It tries a choice's values from zero up,
read as unsigned. `--choice-bits B` bounds the bits that one path chooses in
all, and is 16 by default. `--choices` with `--exhaustive`, and `--choice-bits`
without it, are usage errors (ADR-2026-10-30-2218).

Its result is `{"kind":"outcomes","choices":N,"outcomes":[O,...]}`. Each `O`
is one way a path ends, without `choices`. Each outcome appears once, in the
order the paths first reach it. `N` is the most choices one path made. The
exit status is 1 when a path is stuck, and 0 otherwise (ADR-2026-10-30-2218).

When a path would choose more than B bits, the result is
`{"kind":"choice-budget-exceeded","budget":B}` with exit status 0. The budget
is checked first, even when a path reaches an op without rules
(ADR-2026-10-30-2218). Within its budget, exhaustive mode lists exactly the
run's outcomes. On a sequence that fits, scripted mode gives one of them
(ADR-2026-10-30-2218).

**Sampled mode** is `--seed S`. It follows the path on which a generator,
seeded with S, draws each choice as the run makes it. S is ASCII decimal
digits, from 0 to 2^64 - 1. `--seed` does not go with `--choices` or
`--exhaustive` (ADR-2026-10-31-0002).

The result is the scripted result with one more field, `sequence`: the values
drawn, in order, spelled as `--choices` takes them. The generator is
SplitMix64 (`lean/FirRef/Sample.lean`). One draw in four gives a boundary bit
pattern. A seed draws the same values on every machine. `Core.sampled_outcomes`
proves that a sampled outcome is a member of the run's set. That the printed
spelling reads back is tested, not proved (ADR-2026-10-31-0002).

**Exit status of a run.** It is 0 for `return`, `ub` and `fuel-exhausted`. It
is 1 for `stuck`, and for a text that does not parse. It is 2, with nothing on
standard output, for each of these (ADR-2026-10-30-1856):

- a usage or I/O error;
- a function the module does not have;
- a wrong number of arguments;
- an argument that is not a value of its type;
- an op without execution rules.

**An op without rules.** A run that reaches one prints one line on standard
error, `fir-ref: @f: OP has no execution rules yet`, and nothing on standard
output. The exit status is 2. `fir-ref` never reports such a run as stuck or
as UB (ADR-2026-10-30-1855). The same error holds in scripted mode, in sampled
mode, and in exhaustive mode within the budget (ADR-2026-10-30-2218,
ADR-2026-10-31-0002).

**Messages.** A usage error prints its message, a blank line and the usage on
standard error. Every other error prints one line. In a `fir-ref: ...`
message, each control character from the command line shows as `\xHH`.
Strings in the JSON escape as `fir-ref validate`'s and `funk`'s reports escape
them (ADR-2026-10-30-1856).
