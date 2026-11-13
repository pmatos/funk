# Current decisions: fir-ref's command line

This page continues [fir-ref.md](fir-ref.md). It says what `fir-ref`'s
commands take and print. It is the record: when this page and an ADR disagree,
the page wins, and the ADR is fixed or deleted (ADR-2026-11-09-1610).

## Shared by every command

`fir-ref`'s command line follows `funk`'s, so the harness compares the two
with no translation. It reads verdicts from the exit status, and the position
of a parse error from `LINE:COL`. A change to `funk`'s exit status or
parse-error line needs the same change in `fir-ref`. A change to `funk`'s
report schema needs the same change in `fir-ref validate`, in the same PR,
which edits this page and
[rust-ir-and-tools-funk.md](rust-ir-and-tools-funk.md#report-format) together.

The form is `fir-ref COMMAND ...`. In every command, a FILE of `-` is standard
input, and `--` ends the options. In `fmt` and `run`, a parse error is one line
on standard error, `FILE:LINE:COL: parse error: REASON`, with FILE as given.
`fir-ref validate` reports it as a JSON diagnostic on standard output. Bytes
that are not UTF-8 are a parse error at the first byte of the first sequence
that is not well formed, as in `funk`.

A usage error prints its message, a blank line and the usage on standard
error. Every other error prints one line. In a `fir-ref: ...` message, each
control character from the command line, below 0x20 or 0x7f, shows as `\xHH`,
so the message stays on one line.

Rejected: a format of `fir-ref`'s own. The harness would translate each tool's
output before comparing them.

## `fir-ref fmt`

`fir-ref fmt [--check] FILE...` parses each file with the core dialect. It
prints it in canonical form with the spec's printer, `Module.print`. `--check`
prints the name of each file that is not canonical instead. The exit status is
0 when every file is accepted, and canonical under `--check`. It is 1 when one
is rejected, or not canonical under `--check`. It is 2 on a usage or I/O error.
The harness uses it to check that both sides print each non-canonical text of
`tests/fir/` as its canonical sibling.

Rejected: `--write` and `--json`, as `funk fmt` has. `fir-ref fmt` rewrites no
files, and its verdict is its exit status.

## `fir-ref validate`

`fir-ref validate FILE...` parses each file with the core dialect and runs
`Module.problems`. A FILE of `-` may appear at most once. It has no options,
and its output is always JSON.

It writes one object per file, on one line, in the order of the files, in the
schema of `funk verify --json`: `file`, `verdict` and `diagnostics`, with the
fields and escapes of
[rust-ir-and-tools-funk.md](rust-ir-and-tools-funk.md#report-format). Only the
parser's first error appears, and there is one validation error for each
problem the check finds, in the check's order.

The exit status is 0 when every file is accepted and 1 when one is rejected.
It is 2 on a usage or I/O error, and the largest status over the files wins.
A file that cannot be read still gets its report, with `io-error`.

The harness compares verdicts. On a text with one parse error it also compares
`line` and `column`. Messages, the `func`, `block`, `op` and `loc` fields and
the number of diagnostics are for people: the spec's check reports each rule a
module breaks, and `funk` may report one diagnostic for two (#59).

Rejected: `--json`, as `funk verify` has. `fir-ref validate` exists for tools
and has no text output to choose from.

## `fir-ref run`

The full form is `fir-ref run [--fuel N] [--choices C,C,... | --exhaustive
[--choice-bits B] | --seed S] FILE @FUNC [ARG...]`. Options come anywhere
before `--`, and each takes the next argument as its value. An argument such as
`-5` is not an option.

`fir-ref run` parses FILE with the core dialect, without validating it, and
runs the function. A `return`, `ub` or `fuel-exhausted` result means something
only for a module that `fir-ref validate` accepts: the interpreter does not
check every rule of validation. The harness runs only modules that `fir-ref
validate` must accept. `@FUNC` is the symbol as fir's text writes it, quoted
exactly when it is not a word: `@add3`, `@"a b"`.

Rejected: validating first. Then `fir-ref run` could never report a run as
stuck, and the interpreter's stuck paths could not be tested end to end.

### Arguments and fuel

There is one argument per parameter, spelled as a `const` of the parameter's
type: `true` or `false` at `i1`, and signed decimal at every other width.
Decimals have no leading zeros, no `+` and no `-0`, and are in the type's range.
A float of `float<e,m>` is spelled as its constants are, as `1.0` or
`0x7fc00000`, and a float result is written the same way (ADR-2026-11-11-1438).
`fir-ref` reads each argument as the spec's lexer and `Core.Op.decode` read it
(see [lexing and reading](fir-ref-fast-paths.md#lexing-and-reading)).

`poison`, spelled exactly so, is an argument of any `iN` and of any float type
(`FirRef.readArg`). It is no argument of `ptr`: a run starts with no
allocation. It is not a choice either, since `freeze` chooses a value. The
human ruled on 2026-11-03 that `fir-ref run` takes `poison` (#123); the
harness's use of it is in
[testing-and-harness.md](testing-and-harness.md#poison-arguments).

`--fuel N` gives N steps, one for each op run, terminators included. N is
ASCII decimal digits, and anything else is a usage error. The default is
1,000,000. The option exists because the harness gives each test its own
budget; it was taken without a ruling, as #10's text has no fuel option.

### Results

The result is one JSON object on one line of standard output, with a `kind`.
Its `choices` field counts the choices the path made, `0` when it made none:

- `{"kind":"return","values":["V1","V2"],"choices":N}`: each value is spelled
  as the arguments are, or is `"poison"`. A function with no result prints
  `"values":[]`.
- `{"kind":"ub","reason":"...","choices":N}`: immediate UB.
- `{"kind":"fuel-exhausted","choices":N}`: the run used all its fuel.
- `{"kind":"stuck","reason":"...","choices":N}`: the run reached a case that
  validation rules out.

Reasons are for people. Tools compare the kind and the values only, and
`"poison"` matches any native value. Strings escape as `fir-ref validate`'s
and `funk`'s reports escape them.

Rejected: bare JSON numbers. `i1` would read as booleans, and wide values lose
precision in many JSON readers.

### Scripted and exhaustive modes

**Scripted mode** is the default. It follows the one path that `--choices`
names: the choices in the order the run makes them, separated by commas with
no spaces. Each is spelled as a constant of its choice's type, as arguments
are. `freeze` at `iN` makes a choice of type `iN`. The empty text is the empty
sequence, which is the default, so a run that makes no choice needs no option.
A witness of a test is a `--choices` text.

**A sequence that does not fit** is an argument error, never an outcome. It is
one line on standard error, `fir-ref: @f: the choices do not fit the run:
REASON`, nothing on standard output, and exit status 2. The run makes a choice
after the sequence ends, the sequence has values left when the path ends, or a
value is not a constant of its choice's type. A stale witness fails loudly. A
path that reaches an op without rules reports that error instead, even with
values left.

**Exhaustive mode** is `--exhaustive`. It tries a choice's values from zero up,
read as unsigned. `--choice-bits B` bounds the bits that one path chooses in
all, and is 16 by default, so at most 65,536 paths. `--choices` with
`--exhaustive`, and `--choice-bits` without it, are usage errors.

Its result is `{"kind":"outcomes","choices":N,"outcomes":[O,...]}`. Each `O`
is one way a path ends, without `choices`, a stuck path included. Each outcome
appears once, in the order the paths first reach it. `N` is the most choices
one path made. The exit status is 1 when a path is stuck, and 0 otherwise.

When a path would choose more than B bits, the result is
`{"kind":"choice-budget-exceeded","budget":B}` with exit status 0: a result,
which a tool tells apart from an error by its `kind`. The budget is checked
first, even when a path reaches an op without rules.

Within its budget, exhaustive mode lists exactly the run's outcomes, and on a
sequence that fits, scripted mode gives one of them (`Core.exhaustive_memOutcomes`,
`Core.scripted_memOutcomes`, over the runs with memory at the module's layout). Exhaustive mode is within its budget exactly when no
path chooses more than B bits (`ChoiceTree.explore_isSome_iff`).

Rejected: exhaustive mode by default. It would have changed every existing
run's output at once; a scripted default keeps a run that makes no choice as it
was. Also rejected: a JSON `kind` for a sequence that does not fit, since the
choices are arguments and a tool error never passes.

### Sampled mode

`--seed S` follows the path on which a generator, seeded with S, draws each
choice as the run makes it. S is ASCII decimal digits, from 0 to 2^64 - 1.
`--seed` does not go with `--choices` or `--exhaustive`.

The result is the scripted result with one more field, `sequence`: the values
drawn, in order, spelled as `--choices` takes them, so it can be pasted into a
test as a witness. The generator is SplitMix64 (`lean/FirRef/Sample.lean`). A
choice of `w` bits takes one 64-bit draw. One draw in four gives a boundary bit
pattern: 0, 1, all ones, the signed minimum or the signed maximum. Otherwise it
takes ⌈w/64⌉ more draws and keeps their low `w` bits. A seed draws the same
values on every machine; `lean/FirTest/Sample.lean` pins a few draws.

`Core.sampled_fits` proves that the values drawn are a sequence that fits the
run, so `Core.sampled_outcomes` follows from `Core.scripted_outcomes`: a
sampled outcome is a member of the run's set, whatever the generator. That the
printed spelling reads back is tested, not proved.

Rejected: Lean's `StdGen`. Its algorithm is the toolchain's to change. Also
rejected: a generator in the harness, which cannot know the choices' widths.

### Exit status and errors

The exit status is 0 for `return`, `ub` and `fuel-exhausted`. It is 1 for
`stuck`, and for a text that does not parse. It is 2, with nothing on standard
output, for each of these:

- a usage or I/O error;
- a function the module does not have;
- a wrong number of arguments;
- an argument that is not a value of its type
  (`fir-ref: 128 is not a value of type i8`);
- a sequence of choices that does not fit;
- an op without execution rules.

Rejected: exit status 0 for stuck. Stuck shows that the module is not valid,
which `funk`'s tools report with status 1.

**An op without rules.** A run that reaches one prints one line on standard
error, `fir-ref: @f: OP has no execution rules yet`, with the op as text writes
its name and attributes (`sub`, `add nsw`), and nothing on standard output. The
exit status is 2. `fir-ref` never reports such a run as stuck or as UB
([fir-ref.md](fir-ref.md#an-op-without-rules)). The same error holds in
scripted mode, in sampled mode, and in exhaustive mode within the budget.
