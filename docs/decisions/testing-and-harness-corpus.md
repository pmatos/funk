# Current decisions: the test corpus

This page continues [testing-and-harness.md](testing-and-harness.md). It says
what holds today for the corpus of `tests/fir/`, its coverage matrix and the
cases ported from LLVM. It is the record: when this page and an ADR disagree,
the page wins, and the ADR is fixed or deleted (ADR-2026-11-09-1610).

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

Rejected: metadata in comments of the `.fir` text, which would not be
canonical, and JSON sidecars, which have no comments (ADR-2026-10-30-2050).

A test is one inline table in the sidecar's `tests` list. Its keys are `func`,
`args`, `fuel` (1,000,000 steps by default) and `expect`
(ADR-2026-10-30-2050). The keys `results` and `choices` come from
ADR-2026-10-30-2135.

A module with a differential test builds whole, since `funk build` is all or
nothing. A function that the backend does not lower goes in a module whose tests
are all interpreter-only. A corpus text uses only the ops that both tools have.

A must-reject text is a `[[reject]]` table with `verdict`, `rule` and `text`. The
verdict is `parse-error` or `validation-error`. The rule is the one it breaks, in
words. When the ops cannot break a rule alone, the text breaks a second rule too,
and `rule` names both. A text that the hooks keep out of files is a TOML basic
string with escapes, and one that is not UTF-8 is a list of strings and bytes.

A new test is a new line or file in `tests/fir/`, with no code change
(ADR-2026-10-30-2050).

### The tests of the select rewrites

ADR-2026-10-30-0818 forbids two rewrites of `select`, and each has a named test.
`select-and` tests the rewrite into `and`. `select-cond-br`, and
`FirTest.Branch` in Lean, test the rewrite into `cond_br`, which came with #19,
since #16 had no `cond_br`.

## The coverage matrix

A generated matrix counts the corpus's tests of each cell (ADR-2026-11-03-0557).
A hook fails when the matrix is stale or a cell has no test.

A cell is an op instance of the core dialect at a width, on one side. An op
instance is the op with its flag set, `exact` choice or `icmp` predicate. A flag
that the spec does not give an op is not a cell, and a constant's value is not
part of its cell. Width changes are cells for each pair of widths. Passed and
returned values are cells for none, one or several values.
`scripts/harness/cells.py` holds the exact set.

The differential side has `i1`, `i8`, `i16`, `i32`, `i64` and `i128`. The
interpreter-only side adds `i7` and `i33`. Ops at other widths count towards no
cell.

The float ops have a table of their own, at each float format of a side;
[testing-and-harness-floats.md](testing-and-harness-floats.md#the-coverage-matrix)
says which (ADR-2026-11-03-0557).

A test exercises each op of the function it runs and of every function it calls,
directly or through others. It also exercises the `func` cell of its results. The
count is static, so a block that the arguments skip still
counts. No check reads the outcome. So whoever fills a cell writes a test whose
path runs the op and whose outcome depends on what the op computes. A test that
only passes poison into the op checks how poison goes through it, not the op.

Rejected: a trace mode in `fir-ref` to count only the ops a run takes, a change
to its command line of its own, and cells by file name, since a name says what a
module is for, not what its tests run (ADR-2026-11-03-0557).

`scripts/harness/coverage.py` writes the matrix to `docs/coverage/README.md`, and
`coverage.py --write` rewrites it. A pull request that changes the corpus
regenerates it, after merging `main` when `main` changed the corpus too. A new
op, flag or predicate fails the unit tests until `cells.py` has its cells. The
`coverage-matrix` hook then fails until the corpus tests them. A new side or
width is a change to ADR-2026-11-03-0557 and to `cells.py`. A matrix that would
pass the file-size budget splits by side into files of `docs/coverage/`.

### The cells of poison

`poison` has its own rule, since no differential test can tell it from `const 0`
(ADR-2026-11-03-0557). It is a cell at each width of each side, as `const` is. A
differential test fills its cell when the op runs as native code and the result
refines that of `fir-ref`, whether the poison reaches the result or not. An
interpreter-only test fills its cell when the outcome observes the poison:
`fir-ref` returns it, a result it decides, a value that `freeze` chooses for it,
or UB that it causes. Authors and reviewers keep at least one such test in each
interpreter-only cell, since no check does. `tests/fir/canonical/poison-op-iN`
fills these cells.

## Tests ported from LLVM

Ported cases live in `tests/fir/llvm/` (ADR-2026-11-03-0643). Each is a canonical
valid module and its sidecar. LLVM's licence sits beside them as `LICENSE.TXT`,
and `README.md` is the notice that lists each module with its source. `NAME` is
the LLVM directory (`instsimplify`, `instcombine`, or `x86` for `CodeGen/X86`)
and the stem of the test file, with a suffix where one file is split.

A sidecar has `source`, and each test has `from`. Each sidecar's comment starts
"Derived from LLVM" and says how its cases were rewritten. Each function's ops
carry a location, a source range of the LLVM test file. Every module names one
llvm-project commit, `7a941dfb2877a0b8cf30323fefa85ad019e0b0f5`. Moving to a
newer commit means moving every module, or editing ADR-2026-11-03-0643 to allow
several. No LLVM file is in the repository, only the hand translations.
`scripts/harness/corpus.py` checks that `LICENSE.TXT` and `README.md` are
present, the licence's SHA-256, a sidecar for each module, a well-formed
`source`, a `from` on each test, that no other file is there, and that at most
one commit is named (ADR-2026-11-03-0643). The ported modules are canonical
texts, so every reader of the corpus reads them.

Rejected: `canonical/llvm-*.fir` with provenance in comments only. The licence
would not sit beside the files it covers, and nothing would check a source
(ADR-2026-11-03-0643).

### How cases are chosen and rewritten

A case comes in when fir's M0 ops can express it and it tests an integer edge
case. The sources are `Transforms/InstSimplify/`, the `apint-*` and `div-i1`
tests of `Transforms/InstCombine/`, and the tests of `i128`, division and shifts
of `CodeGen/X86/`. A function that uses a vector, floating point, a pointer,
memory, an intrinsic, `switch` or `undef` is left out. So is one that calls a
function its file does not define. From each file the port takes each kind of
fold, and each negative test that shows a flag or a bound at work. It also takes
every case at an odd width or at `i128`. A function that only repeats one of
those with other constants, commuted operands or another predicate is left out.
A later dialect with vectors, memory or more flags can bring the left-out
functions in under the same rules.

LLVM's text is rewritten into fir by fixed rules. Unreachable blocks are
deleted, phis become block arguments, and labels are written `^name`. LLVM's
names of functions and blocks are kept, and so are most of its names of values.
A constant operand becomes a `const` op, with fir's signed spelling. LLVM's
`poison` constant of type `iN` becomes `%p: iN = poison`, at the location of the
ops that use it. A flag that fir's op lacks is dropped only where it can never
give poison in that function, and the sidecar says why. Where it can, the
function is left out. A result that a code generation test stores through a
pointer is returned, a struct of two values is two results, and parameter and
function attributes are dropped. Each sidecar's comment says which rewrites its
cases needed and which functions are left out.

Each fold becomes runs of the input function at chosen arguments. Where the
folded form has ops, it is ported as `@NAME.folded` and runs on the same
arguments. Every expected value comes from LLVM's statement or separate working,
never from a run of `fir-ref`, so a run that disagrees fails. A run whose module
builds and whose result is a value is differential and declares that result. A
run that gives poison or UB, or has a width the backend does not lower, is
interpreter-only.

LLVM's CHECK lines fold some divisions that are UB to poison, where `fir-ref`
reports UB. LangRef makes those divisions UB too, so the poison is LLVM's
refinement of that UB, not a difference of semantics.

### Names the spelling check rejects

A function whose name the repository's spelling check rejects is still ported.
It keeps LLVM's name with the misspelled word spelled correctly, and nothing
else in the name changes. The misspelled word is written nowhere in the
repository. Its tests' `from` name the function by its file and lines, and say
that LLVM's name misspells the word. The spelling check, its configuration and
its exclusions get no exception. The human ruled this on 2026-11-03 (#124).

Rejected: an exception to the spelling check for LLVM's word, which the human
ruled against, and leaving such functions out, which loses folds for a reason
unrelated to what they test.
