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
ADR-2026-10-30-2135. `work_item` gives the work-item that a kernel of a
device module runs as, and `func` names such a kernel by the path of its
modules, `@dev::@k`, as `fir-ref run` does; a test of either kind is
interpreter-only, since `funk build` builds no nested module's functions
(#212, stage 2; fir-ref-command-line.md#kernels-and-the-work-item). The
coverage matrix counts a kernel's test as any other (#406). This key was
proposed by #212, and the human accepted it on 2026-11-16 (Q4 on #212).

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

ADR-2026-10-29-2006 forbids two rewrites of `select`, and each has a named test.
`select-and` tests the rewrite into `and`. `select-cond-br`, and
`FirTest.Branch` in Lean, test the rewrite into `cond_br`, which came with #19,
since #16 had no `cond_br`.

## The coverage matrix

A generated matrix counts the corpus's tests of each cell (ADR-2026-11-03-0557).
A hook fails when the matrix is stale or a cell has no test.

A cell is an op instance of the core dialect at a width, on one side, or an
op of the `gpu` dialect in a dimension (below). An op instance is the op with its flag set, `exact` choice or `icmp` predicate; a float
op's fast-math flags are cells one by one, by the human's ruling of 2026-11-13
on #355
([testing-and-harness-floats.md](testing-and-harness-floats.md#the-coverage-matrix)).
A flag that the spec does not give an op is not a cell, and a constant's value is not
part of its cell. Width changes are cells for each pair of widths, `zext` and
`sext` to a wider one and `trunc` to a narrower one. Passed and returned values
are cells for none, one or several values.
`scripts/harness/cells.py` holds the exact set, the pointer table in
`pointer_cells.py`.
Its `catalog` expands ordered tables and rows with the actual cells and
explicit blanks for inapplicable pairs. Both cell enumeration and matrix
rendering consume that expansion; `coverage.py` owns presentation and counts,
not a second expansion of the taxonomy.

The differential side has `i1`, `i8`, `i16`, `i32`, `i64` and `i128`. The
interpreter-only side adds `i7` and `i33`. Ops at other widths count towards no
cell.

The float ops have a table of their own, at each float format of a side;
[testing-and-harness-floats.md](testing-and-harness-floats.md#the-coverage-matrix)
says which (ADR-2026-11-03-0557).

The ops of the `gpu` dialect have a table of their own, on the
interpreter-only side alone (`gpu_cells.py`, the catalog's `gpu` table, #406):
one row for each op and dimension, `gpu.work_item_id gpu.x` to
`gpu.num_work_groups gpu.z`, at `i32`, the one width its validation allows. A
kernel runs on `fir-ref` alone, so no differential test can fill a `gpu` cell.
A new op of `gpu`, such as the work-group allocation of #212's stage 3, fails
the unit test that reads `lean/Fir/Gpu/` until it has its rows, and then the
hook until a kernel test runs it. `tests/fir/canonical/gpu-dims.fir` fills
every row with ids and sizes that differ in each dimension. The human ruled on
2026-11-16 (#212, Q3) that #404 could skip kernel tests for a while and that
#406 counts kernel tests and `gpu` ops. That the cells are on the
interpreter-only side alone, at `i32` alone, is #406's choice, not a ruling.
Rejected: leaving kernel tests out, which leaves the ops that kernels run, and
every op of `gpu`, with no gate (ADR-2026-11-03-0557).

The pointer ops have a table of their own (`cells.POINTER_OPS`, the
catalog's `pointers` table): `ptradd` has a cell at each width of its integer,
the stack allocation `alloca` a cell at each width of the integer type it
allocates, `load` a cell at each width of the integer it loads, and
`store` a cell at each width of the integer it stores; each of the three
has one more cell, `ptr`, for a pointer of any memory (stage 4d-2b of
#231). Each side has them at its own widths: the backend lowers
pointers since stage 5 of #231, so the differential side has `i1` to
`i128` and `ptr`, filled by `tests/fir/canonical/memory-native.fir` and the
tests of `store` and `pointer-store` that return integer values. A test of
poison stays interpreter-only, since native code may give any value for it
and so pins nothing. A test that returns a pointer stays interpreter-only, since native code returns
an address, not a pointer of the spec, and so does one with a poison
pointer argument, which has no stand-in. A run's pointers come from
`alloca`, so the tests that fill the `ptradd` cells move real pointers, as
`tests/fir/canonical/memory-native.fir` does, and also pass poison
through it; its rule on pointers is checked in Lean too, in
`lean/Fir/Core/Pointer.lean` (#231).

`alloca`, `load` and `store` have one more cell each for every float
format of a side's floats in memory (`pointer_cells.MEMORY_FLOAT_*`, #264).
The backend sizes an `alloca` of floats but does not load or store a
float yet, so only the interpreter-only side has them, at `f16`, `bf16`, `f32`, `f64` and
`f128`, filled by `tests/fir/canonical/float-memory.fir`; stage 2 of #264
gives the differential side `f32` and `f64`. A float of a format without
an alias, such as `float(2, 1)`, counts towards no cell, as at every other
float op.

A test exercises each op of the function it runs and of every function it calls,
directly or through others. A function of a nested module, such as a kernel
`@dev::@k`, counts too, and its calls go to its own module's functions (#406).
It also exercises the `func` cell of its results. The count is static, so a
block that the arguments skip still counts. No check reads the outcome. So whoever fills a cell writes a test whose
path runs the op and whose outcome depends on what the op computes. A test that
only passes poison into the op checks how poison goes through it, not the op.

Rejected: a trace mode in `fir-ref` to count only the ops a run takes, a change
to its command line of its own, and cells by file name, since a name says what a
module is for, not what its tests run (ADR-2026-11-03-0557).

`scripts/harness/coverage.py` writes the matrix to `docs/coverage/README.md`, an
index, and to a page for each side beside it, `differential.md` and
`interpreter.md`: one file came within about 100 bytes of the file-size
budget, which the next `gpu` row would pass (#406).
`coverage.py --write` rewrites them. A pull request that changes the corpus
regenerates it, after merging `main` when `main` changed the corpus too. A new
op, flag or predicate fails the unit tests until `cells.py` has its cells. The
`coverage-matrix` hook then fails until the corpus tests them. A new side or
width is a change to ADR-2026-11-03-0557 and to `cells.py`.

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
the pinned commit's `llvm/LICENSE.TXT` but for the empty line that ends it,
which the `end-of-file-fixer` hook removes, and `README.md` is the notice that
lists each module with its source. `NAME` is the LLVM directory
(`instsimplify`, `instcombine`, or `x86` for `CodeGen/X86`) and the stem of the
test file, with a suffix where one file is split.

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
Where a port names a value anew, it does not use a name that LLVM gives another
value of the function. A constant operand becomes a `const` op: `i1` constants
are `true` and `false`, and other constants take fir's signed spelling, so
LLVM's unsigned `i64 13835058055282163710` is `-4611686018427387906`. LLVM's
`poison` constant of type `iN` becomes `%p: iN = poison`, at the location of the
ops that use it. A flag that fir's op lacks is dropped only where it can never
give poison in that function, and the sidecar says why. Where it can, the
function is left out. A result that a code generation test stores through a
pointer is returned, a struct of two values is two results, and parameter and
function attributes are dropped. Each sidecar's comment says which rewrites its
cases needed and which functions are left out.

Each fold becomes runs of the input function at chosen arguments: boundary bit
patterns, and values at the edge of the fold's condition. A run expects the
folded value where the input is defined, and the input's poison or UB where it
is not, which LLVM's value refines. Where the folded form has ops, it is ported
as `@NAME.folded` and runs on the same arguments. Where a file has only a RUN
line, the folded form is the one it asks for, written by hand. A negative test
runs on an argument where the fold would be wrong, if there is one. A negative
test, and a code generation test, whose CHECK lines are assembly, declares the
value its IR computes, worked out apart from `fir-ref`. Every expected value
comes from LLVM's statement or separate working, never from a run of
`fir-ref`, so a run that disagrees fails. A run whose module builds and whose
result is a value is differential and declares that result. A run that gives
poison or UB, or has a width the backend does not lower, is interpreter-only.

LLVM's CHECK lines fold some divisions that are UB to poison, where `fir-ref`
reports UB: `sdiv i8 -128, -1` and `srem i8 -128, -1`, and the division by a
`false` that both paths give in `div-i1.ll`'s `@*_by_zero_indirect_is_poison`
functions. LangRef makes those divisions UB too, so the poison is LLVM's
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
