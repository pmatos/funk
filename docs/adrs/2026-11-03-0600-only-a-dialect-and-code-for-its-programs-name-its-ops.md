# Only a dialect, and code that builds, lowers or runs its programs, name its ops; tests in Rust and Lean keep it so

Status: accepted; refined by ADR-2026-11-03-1617
Tier: direction; area: semantics

## Context

G0 (ADR-2026-10-29-2016) keeps fir open to dialects that M0 does not
have. For M0 it asks for four things, which
[#23](https://github.com/pmatos/funk/issues/23) checks on `main`: no
closed `enum` of ops in Rust; no per-op code in the parser or the printer
of either language, since a dialect's `decodeOp` and `opAttrs` hold its
text; a Lean semantics parameterized over the dialect; and a poison class
declared for every op (ADR-2026-10-30-0818).

Some code must name ops: the core dialect itself, and the x86-64 backend,
which lowers core programs. So the check needs a line between the code
that may name ops and the code that may not. A check that a person runs by
hand does not stop a later change from reopening the door.

The check found all four points held on `main`, but one in part:
`Core.Op.poisonClass` named the six exceptions and gave the other 18 core
ops their class through a case for the rest. So a new op got a class that
no one declared for it.

## Decision

### Where the line is

_Generic code_ sees every op alike and must not know the ops of any
dialect. It is:

- in Rust, all of `funk-ir`'s `src/` but `src/dialects/`, the module
  generator (`src/generate.rs` and `src/generate/`) and the unit tests
  (`#[cfg(test)]` items and the files of `#[cfg(test)]` modules): the IR,
  the registry, the parser, the printer and the verifier;
- in Lean, all of `lean/Fir/` but the core dialect's `lean/Fir/Core/` and
  the text chapter's example, `Fir/Text/Example.lean`, which is a core
  module; all of `lean/FirRef/` but `fir-ref`'s command line, which runs
  core programs: its entry point `Main`, its reports `Report`, and
  `fir-ref run` and its arguments, `Run` and `RunArgs`; and G0's own
  test, `lean/FirTest/G0.lean`.

Generic code reaches a dialect's ops only through the registry (`OpSpec`,
`TypeSpec`) or the dialect's classes (`DialectText`, `DialectSignature`,
`DialectValidation`, `DialectDenote`, `DialectCall`, `DialectPoison`). The
grammar's own words, such as `func`, `locs` and the kinds of location, are
not per-op code. Neither is an item's kind: a new kind of item is a new
`Item` constructor and a parser change (H4, H5).

Code that builds, lowers or runs the programs of one dialect may name its
ops: the dialect's own files, the module generator of the property tests,
the x86-64 backend (`crates/funk-x86-64/`: its lowering names each op
family, the rest of it reaches ops through the lowering, and any other op
is a diagnostic at the op), `funk`'s command line (`crates/funk/src/`,
which today reaches ops only by registering the core dialect,
`Registry::core()`), `fir-ref`'s command line, the tests and the corpus.

Two files of the text chapter end with the core dialect's corollaries of
results proved for every dialect: `Core.printThenParse` in
`Fir/Text/PrintParse.lean` and `Core.parse_wellFormed` in
`Fir/Text/ParseWellFormed.lean`. They may name the core dialect, but not
write its words.

Every op of every dialect declares its class through `DialectPoison`. The
core dialect lists each of its 24 ops by its constructor in
`Core.Op.poisonClass`, with no case for the rest. The Rust IR has no
semantics, so poison classes are Lean's alone (S7).

### How CI keeps it

- `crates/funk-ir/tests/g0.rs`, which `rust-test` runs. An empty registry
  knows no op: for each core op name `N`, the parser reports
  `unknown op N` and the verifier `op N is not registered`. An `Op` is
  built field by field with a name that no dialect registers, so the test
  stops compiling if the name stops being a string. A small lexer,
  `tests/g0_scan/`, reads the code of the generic modules, without
  comments and unit tests. The test fails when that code writes a word of
  the core dialect's text as a string (an op name from the core dialect's
  registration, a predicate, a flag, `exact`, `true`, `false`, `ptr` or an
  `iN`), names the `dialects` module in a path outside `lib.rs` and
  `registry.rs` (a field or a variable of that name is not the module), or
  declares an `enum` with two or more variants named after core ops. One
  such variant is not a closed set of ops: the spec's own `Exit` has
  `ret`.
- `scripts/check_g0.py`, which a new hook, `g0`, runs, with its tests in
  `scripts/test_check_g0.py` (hook `g0-test`). In the generic Lean files,
  it fails on a name with a part `Core` or `CoreDialect` (Lean's own
  `Lean.` names aside), on an import of a module that it leaves out, and
  on a string that is a word of the code of `lean/Fir/Core/Text.lean` or
  an `iN`. It reads raw strings, and the code inside an interpolated
  string, and skips comments and commands such as `#guard`. It also fails
  when a case of `Core.Op.poisonClass` is not one op's constructor, so a
  case for the rest cannot come back. The dialects' directories are one
  constant, `DIALECT_DIRS`, so the ADR that adds a dialect moves the line
  there.
- `lean/FirTest/G0.lean`, which `fir-spec` and `fir-ref-test` build. It
  restates for an arbitrary dialect, with the spec's own proof or
  definition: the parser and the printer, `fir-ref`'s copies of them, both
  round trips, that the parser gives well-formed modules and that valid
  modules are well formed, the validation check, the interpreter, and the
  theorems of fuel monotonicity, progress, no stuck path and poison
  propagation. Narrowing one of those definitions or theorems to the core
  dialect breaks the build, and `g0` fails if a statement of `G0.lean`
  names the core dialect. With no case for the rest in
  `Core.Op.poisonClass`, a new core op does not build until it declares
  its class.

Each check covers a place unless the line above excludes it, so a new file
is checked.

## Alternatives

- **Review by hand.** Not durable.
- **One script for both languages.** The Rust test takes the core
  dialect's words from its live registration; a script would need a copy.
- **Lean theorems alone.** They show that the definitions take any
  dialect, but a generic definition could still test an op's name as a
  string and keep every theorem true.
- **Moving the two corollaries into `lean/Fir/Core/`.** It changes the
  spec's chapters for no gain: the corollaries follow the generic results
  and write none of the core dialect's words.

## Consequences

- A change that puts per-op code in generic code fails CI, naming the file
  and the word.
- The source checks read words, not meaning: code that builds a core op's
  name from pieces would pass them. They stop plain per-op code; the
  theorems, the empty registry and the test dialects of
  ADR-2026-10-30-1146 and ADR-2026-11-09-2306 check behaviour.
- Generic code that needs a word of the core dialect's text for a reason
  other than per-op code must move behind a dialect's class, or a new ADR
  must move the line.
