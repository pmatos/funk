# Only a dialect, and code that builds, lowers or runs its programs, name its ops; tests in Rust and Lean keep it so

Status: accepted; refined by ADR-2026-11-03-1617
Tier: direction; area: semantics

## Decision

- **Generic code** sees every op alike and must not know the ops of any
  dialect. It reaches them only through the registry (`OpSpec`, `TypeSpec`)
  or the dialect's classes. It is: in Rust, all of `funk-ir`'s `src/` but
  `src/dialects/`, the module generator (`src/generate.rs`,
  `src/generate/`) and the unit tests; in Lean, all of `lean/Fir/` but
  `lean/Fir/Core/` and the text chapter's example, `Fir/Text/Example.lean`;
  all of `lean/FirRef/` but `fir-ref`'s command line (`Main`, `Report`,
  `Run`, `RunArgs`); and `lean/FirTest/G0.lean`. Two files of the text
  chapter, `Fir/Text/PrintParse.lean` and `Fir/Text/ParseWellFormed.lean`,
  end with core corollaries: they may name the core dialect, but not write
  its words. The grammar's own words, such as `func`, are not per-op code.
- **Code that may name ops** builds, lowers or runs one dialect's programs:
  the dialect's files, the module generator, the x86-64 backend, `funk`'s
  and `fir-ref`'s command lines, the tests and the corpus.
- **Every op declares its poison class and effects.** The core lists each op
  by its constructor in `Core.Op.poisonClass` and `Core.Op.effects`, with no
  case for the rest, so a new core op does not build until it declares them.
- **CI keeps the line.** `crates/funk-ir/tests/g0.rs` and
  `scripts/check_g0.py` fail on per-op code in generic code, and
  `lean/FirTest/G0.lean` breaks when a generic definition or theorem narrows
  to the core. Each check covers a place unless this line excludes it, so a
  new file is checked. A new dialect's directory joins `DIALECT_DIRS` in
  `check_g0.py`, and moving the line edits this ADR in place.

semantics.md states the rule; each check's module docs say what it reads.

## Why

G0 (ADR-2026-10-29-2016) keeps fir open to dialects that M0 does not have.
Some code must name ops, so the line must be explicit, and only a check in CI
stops a later change from reopening the door.

## Rejected alternatives

- **Review by hand.** Not durable.
- **One script for both languages.** The Rust test takes the core's words
  from its live registration; a script would need a copy.
- **Lean theorems alone.** A generic definition could test an op's name as a
  string and keep every theorem true.
- **Moving the two corollaries into `lean/Fir/Core/`.** It changes the spec's
  chapters for no gain.
