# The fir test corpus keeps canonical modules, TOML sidecars of tests, non-canonical inputs and TOML files of must-reject texts apart

Status: accepted

## Context

[#13](https://github.com/pmatos/funk/issues/13) asks for a corpus format
that later tickets extend by adding files. Every test module is a canonical
`.fir` file, exactly what the printer writes, so the round trips use it as
it is; a comment would break `print(parse(t)) == t`. So test metadata
(arguments, expected results, fuel budget, the rule a must-reject text
breaks) lives outside the `.fir` text. Must-reject texts and non-canonical
inputs are kept apart from the canonical files. Some texts cannot be
committed as files: the `hidden-chars` hook, `end-of-file-fixer`,
`trailing-whitespace` and `*.fir text eol=lf` would reject or change them.

`tests/fir/canonical/` and `tests/fir/noncanonical/` exist, and three
readers take every `*.fir` file in them: `crates/funk-ir/tests/corpus.rs`,
the `fir_texts` example and `scripts/check-fir-ref.sh`
(ADR-2026-10-30-1250).

## Decision

- **Layout of `tests/fir/`**, which holds nothing else but `README.md`:
  - `canonical/NAME.fir`: a canonical, valid module. Every `.fir` file of
    the corpus outside `noncanonical/` is canonical.
  - `canonical/NAME.toml`: the tests of `NAME.fir`, if it has any.
  - `noncanonical/NAME.fir`: an input with comments or other layout, whose
    canonical form is `canonical/NAME.fir`.
  - `reject/*.toml`: must-reject texts, grouped by what they break.
- **A test** is one entry of `tests`, a list of TOML inline tables:
  - `func`: the function's symbol as text writes it, such as `@add3`, or
    `'@"a b"'` in a TOML literal string.
  - `args`: one string per parameter, each spelled as a constant of its
    type (ADR-2026-10-30-1856); none by default.
  - `fuel`: the budget of `fir-ref run`, 1,000,000 steps by default.
  - `expect`: absent for a differential test, which runs on `fir-ref` and
    as native code. Present for an interpreter-only test, which runs on
    `fir-ref` only: a list of values, each a value or `"poison"`, or
    `"ub"`, or `"fuel-exhausted"`.
- **A module with a differential test builds whole.** `funk build` builds a
  module all or nothing (ADR-2026-10-30-1326), so every function of such a
  module is one the backend lowers. A function that the backend does not
  lower, such as one at `i7` or with several results, goes in a module
  whose tests are all interpreter-only.
- **A must-reject text** is a `[[reject]]` table with `verdict`
  (`parse-error` or `validation-error`), `rule` (the one rule it breaks,
  in words) and `text`. When the ops that both tools have cannot break a
  rule alone, the text breaks a second rule too, and `rule` names both. The text is a TOML string: a multi-line literal
  string (`'''`) shows it as it is, and a basic string writes the
  characters that the hooks keep out of files as escapes, such as `\r`,
  `\u202e` or `\u0000`, and a text with no final line feed. A text that
  is not UTF-8 is a list of strings and bytes, such as
  `["name(\"a", 0xff, "b\")"]`: each string is written in UTF-8, and each
  number from 0 to 255 is one byte.
- **Only ops that both tools have.** A text uses only the ops that `funk`
  registers. Until #14 to #20 land, `fir-ref` decodes ops and flags that
  `funk` does not (ADR-2026-10-30-1250), and those texts would fail for
  that reason alone.

## Alternatives

- **JSON sidecars.** No comments, and a quoted symbol needs escaped
  quotes.
- **One `.fir` file per must-reject text, each with a sidecar.** More than
  a hundred pairs for the tracer subset, and a text that the hooks keep
  out of files would still need another form.
- **Metadata in comments of the `.fir` text.** The text would not be
  canonical.
- **The verdict as a directory name.** The rule still needs words
  somewhere.

## Consequences

- A later ticket adds tests by adding a sidecar, or lines to one, and
  must-reject texts by adding a `reject/` file of its own, so parallel
  tickets rarely edit the same file.
- The existing hooks keep each canonical file canonical and valid, in
  Rust and in Lean. The harness fails on a file the layout has no place
  for and on a sidecar key it does not know (ADR-2026-10-30-2049).
- [`tests/fir/README.md`](../../tests/fir/README.md) documents the format
  for authors.
