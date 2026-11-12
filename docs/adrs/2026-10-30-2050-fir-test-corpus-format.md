# The fir test corpus keeps canonical modules, TOML sidecars of tests, non-canonical inputs and TOML files of must-reject texts apart

Status: accepted
Tier: direction; area: testing-and-harness

## Decision

- **`tests/fir/` holds only** `canonical/NAME.fir` (a canonical, valid module),
  `canonical/NAME.toml` (its tests), `noncanonical/NAME.fir` (an input whose
  canonical form is `canonical/NAME.fir`), `reject/*.toml` (must-reject texts),
  `llvm/` (the cases ported from LLVM, ADR-2026-11-03-0643) and `README.md`.
- **A test** is one inline table of a sidecar's `tests` list, with `func`,
  `args`, `fuel` (1,000,000 steps by default) and `expect`. A test without
  `expect` is differential and runs on `fir-ref` and as native code; one with
  it is interpreter-only. `results` and `choices` are ADR-2026-10-30-2135's.
- **A module with a differential test builds whole**, since `funk build` is all
  or nothing. A function the backend does not lower goes in a module whose
  tests are all interpreter-only.
- **A must-reject text** is a `[[reject]]` table with `verdict`
  (`parse-error` or `validation-error`), `rule` (in words) and `text`, a TOML
  string or a list of strings and bytes for a text that is not UTF-8.
- **A corpus text uses only the ops that both tools have.** The harness fails
  on a file the layout has no place for and on a sidecar key it does not know.
- A new test is a new line or file, with no code change.

## Why

Every reader of the corpus (the Rust round trip, `fir-ref`'s checks and the
differential harness) uses each module as it is, so it must stay canonical: a
comment would break `print(parse(t)) == t`. So test metadata lives outside the
`.fir` text. Some must-reject texts hold characters that the hooks keep out of
files, so they are TOML strings. Adding tests by adding files keeps parallel
tickets off each other's files.

## Rejected alternatives

- **JSON sidecars.** No comments, and a quoted symbol needs escaped quotes.
- **One `.fir` file per must-reject text.** Hundreds of pairs, and a text the
  hooks keep out of files would still need another form.
- **Metadata in comments of the `.fir` text.** The text would not be canonical.
- **The verdict as a directory name.** The rule still needs words somewhere.
