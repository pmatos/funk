# `fir-ref run` reads an argument with at most two steps of its lexer over positions

Status: accepted

## Context

`fir-ref run` reads each argument, and each choice of `--choices`, as one
token of fir's text, an integer or a word, then the end of the text, and
decodes it as a `const` (ADR-2026-10-30-1856). `FirRef.constOf` matched the
spec's `Text.lex` of the whole argument against that shape. The spec's
lexer builds the list of the text's characters and measures a comment with
`utf8Len`, which takes a C frame per character. So with
`LEAN_STACK_SIZE_KB=256`, an argument that is a comment of 100,000
characters aborted (`Stack overflow detected`) instead of being rejected
with exit 2 ([#135](https://github.com/pmatos/funk/issues/135)). A Linux
argument is at most 128 KiB.

Since ADR-2026-11-03-1810, `fir-ref` parses a file with its own lexer over
`String` positions, `nextTokP`, which scans a comment with no stack per
character. `constOf` was the last call of the spec's lexer in `fir-ref`.

## Decision

- **`FirRef.argAttr` is the reading by the spec's lexer:** `Text.lex s`
  matched against an integer or a word, then `eof`. `constOf` calls it, then
  checks the spelling and decodes the `const` as before.
- **`FirRef.argAttrP` reads the same over positions.** `nextTokP` reads the
  first token from the start of the text; after an integer or a word, one
  more step must give `eof` and end the text. It lexes at most two tokens,
  builds no list of characters and takes no stack per character.
- **`@[csimp] theorem argAttr_eq_argAttrP : @argAttr = @argAttrP`**, in
  `FirRef.Lex.Arg`, holds for every text. Its proof turns the spec's lexer
  into steps of `nextTokP` with `lex_eq_lexRest` and `lexRest_some`; the
  first three steps decide the match. `FirRef.Fast` imports the module, so
  `constOf`, compiled after it, runs `argAttrP` (ADR-2026-10-30-1450). The
  function replaced is `fir-ref`'s own reading by the spec's lexer, not a
  spec function; the spec does not change.

## Alternatives

- **`@[csimp]` on `Text.lex` itself, as `lexRest` from the start.** `lexRest`
  takes stack per token, and it lexes the whole argument where two tokens
  decide.
- **`constOf` written over positions, with a plain theorem about it.** The
  same code runs, but `constOf` would no longer show the reading by the
  spec's lexer that ADR-2026-10-30-1856 names.

## Consequences

- In the C that Lean emits, no function of the spec's lexer (`Text.lex`,
  `lexFrom`, `lexToken`, `utf8Len`) is reachable from `fir-ref`'s `main`.
- Arguments and choices give the results and messages they gave before,
  byte for byte, by the theorem.
- An argument that is a long comment, alone or after a value, gets exit 2
  on a 256 KiB stack; `scripts/check-fir-ref-run.sh` checks it.
- A change to the spec's lexer breaks the proof, and so the build, until
  `argAttrP` follows it.
