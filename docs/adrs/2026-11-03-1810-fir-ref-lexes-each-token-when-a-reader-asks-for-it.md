# `fir-ref` lexes each token when a reader asks for it, after a pass that finds the lexer's error

Status: accepted

## Context

[#47](https://github.com/pmatos/funk/issues/47) asks `fir-ref` to read a
text nested to any depth with no stack per level, and to fit large texts
in memory. The spec's `Fir.parse` turns the text into a `List Char` (about
29 bytes per input byte), lexes it into a `List Token` (up to about 47),
reads the tokens into a tree, and decodes the tree. A lexer error anywhere
in the text is reported before any error of the readers, since lexing
ends before reading starts.

`fir-ref` runs implementations proved equal to the spec's functions
(ADR-2026-10-30-1450). For the readers, #47 names two designs: tokens
pulled from a lexer over the text's `String` positions, so that no list of
tokens exists; or tokens stored compactly, in an `Array` read by index.

## Decision

- **Tokens are lexed from `String` positions when a reader asks for them.**
  `fir-ref` keeps neither a `List Char` nor a `List Token`.
- **Two passes over the text.** `FirRef.lexCheck` first runs the lexer
  from the start to `eof` and keeps no token; its error, if any, is the
  parse error. Only then do the readers run, on a `LexCursor`: a position
  in the text and the line and column there, whose `uncons` lexes the next
  token. So a lexer error is still reported before any reader error.
- **The lexer over positions is proved step by step.** `chars p`, the
  characters from position `p` on, exists only in proofs. `nextTokP`
  skips whitespace and comments and reads one token, and `lexFrom_eq`
  proves that the spec's `lexFrom` is `nextTokP` then `lexFrom` again.
- **The readers are written once, over a `Cursor` class**: `uncons`, and
  `view`, the tokens left as a list, for proofs. Each reader is proved to
  give what the spec's reader gives on `view`, errors included. Blocks,
  ops and regions are one loop with a stack of frames; items another;
  attributes another; lists take an accumulator. Every call to itself is a
  tail call.
- **Two instances.** On a `List Token`, they give `FirRef.readModule`, with
  `@[csimp] theorem readModule_eq_readModule : @Text.readModule =
  @FirRef.readModule`. On a `LexCursor`, they give `FirRef.readText`, and
  `readText_eq` proves it equal to `Text.lex` then `Text.readModule`.
  `FirRef.parse` is `readText` then `Text.decodeModule`, and
  `parse_eq_parse` is proved from `readText_eq`, no longer by `rfl`.

## Alternatives

- **An `Array` of tokens read by index.** It still holds one record per
  token, with its own `String` for names and its position: 7,000,023
  tokens for a block of 1,000,000 ops. It also needs a proof that the
  array holds `lex`'s list.
- **One pass: read while lexing, and on a reader error lex the rest for a
  lexer error.** It saves a pass on accepted texts. Its proof needs a fact
  the spec does not state: that the readers never accept the tokens before
  a lexer error, which lack `eof`. The second pass costs about 1.3 s of
  CPU on a block of 1,000,000 ops.

## Consequences

- `fir-ref` holds the file's bytes and the `String` made from them, one
  byte per input byte each, then the read tree and the module; `fmt
  --check` adds the printed text and its bytes. Peak RSS on a block of
  1,000,000 ops (34 MB) fell from 980 MB to 78 MB on a lexer error at byte
  1, from 980 MB to 77 MB on a reader error at the first token, and from
  980 MB to 505 MB for `fmt --check`. On `ret %a, %a, …` with 5,000,000
  operands (20 MB): from 585 to 50, 984 to 49 and 1,518 to 683 MB.
- Each token is lexed twice, and the lexer reads one character at a time
  through `String.Pos`. Parsing takes more CPU than the spec's lexer and
  readers did where those had the stack to finish.
- A change to the spec's lexer or readers breaks these proofs, and so the
  build, until the implementations follow it.
