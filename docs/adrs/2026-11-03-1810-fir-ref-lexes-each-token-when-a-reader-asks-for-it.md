# `fir-ref` lexes each token when a reader asks for it, and lexes the whole text again only when the readers fail

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
  `fir-ref` keeps neither a `List Char` nor a `List Token`, and builds no
  list of a comment's characters: `commentP` scans a comment's body for
  the spec's `firstDisallowed` and `utf8Len` over positions.
- **One pass when the readers accept.** The readers run on a `LexCursor`:
  a position in the text and the line and column there, whose `uncons`
  lexes the next token. At a lexer error the cursor ends, so the readers
  fail there. Only when the readers fail does `FirRef.lexCheck` run the
  lexer over the whole text, keeping no token; its error, if any, is the
  parse error, and otherwise the readers' error is. So a lexer error is
  still reported before any reader error.
- **Why one pass gives the spec's answer.** The readers accept only after
  they take `eof` (`readModule_ok_eof`), and the lexer reads `eof` only at
  the end of a text that it reads without an error (`nextTokP_ne_eof`,
  `lexRest_of_eof_mem`). `readModule_ok_eof` comes from `readModuleC_eq`
  on a cursor that reads a list by index, so it needs no new fact about
  the spec's readers.
- **The lexer over positions is proved step by step.** `chars p`, the
  characters from position `p` on, exists only in proofs. `nextTokP`
  skips whitespace and comments and reads one token, and `lexFrom_eq`
  proves that the spec's `lexFrom` is `nextTokP` then `lexFrom` again.
- **The readers are written once, over a `Cursor` class**: `uncons`, and
  `view`, the tokens left as a list, for proofs. Each reader is proved to
  give what the spec's reader gives on `view`, errors included. Blocks,
  ops and regions are one loop with a stack of frames; items another;
  attributes another; lists take an accumulator. Every call to itself is a
  tail call. Where a reader looks at a token and then reads from it, an
  op's attributes, a type and an op's location reference, it reads from
  the token it already took (`attrFrom`, `attrApp`, `opLocOf`).
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
- **Two passes: `lexCheck` over the whole text first, then the readers.**
  The first version of this decision, in
  [PR #133](https://github.com/pmatos/funk/pull/133). It lexes every
  accepted text once more: on the block of 1,000,000 ops, `fmt --check`
  took 6.4 s of CPU against 4.3 s now, and `lexCheck` alone about 1 s. It
  kept the peak RSS of a lexer error at the end to the two copies of the
  text.
- **A cursor that keeps the token it lexed** (in a `Thunk`), so that no
  token is lexed twice. The review of PR #133 measured it faster on long
  tokens and regions but no faster on a block of ops. Reading from the
  token already taken, where a reader looks at a token and then reads from
  it, gets the gain on long tokens.

## Consequences

- `fir-ref` holds the file's bytes and the `String` made from them, one
  byte per input byte each, then the read tree and the module; `fmt
  --check` adds the printed text and its bytes. A file that is not UTF-8
  is located with a loop over its bytes, without a list of them.
- Peak RSS on a block of 1,000,000 ops (34 MB) fell from 980 MB to 78 MB
  on a lexer error at byte 1 or a reader error at the first token, from
  980 MB to 506 MB for `fmt --check`, and from 874 MB to 43 MB when its
  last byte is not UTF-8. On `ret %a, %a, …` with 5,000,000 operands
  (20 MB): from 585 or 984 MB to 50 MB on those errors, and from 1,517 MB
  to 698 MB for `fmt --check`.
- On a lexer error near the end of a large text, the readers first build
  the tree of what comes before it: 475 MB on the block of ops with a bad
  character at its end (980 MB before), not the 78 MB of the two copies of
  the text.
- The readers lex each token of a block of ops about 1.6 times, 11 lexes
  for the 7 tokens of `%c0: i32 = const 0 @0`, since a reader that looks
  at a token and does not take it leaves it to be lexed again; a rejected
  text is lexed once more by `lexCheck`. In CPU time (median of five, the
  spec's lexer and readers first): `fmt --check` of the block of ops,
  4.5 s and 4.3 s; its `validate`, 7.5 s and 7.3 s; regions nested 3,000
  deep, 0.9 s and 0.5 s; the widest constants of
  [#41](https://github.com/pmatos/funk/issues/41), 4.9 s and 3.7 s.
- A change to the spec's lexer or readers breaks these proofs, and so the
  build, until the implementations follow it.
