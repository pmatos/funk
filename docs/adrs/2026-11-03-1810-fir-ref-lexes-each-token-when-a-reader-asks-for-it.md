# `fir-ref` lexes each token once, when its readers reach it, and lexes the whole text again only when they fail

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
The first version of this decision parsed a block of 1,000,000 ops in
about twice the CPU time of the spec's lexer and readers. The human held
it for a faster one, keeping the spec's order of errors. This version is
faster than the spec's lexer and readers on accepted texts, but slower on
a text with a late lexer error, a cost the human accepted on 2026-11-05.

## Decision

- **Tokens are lexed from `String` positions as the readers reach them.**
  `fir-ref` keeps neither a `List Char` nor a `List Token`, and builds no
  list of a comment's characters: `commentP` scans a comment's body for
  the spec's `firstDisallowed` and `utf8Len` over positions.
- **The cursor holds its next token, so each token is lexed once.** A
  `LexCursor` holds the next token, already lexed, and the lexer's state
  after it. `uncons` gives that token and lexes the one after it; it is
  inlined into the readers, and the compiler lexes the token after only in
  the branches that take the token. Where a reader would take a token in
  some branches and leave it in others, it first looks without taking
  (`startsOpC` before `opHeadC` for an op, `atLocs` for the location
  table), or it reads on from the cursor it already has
  (`succsAfterComma`, `attrFrom`, `attrApp`, `opLocOf`).
- **One pass when the readers accept.** The readers run on a `LexCursor`
  from the start of the text. At a lexer error the cursor ends, so the
  readers fail there. Only when the readers fail does `FirRef.lexCheck`
  run the lexer over the whole text, keeping no token; its error, if any,
  is the parse error, and otherwise the readers' error is. So a lexer
  error is still reported before any reader error.
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
- **Two passes: `lexCheck` over the whole text first, then the readers.**
  The first version, in [PR #133](https://github.com/pmatos/funk/pull/133).
  It lexes every accepted text once more.
- **A cursor that lexes its next token at each `uncons`.** Readers look at
  a token and leave it, at the end of a list or of a block, and the next
  reader lexes it again: 1.6 lexes per token on a block of ops, 2 on a
  function of blocks, which parsed slower than the spec's lexer and
  readers.
- **A cursor that keeps each token in a `Thunk`**, lexed the first time a
  reader asks. No token is lexed twice, but a node, a `Thunk` and a
  closure per token cost more than they save: `fmt --check` of the block
  of 1,000,000 ops took 7.2 s of CPU, against 5.6 s with the spec's lexer
  and readers, in the same batch.
- **Keep the lexer's error in the cursor and, on a reader error, lex only
  from where the readers stopped.** Every token before that point was
  lexed without an error, so only the rest needs `lexCheck`. On the block
  of 1,000,000 ops this would save about 1 s, the cost of `lexCheck`, on a
  text rejected at its end. It was not taken: `lookP` turns a lexer
  error into the end of the cursor, so the cursor does not keep the error;
  the readers would have to return their cursor with their error, which
  changes the type of every reader and every proof about them; and
  `readText_eq` would need the lexer's run split at a state.

## Consequences

- Every token of the 277 texts of `tests/fir/` is lexed once: 111,775
  tokens, 111,775 calls of `nextTokP`.
- CPU time (user and system, median of three) of `main`'s `fir-ref`, then
  this one: `fmt --check` of the block of 1,000,000 ops, 4.62 s and
  4.10 s, its `validate` 8.73 s and 7.82 s; a function of 1,000,000 blocks,
  2.03 s and 1.50 s, and 11.35 s and 10.47 s; the 277 texts of
  `tests/fir/`, one process each, 0.83 s and 0.82 s, and 0.84 s and 0.81 s.
- Peak RSS: 980 MB to 505 MB for `fmt --check` of the block of ops, and to
  78 MB when it has a lexer error at byte 1 or a reader error at the first
  token; a block whose last byte is not UTF-8, 874 MB to 44 MB.
  `fir-ref` holds the file's bytes and the `String` made from them, one
  byte per input byte each, then the read tree and the module; `fmt
  --check` adds the printed text and its bytes. A file that is not UTF-8
  is located with a loop over its bytes, without a list of them.
- A text rejected late can be slower than on `main`: the readers read it
  up to the error, then `lexCheck` lexes it again from the start. On the
  block of 1,000,000 ops (`fmt --check`, median of five to seven runs, in
  two batches), a lexer error at byte 1 takes 0.36 s on `main` and 0.05 s
  here; in the middle, 0.97 s and 1.12 to 1.46 s; at the end, 1.27 to
  1.59 s and 2.85 s. So a lexer error past about the first fifth of a
  text costs more than on `main`. A reader error at the first token takes
  2.21 s and 1.09 s; in the middle, 2.19 to 2.24 s and 1.90 s; at the end,
  2.35 to 2.38 s and 2.23 to 2.51 s, about the same. The human accepted
  this cost on 2026-11-05: "Performance is not a deal breaker for the lean
  side of things." Lexing only from where the readers stopped stays an
  alternative not taken, and nothing is filed for it.
- A change to the spec's lexer or readers breaks these proofs, and so the
  build, until the implementations follow it. A reader that takes a token
  in some branches and leaves it in others, written plainly, lexes the
  next token there twice: nothing fails, but it costs time.
