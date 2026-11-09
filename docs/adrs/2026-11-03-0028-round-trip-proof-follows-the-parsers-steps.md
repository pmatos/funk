# The round-trip proof follows the parser's three steps

Status: accepted
Tier: implementation; area: text-format

## Context

[#11](https://github.com/pmatos/funk/issues/11) proves `PrintThenParse`
for the spec's parser `Fir.parse`, for every dialect whose text is lawful,
over every well-formed module (ADR-2026-10-30-0815). The printer and the
parser are spec definitions, and the proof may not change what they
compute.

Facts:

- `Fir.parse` has three steps: `lex`, then `readModule`, then
  `decodeModule`. Each one is total and computes a different kind of
  thing: tokens, a syntax tree with the positions of the tokens, a module.
- The readers of blocks, ops and regions call one another, to any depth,
  and so do the two passes of the decoder. fir has no nesting limit
  (ADR-2026-10-30-1549).
- The spec document renders each module of `lean/Fir/` with its proofs,
  and a page holds the proof states that a reader can open. A proof whose
  goals hold a whole reader's body, or the context of a large mutual
  proof, makes a large page. In PR
  [#57](https://github.com/pmatos/funk/pull/57), one page held the proofs
  for ops, blocks and regions and was 10.4 MB before their lemmas took the
  nested readers' behaviour as hypotheses; the two pages that hold them
  now are 3.5 MB and 2.3 MB.
- The first pass of the decoder reads an op's results, then the blocks of
  its regions. `Func.defs` lists all of a block's op results before the
  blocks of their regions.

## Decision

- **One step of the proof for each step of the parser, joined at exact
  forms.** Each step's result states what the next step reads, whatever
  the positions:
  1. `lex_print`: `lex m.print` gives the tokens `Module.tokens m`, then
     `eof` ([Tokens.lean](../../lean/Fir/Text/Tokens.lean),
     [LexModule.lean](../../lean/Fir/Text/LexModule.lean)).
  2. `readModule_tokens`: on any tokens of those kinds, `readModule` gives a
     tree that erases to `Module.tree m`
     ([Tree.lean](../../lean/Fir/Text/Tree.lean),
     [ReadModule.lean](../../lean/Fir/Text/ReadModule.lean)).
  3. `Module.WellFormed.decodeModule_eq`: on any tree that erases to
     `Module.tree m`, `decodeModule` gives `m`
     ([DecodeModule.lean](../../lean/Fir/Text/DecodeModule.lean)).

  `printThenParse` ([PrintParse.lean](../../lean/Fir/Text/PrintParse.lean))
  joins the three. Each step states the hypotheses it needs, and
  `Module.WellFormed` gives them all.
- **One predicate per step says what a reader does with a part.** `Spells`
  for the lexer, `Reads` for the grammar, `Defines` and `Decodes` for the
  two passes of the decoder. Each says what the step gives on the text,
  the tokens or the tree of one part, at any positions, and, for `Spells`
  and `Reads`, before what follows the part, when that starts at a
  boundary (`Spells`) or with a token that `stop` allows (`Reads`).
- **The lemmas for blocks, ops and regions take what the nested readers do
  as hypotheses.** Each such lemma, such as `readOps_cons_reads`,
  `defineOps_cons` or `decodeOps_cons`, is not recursive: it takes the
  predicate of each reader that its reader calls as a hypothesis, and
  proves the predicate of its own reader from them. Short mutual theorems,
  one per reader, such as `Block.readsList`, `Block.defines` and
  `Block.decodesList`, then tie the lemmas together by structural
  recursion on the module's blocks, ops and regions.
- **The decoder's scope is matched by permutation.** `Block.scopeDefs`
  lists the blocks' definitions in the order that the first pass reads
  them, `Func.scopeDefs_perm` proves the parameters followed by that list a
  permutation of `Func.defs`, and, since a well-formed function names each
  value once, the scope gives each value the type that `Func.typeOf` gives
  it.

## Why the hypotheses

A lemma that unfolds a recursive reader inside a mutual proof has goals
that hold the reader's whole body and the context of every theorem of the
mutual block. Taking the nested readers' behaviour as hypotheses keeps each
goal to one reader's body, so the proofs stay fast to check and their pages
small. No build check guards this. A later proof that unfolds the recursion
in place still builds; it only makes the goals, the build and the pages
larger. This ADR records the choice so that a later change keeps it.

## Alternatives

- **One induction through the three steps at once**, on the module. Its
  goals would mix the lexer's state, the readers' tokens and the decoder's
  scope, and a change to one step would break the proof of the others.
- **A decoder or a token order that matches `Func.defs`**, so that no
  permutation is needed. That changes what the printer or the parser
  computes, which the proof may not do.
- **First proving that decoding ignores positions**, then decoding
  `Module.tree m` itself. It needs a mutual induction of its own, and the
  inversion lemmas of `Tree.lean` already give each part of the tree, at
  any positions.

## Consequences

- A new dialect gets the round trip by proving its own `LawfulDialectText`,
  and a change to the core op set extends `Core.lawfulDialectText`;
  neither reworks `printThenParse`. A new kind of item changes the token
  lists, the readers and `decodeItem`, and so extends the item lemma of
  each step.
- A change to the printer, the lexer, the readers or the decoder that
  breaks the round trip breaks the proof of the step it changes.
- Each reader has a lemma for no parts and one for a part followed by
  more, so the proof has many short lemmas that look alike.
