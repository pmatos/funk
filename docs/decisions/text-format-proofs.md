# Current decisions: how the text proofs are built

This page continues [text-format.md](text-format.md). It says how the Lean
proofs about fir's text are structured: the round trip,
`printThenParse`, and the proof that a parsed module is well formed,
`parse_wellFormed`. These are rules for one group of Lean modules under
`lean/Fir/Text/`, so they have no ADR. The page is the record (ADR-2026-11-09-1610).

The proofs may not change what the printer and the parser compute: both are
spec definitions.

## Printing then parsing

#11 proves `PrintThenParse` for the spec's parser `Fir.parse`, for every
dialect whose text is lawful, over every well-formed module
(ADR-2026-10-29-2014). `Fir.parse` has three steps: `lex`, `readModule` and
`decodeModule`. Each is total and computes a different kind of thing:
tokens, a syntax tree with the positions of the tokens, a module.

The proof has one step for each step of the parser, joined at exact forms.
Each step's result states what the next step reads, whatever the positions:

1. `lex_print`: `lex m.print` gives the tokens `Module.tokens m`, then `eof`
   ([`Tokens.lean`](../../lean/Fir/Text/Tokens.lean), [`LexModule.lean`](../../lean/Fir/Text/LexModule.lean)).
2. `readModule_tokens`: on any tokens of those kinds, `readModule` gives a
   tree that erases to `Module.tree m` ([`Tree.lean`](../../lean/Fir/Text/Tree.lean), [`ReadModule.lean`](../../lean/Fir/Text/ReadModule.lean)).
3. `Module.WellFormed.decodeModule_eq`: on any tree that erases to
   `Module.tree m`, `decodeModule` gives `m` ([`DecodeModule.lean`](../../lean/Fir/Text/DecodeModule.lean)).

`printThenParse`, in [`PrintParse.lean`](../../lean/Fir/Text/PrintParse.lean), joins the three. Each step states the
hypotheses it needs, and `Module.WellFormed` gives them all.

One predicate per step says what a reader does with a part. `Spells` is for
the lexer and `Reads` for the grammar. `Defines` and `Decodes` are for the two
passes of the decoder. Each says what the step gives on the text, the tokens
or the tree of one part, at any positions. `Spells` and `Reads` also say it
before what follows the part, when that starts at a boundary (`Spells`) or
with a token that `stop` allows (`Reads`).

The readers of blocks, ops and regions call one another to any depth, and so
do the two passes of the decoder; fir has no nesting limit
(ADR-2026-10-30-1549). The lemmas for blocks, ops and regions, such as
`readOps_cons_reads`, `defineOps_cons` and `decodeOps_cons`, are not
recursive. Each takes the predicate of every reader its reader calls as a
hypothesis, and proves its own reader's predicate. Short mutual theorems, one
per reader, such as `Block.readsList`, `Block.defines` and
`Block.decodesList`, tie the lemmas together by structural recursion on the
module's blocks, ops and regions.

The decoder's scope is matched by permutation. The first pass reads an op's
results, then the blocks of its regions, while `Func.defs` lists all of a
block's op results before the blocks of their regions. `Block.scopeDefs` lists
the blocks' definitions in the order that the first pass reads them.
`Func.scopeDefs_perm` proves the parameters followed by that list a
permutation of `Func.defs`. Since a well-formed function names each value
once, the scope gives each value the type that `Func.typeOf` gives it.

A new dialect gets the round trip by proving its own `LawfulDialectText`. A
change to the core op set extends `Core.lawfulDialectText`. Neither reworks
`printThenParse`. A new kind of item changes the token lists, the readers and
`decodeItem`, and so extends the item lemma of each step. The M1 design
restates the round-trip proofs over sums of dialects and registered kinds of
item (ADR-2026-11-09-1543). A change to the printer, the lexer, the readers or
the decoder that breaks the round trip breaks the proof of the step it
changes. Each reader has a lemma for no parts and one for a part followed by
more, so the proof has many short lemmas that look alike.

Rejected:

- one induction through the three steps at once, on the module. Its goals
  would mix the lexer's state, the readers' tokens and the decoder's scope, and
  a change to one step would break the proofs of the others;
- a decoder or a token order that matches `Func.defs`, so that no permutation
  is needed. It changes what the printer or the parser computes;
- first proving that decoding ignores positions, then decoding
  `Module.tree m` itself. It needs a mutual induction of its own, and the
  inversion lemmas of [`Tree.lean`](../../lean/Fir/Text/Tree.lean) already give each part of the tree at any
  positions.

## Parsed modules are well formed

#105 proves `parse_wellFormed`, in [`ParseWellFormed.lean`](../../lean/Fir/Text/ParseWellFormed.lean): every module that
`Fir.parse` gives is well formed, for every dialect whose text is lawful. The
proof follows the same three steps, joined at `TokensWritable` and
`SModule.Writable`.

It is given only a text, so it has no module or tree to recurse on while the
grammar reads tokens. The readers are defined by well-founded recursion on the
number of tokens (`termination_by ts => 2 * ts.length` and the like in
[`Read.lean`](../../lean/Fir/Text/Read.lean)), so there is no structural recursion on the tokens either. Lean
derives a functional induction principle for each group of mutual readers:
`readBlocks.induct`, `readItems.induct` and `readAttr.mutual_induct`.

A lemma about a group of mutual readers is proved by the group's functional
induction principle, with one motive per reader. Each case is one reader on
one shape of tokens. It unfolds only its own reader, and takes what the
readers it calls do on the tokens left to them as the case's hypotheses. No
case unfolds a reader that it calls. This is the round trip's rule, applied
through functional induction instead of structural recursion on the module.

A step of a reader or of the decoder is taken apart with `bind_step`, in
[`LexAccepted.lean`](../../lean/Fir/Text/LexAccepted.lean). It drops the hypothesis it consumes, so a goal does not
hold a step's program twice.

The two passes of decoding recurse on the tree. They keep the round trip's
shape: step lemmas that are not recursive, joined by short mutual theorems.

A change to a reader's recursion changes its induction principle, and the
build fails at the cases whose shape changed. The proofs of blocks and of
items have pages of their own ([`ReadAcceptedBlocks.lean`](../../lean/Fir/Text/ReadAcceptedBlocks.lean),
[`ReadAcceptedItems.lean`](../../lean/Fir/Text/ReadAcceptedItems.lean)), and so do the second pass and the decoding of
functions. Each induction names one motive per reader of its group, so its
call is long.

Rejected:

- strong induction on the number of tokens, unfolding each reader in place.
  Every case would hold the bodies of the readers it calls and the measure's
  arithmetic;
- induction on the tree that the readers give. Each case would first have to
  take the reader's run apart to find the tokens it read; the cases of the
  functional induction principle are those runs.

## Why the shape must be kept

A lemma that unfolds a recursive reader inside a mutual proof has goals that
hold the reader's whole body and the context of every theorem of the mutual
block, and so does every goal after it. Taking called readers' behaviour as
hypotheses keeps each goal to one reader's body. The proofs stay fast to check
and their pages small.

The spec renders each module of `lean/Fir/` with its proof states. In PR #57,
one page held the proofs for ops, blocks and regions and was 10.4 MB before
their lemmas took the nested readers' behaviour as hypotheses; the two pages
that hold them after were 3.5 MB and 2.3 MB. Pages that held the readers of
blocks with those of items, and the second pass of decoding with the decoding
of functions, were 8.2 MB and 6.6 MB; split, the pages of blocks and of items
were 3.4 MB and 4.9 MB.

No build check guards this. A later proof that unfolds the readers in place
still builds. It only makes the goals, the build and the pages larger. Later
changes keep this shape.
