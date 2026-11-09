# The parsed-module proof proves the readers by their functional induction

Status: accepted
Tier: implementation; area: text-format

## Context

[#105](https://github.com/pmatos/funk/issues/105) proves
`parse_wellFormed`: every module that `Fir.parse` gives is well formed,
for every dialect whose text is lawful
([ParseWellFormed.lean](../../lean/Fir/Text/ParseWellFormed.lean)). As
for the round trip (ADR-2026-11-03-0028), the proof follows the parser's
three steps, joined at `TokensWritable` and `SModule.Writable`.

Facts:

- The round trip recurses on the module it is given. This direction is
  given only a text, so there is no module or tree to recurse on while the
  grammar reads tokens.
- The readers are defined by well-founded recursion on the number of
  tokens (`termination_by ts => 2 * ts.length` and the like in
  [Read.lean](../../lean/Fir/Text/Read.lean)), so there is no structural
  recursion on the tokens either.
- The readers of blocks, ops and regions call one another, to any depth,
  and so do the readers of items and those of attributes. Lean derives a
  functional induction principle for each group from its own recursion:
  `readBlocks.induct`, `readItems.induct` and `readAttr.mutual_induct`.
- The spec renders each module with its proof states. Pages that held the
  readers of blocks with those of items, and the second pass of decoding
  with the decoding of functions, were 8.2 MB and 6.6 MB.

## Decision

- **A lemma about a group of mutual readers is proved by the group's
  functional induction principle**, with one motive per reader. Each case
  is one reader on one shape of tokens. It unfolds only its own reader,
  and takes what the readers it calls do on the tokens left to them as the
  case's hypotheses. No case unfolds a reader that it calls. This is
  ADR-2026-11-03-0028's rule for the round trip's lemmas, applied through
  functional induction instead of structural recursion on the module.
- **A step of a reader or of the decoder is taken apart with `bind_step`**
  ([LexAccepted.lean](../../lean/Fir/Text/LexAccepted.lean)), which drops
  the hypothesis it consumes, so that a goal does not hold a step's program
  twice.
- **The two passes of decoding**, which recurse on the tree, keep
  ADR-2026-11-03-0028's shape: step lemmas that are not recursive, joined
  by short mutual theorems.

## Why

A case that unfolds a reader it calls holds that reader's body in its
goals, and so does every goal after it. Taking the called readers'
behaviour as hypotheses keeps each goal to one reader's body, so the
proofs stay fast to check and their pages small. No build check guards
this. A later proof that unfolds the readers in place still builds; it only
makes the goals, the build and the pages larger. This ADR records the
choice so that a later change keeps it.

## Alternatives

- **Strong induction on the number of tokens**, unfolding each reader in
  place. Every case would hold the bodies of the readers it calls and the
  measure's arithmetic.
- **Induction on the tree that the readers give.** Each case would first
  have to take the reader's run apart to find the tokens it read; the
  cases of the functional induction principle are those runs.

## Consequences

- A change to a reader's recursion changes its induction principle, and
  the build fails at the cases whose shape changed.
- The proofs of blocks and of items have pages of their own
  ([ReadAcceptedBlocks.lean](../../lean/Fir/Text/ReadAcceptedBlocks.lean),
  [ReadAcceptedItems.lean](../../lean/Fir/Text/ReadAcceptedItems.lean)),
  of 3.4 MB and 4.9 MB, and so do the second pass and the decoding of
  functions.
- Each induction names one motive per reader of its group, so its call is
  long.
