# Current decisions: text format and parsing

This page says what holds today for fir's text format and its parsers. It
only summarizes the ADRs it cites (ADR-2026-11-09-1610). When this page and
an ADR disagree, the page has a bug.

## One canonical text

fir has one canonical text form. It has no sugar and no alternative
spellings. The grammar has exactly one spelling for every construct
(ADR-2026-10-29-2014).

The printer is the formatter. `funk fmt` prints a module in canonical form.

Value names, attributes and locations are stored in the IR and printed as
stored. Nothing is renumbered. A module keeps the names its producer gave
it. So diffs stay small, and diagnostics name values as the author wrote them
(ADR-2026-10-29-2014).

The text format is the interface between Lean and Rust. Rust prints a module.
Lean parses and reprints it. The bytes must match (ADR-2026-10-29-2014).

Every op of every dialect uses one grammar, so a new dialect needs no parser
change (ADR-2026-10-29-2014). In M0, a new kind of item is a new `Item`
constructor and a parser change (ADR-2026-11-03-0600). The M1 design registers
kinds of item through the one grammar, so a new kind needs no parser change
(ADR-2026-11-09-1543).

## The dialect set

A module's text may start with its dialect set: the word `dialects`, the
names of the dialects other than the core whose words it writes, separated
by `, `, then an empty line, as in `dialects toy, gpu`. A module that names
no dialect has no such line, so every M0 text is unchanged. The word
`dialects` is no item's kind. The names keep the order the text gives them
(ADR-2026-11-10-1306).

A valid module names each dialect once, by a word. Each name must be a
dialect that the reader holds, other than the core, and every word of the
module must name the core or a dialect of its set: op names, attribute
words and type words, at any depth. Both validators check this beside
`Module.Valid`, as `Module.InDialectSet` (ADR-2026-11-10-1306).

## Region kinds

A region names its kind. A region of an op writes its kind as a word right
after its `{`, as in `toy.run { toy.graph`. The core's kind, a control-flow
graph, writes nothing there, so every M0 text is unchanged. A function's
body is always of the core's kind and its text names none: a word after an
item's `{` starts its items. Validation rejects a function whose body names
a kind (ADR-2026-11-10-1530). An op may own regions only of the kinds its
op instance states, and a kind's word joins the module's dialect set
(ADR-2026-11-10-1941).

## One format

Text is fir's only format in v0. A binary format is left out on purpose. It
can come later if text parsing becomes a bottleneck (ADR-2026-10-29-2014).

Text has no nesting limit. Every text the grammar accepts is read at any
depth (ADR-2026-10-30-1549).

Numbers have limits. An integer type `iN` has `1 <= N <= 16,777,215`. A
location reference, a line and a column are below `2^32`. An integer
attribute has no bound of its own: the dialect that reads it bounds it
(ADR-2026-11-03-1000).

`funk fmt` parses a file but does not validate it. Every module that parses
has a canonical form (ADR-2026-10-30-1032).

## The round trip

`parse(print(m)) == m` holds for every well-formed module.
`print(parse(t)) == t` holds for every text printed from one
(ADR-2026-10-30-0815).

A well-formed module is one whose printed form says everything it holds. The
spec defines it as `Module.WellFormed` in `lean/Fir/Text/RoundTrip.lean`.

The limit exists because text writes types only where values are defined. A
parser finds an op's operand types at the definitions of its operands. So an
op whose operand is undefined or has the wrong type has no text that reads
back to it. fir does not write a full signature on every op. That would write
every type twice and make op lines long (ADR-2026-10-30-0815).

Every valid module is well formed. Validation checks the characters of value
names and labels and the limits on numbers. Symbols that are not words are
quoted. So two different valid modules never print the same text. The spec
proves this as `validIsWellFormed`, for every dialect whose text meets the
laws of `LawfulDialectText`. #11 proves those laws for the core dialect
(ADR-2026-10-30-0815).

Round trips are tested within Rust and across Rust and Lean, including under
fuzzing (ADR-2026-10-29-2014). Lean proves that parsing a printed well-formed
module gives it back (ADR-2026-11-03-0028).

Every module that `Fir.parse` gives is well formed, for every dialect whose
text is lawful (ADR-2026-11-03-0328).

## Parse errors and validation errors

A text that follows the grammar but does not decode is not a module. The
parser rejects it with a reason and a position (ADR-2026-10-30-0815). These
texts are rejected:

- a number out of range, located at the number (ADR-2026-11-03-1000);
- a string or symbol not in its one spelling;
- an item of an unknown kind;
- a type that does not decode;
- a value defined twice;
- an operand that is not defined;
- an op whose name, attributes and types do not decode, such as a type
  mismatch.

Every other error, such as an undefined successor argument, is a validation
error on a module that parsed (ADR-2026-10-30-0815).

A type mismatch or an undefined operand in text is a parse error. Its tests
are parser tests, not verifier tests (ADR-2026-10-30-0815). An op that a
builder or a pass made ill-typed is a validation error (ADR-2026-10-30-1146).

Lean's and Rust's parsers must reject the same texts. Tests compare only
whether a text is rejected, not the wording of the reason
(ADR-2026-10-30-0815).

## Locations

Every op has a location field. The field always exists, and `unknown` is a
valid value (ADR-2026-10-29-2013).

An op cannot be built without a location. The `funk-ir` builder requires one,
and the verifier checks that every op has one. Every pass must give each op
it creates a location (ADR-2026-10-29-2013).

A location is `unknown` or one of these kinds: a source range, a name,
`callsite(callee at caller)`, `fused(a, b)` or `derived(op)`. The spec gives
the exact spelling of each kind (ADR-2026-10-29-2013).

Locations are erased before semantics. They never change what a program
means. The interpreter ignores them. Both parsers and printers keep them, and
round trips preserve them (ADR-2026-10-29-2013).

In text, each op carries a short `@N` reference. A `locs { ... }` table ends
the module and gives the location that each `@N` stands for. So op lines stay
short (ADR-2026-10-29-2013).

## Source ranges

A source range is written as MLIR writes it: `"f":2:3 to 2:14`
(ADR-2026-11-05-1131). The file is a string. Then come the line and column of
the start, the word `to`, and the line and column of the end.

The end is exclusive. It is the position just after the range's last byte. A
range whose end equals its start is empty, so an empty range can be written
(ADR-2026-11-05-1131).

Columns count UTF-8 bytes, from 1. Column 0 means that the column is unknown.
So a column does not depend on how a tool counts characters. Lines count from
1 (ADR-2026-11-05-1131).

The separator is the word `to`, not `-`. So the lexer reads a range without
depending on context (ADR-2026-11-05-1131).

The spec states this form in `lean/Fir/Syntax/Location.lean` and
`lean/Fir/Text/Grammar.lean`.

## How the text proofs are built

The proofs may not change what the printer and the parser compute
(ADR-2026-11-03-0028).

### Printing then parsing

The proof follows the three steps of `Fir.parse`: `lex`, `readModule` and
`decodeModule` (ADR-2026-11-03-0028). Each step's result states what the next
step reads, whatever the positions.

1. `lex_print`: `lex m.print` gives the tokens `Module.tokens m`, then `eof`.
2. `readModule_tokens`: on any tokens of those kinds, `readModule` gives a
   tree that erases to `Module.tree m`.
3. `Module.WellFormed.decodeModule_eq`: on any tree that erases to
   `Module.tree m`, `decodeModule` gives `m`.

`printThenParse` joins the three. Each step states the hypotheses it needs,
and `Module.WellFormed` gives them all.

One predicate per step says what a reader does with a part. `Spells` is for
the lexer and `Reads` for the grammar. `Defines` and `Decodes` are for the two
passes of the decoder (ADR-2026-11-03-0028).

The lemmas for blocks, ops and regions are not recursive. Each takes the
predicate of every reader it calls as a hypothesis, and proves its own
reader's predicate. Short mutual theorems, one per reader, tie the lemmas
together. They recurse structurally on the module's blocks, ops and regions
(ADR-2026-11-03-0028).

The decoder's scope is matched by permutation. `Block.scopeDefs` lists the
blocks' definitions in the order that the first pass reads them.
`Func.scopeDefs_perm` proves the parameters followed by that list a
permutation of `Func.defs` (ADR-2026-11-03-0028).

A new dialect gets the round trip by proving its own `LawfulDialectText`. A
change to the core op set extends `Core.lawfulDialectText`. Neither reworks
`printThenParse`. Today a new kind of item extends the item lemma of each step
(ADR-2026-11-03-0028). The M1 design restates the round-trip proofs over sums
of dialects and registered kinds of item (ADR-2026-11-09-1543).

### Parsed modules are well formed

The proof of `parse_wellFormed` follows the same three steps, joined at
`TokensWritable` and `SModule.Writable` (ADR-2026-11-03-0328). It is given
only a text. So it has no module or tree to recurse on while the grammar
reads tokens.

A lemma about a group of mutual readers uses the group's functional induction
principle, with one motive per reader. Each case unfolds only its own reader.
It takes what the readers it calls do as hypotheses. No case unfolds a reader
that it calls (ADR-2026-11-03-0328).

A step of a reader or of the decoder is taken apart with `bind_step`. It
drops the hypothesis it consumes, so a goal does not hold a step's program
twice (ADR-2026-11-03-0328).

The two passes of decoding recurse on the tree. They keep the shape of the
round trip: step lemmas that are not recursive, joined by short mutual
theorems (ADR-2026-11-03-0328).

### Why the shape must be kept

Taking called readers' behaviour as hypotheses keeps each goal to one reader's
body. The proofs stay fast to check and their pages small. No build check
guards this. A later proof that unfolds the readers in place still builds. It
only makes the goals, the build and the pages larger. Later changes keep this
shape (ADR-2026-11-03-0028, ADR-2026-11-03-0328).
