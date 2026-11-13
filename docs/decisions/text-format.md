# Current decisions: text format and parsing

This page says what holds today for fir's text format and its parsers. It is the
record: when this page and an ADR disagree, the page wins, and the ADR is fixed
or deleted (ADR-2026-11-09-1610). How the proofs about the text are built is on
[text-format-proofs.md](text-format-proofs.md), and how float constants and
float ops are written is on [text-format-floats.md](text-format-floats.md).

## One canonical text

fir has one canonical text form. It has no sugar and no alternative
spellings. The grammar has exactly one spelling for every construct
(ADR-2026-10-29-2014). The human chose this on 2026-10-29 (P3 on #5).

The printer is the formatter. `funk fmt` prints a module in canonical form.

Value names, attributes and locations are stored in the IR and printed as
stored. Nothing is renumbered. A module keeps the names its producer gave
it. So diffs stay small, and diagnostics name values as the author wrote them
(ADR-2026-10-29-2014).

The text format is the interface between Lean and Rust. Rust prints a module.
Lean parses and reprints it. The bytes must match (ADR-2026-10-29-2014).

Every op of every dialect uses one grammar, so a new dialect needs no parser
change (ADR-2026-10-29-2014). The same holds for items: a dialect
registers kinds of item through the one grammar, so a new kind needs no
parser change (ADR-2026-11-09-1543). The core's kinds are `func` and
`module` (ADR-2026-11-10-1510). Any other kind is a word of a dialect, such
as `toy.cell`, written `kind @sym(params) -> results attrs {` and then `}`
on the next line: its body is empty. Every reader decodes such an item,
whichever dialects it holds; a body that is not empty does not decode, and
any other bare kind is still a parse error, so M0 texts are unchanged
(ADR-2026-11-09-1543).

Rejected: sugar or alternative spellings. Each one breaks
`print(parse(t)) == t`, or needs a normalizing step in both implementations
(ADR-2026-10-29-2014).

## The dialect set

A module's text may start with its dialect set: the word `dialects`, the
names of the dialects other than the core whose words it writes, separated
by `, `, then an empty line, as in `dialects toy, gpu`. A module that names
no dialect has no such line, so every M0 text is unchanged. The word
`dialects` is no item's kind, as `locs` is not, and the lexer is unchanged.
The grammar is `module ::= ('dialects' word (',' word)*)? item* locs`. The
names keep the order the text gives them: nothing sorts or merges them
(ADR-2026-11-10-1306).

A valid module names each dialect once, by a word. Each name must be a
dialect that the reader holds, other than the core (`names d` in Lean, a
registered dialect in Rust), and every word of the module must name the core
or a dialect of its set: op names, attribute words and type words, at any
depth. Both validators check this as `Module.InDialectSet`, in
`lean/Fir/Validation/DialectSet.lean`. The rule reads words, which the
dialect's text gives, so it sits beside `Module.Valid`, not in it, and the
theorems about valid modules need no text (ADR-2026-11-10-1306). A region
kind's word (ADR-2026-11-10-1941) and an item kind's word
(ADR-2026-11-09-1543) join the rule too.

`funk verify` and `fir-ref validate` report the problems of
`Module.problems`, then those of `Module.setProblems`. A function that writes
a word outside the set gets one problem, naming the first such dialect in the
order of `Func.wordDialects`: the types the function states, then each op's
name, attributes and region kinds. `tests/dialects/dialect-set.cases` holds
must-accept and must-reject cases that both validators read
(ADR-2026-11-10-1306). A dialect's dependencies do not yet constrain the set:
a module that names `toy` need not name what `toy` depends on beyond the
core. ADR-2026-10-30-1146 says that the set is to use them; no check does
yet.

Rejected: a `module` item that holds the items, with the set as its
attribute, since it would change every M0 text; the set in parentheses,
`dialects(toy, gpu)`, which reads as an applied attribute; and rejecting an
unknown word at parse time, since a builder or a pass can make a module that
no text wrote (ADR-2026-11-10-1306).

The data layout follows the dialect set, on a line of its own that starts
with the word `layout`, and a module with the empty layout writes none:
[text-format-layout.md](text-format-layout.md) gives its spelling and rules
(ADR-2026-11-12-1821).

## Nested modules

A `module` item is a module nested in another: `module @dev() { ... }`, with
the parentheses that every item writes and no parameters, results or
attributes. Its body is a module's text without the location table: an
optional dialect set, `dialects gpu` and an empty line, then its items, each
followed by an empty line. An empty body, `{ }`, is a module with no dialect
and no items. The grammar is
`body ::= '{' (('dialects' word (',' word)*)? item* | block*) '}'`. A
`module` with parameters, results, attributes or blocks does not decode, and
neither does a `func` whose body holds a dialect set or items
(ADR-2026-11-10-1510).

The body is printed two spaces deeper than the `module` line, and its `}` at
that line's indentation. An empty line has no spaces. A function at
indentation `n` writes its header, labels and `}` at `n` and its ops at
`n + 2`, so a top-level module prints as in M0. One location table, at the
end of the text, serves every item at any depth (ADR-2026-11-10-1510).

A nested module is a symbol table of its own, and its dialect set is its own:
one that names no dialect uses the core alone, whatever its parent names. An
op refers by symbol only to an item of its own table. `Module.funcs` is the
functions of the top-level table; a nested module's functions run only
through what its own dialects define, such as a device's kernels
(ADR-2026-11-10-1510, ADR-2026-11-09-1545). Validation checks each table with
the same rule: the page on validation says how.

Rejected: the set as the item's attributes, `module @dev() gpu {`, which
spells one set two ways; nested items at their module's indentation, which
makes deep nests hard to read; and a set inherited from the parent, since a
host module could not then hold a device module that does not use the host's
dialects (ADR-2026-11-10-1510).

## Region kinds

A region names its kind. A region of an op writes its kind as a word right
after its `{`, as in `toy.run { toy.graph`. The grammar is
`region ::= '{' word? block* '}'`; a block starts with a label, so the word
is never read as anything else. The core's kind, a control-flow graph, writes
nothing there, so every M0 text is unchanged. A function's body is always of
the core's kind and its text names none: a word after an item's `{` starts
its items. Validation rejects a function whose body names a kind. A region
that names a kind names it by a word, so that the round trip holds, and
Rust's well-formed generator names kinds, so the cross-language round trip
covers them (ADR-2026-11-10-1530). An op may own regions only of the kinds
its op instance states, and a kind's word joins the module's dialect set
(ADR-2026-11-10-1941).

Rejected: the kind before the `{`, which a parser would read as an attribute
without a second token of lookahead; the kind fixed by the owning op, as MLIR
does, since a reader would then need the dialect to know how a region is
read; and `{kind(toy.graph)`, longer with no gain (ADR-2026-11-10-1530).

## One format

Text is fir's only format in v0 (ADR-2026-10-29-2014). Rejected: a binary
format, left out on purpose; it can come later if text parsing becomes a
bottleneck.

Text has no nesting limit. Every text the grammar accepts is read at any
depth (ADR-2026-10-30-1549).

`funk fmt` parses a file but does not validate it. Every module that parses
has a canonical form
([rust-ir-and-tools-funk.md](rust-ir-and-tools-funk.md#commands-and-verdicts)).

Numbers have limits. An integer type `iN` has `1 <= N <= 16,777,215`, and a
float type has at most as many bits in all (ADR-2026-11-09-1549). A
location reference, a line and a column are below `2^32`. An integer
attribute has no bound of its own: the dialect that reads it bounds it
(ADR-2026-10-29-2007).

## Types

A float type is written by its alias when it has one: `f16`, `bf16`, `f32`,
`f64` or `f128`. Every other format `float<e,m>` is written `float(e, m)`, the
grammar's applied form, such as `float(5, 2)`. `float<e,m>` is notation, not
text. `float(e, m)` of a format with an alias does not decode, so each format
has one spelling, and neither does a negative number, another argument list, an
alias applied to arguments or the bare word `float` (ADR-2026-11-11-0951). The
human ruled on 2026-11-11: "Leave it as is. No need for angle brackets then."
The orchestrator recorded the ruling on #229. Rejected: `float<e,m>` in text,
which needs angle brackets in both parsers and new round-trip proofs for one
type family; and aliases as a second spelling, which breaks
`print(parse(t)) == t`.

A pointer type `ptr<0>`, the default memory's, is written `ptr`, so M0's texts
are unchanged. `ptr<N>` of another memory is written `ptr(N)`, the grammar's
applied form, such as `ptr(1)`. `ptr(0)` does not decode, so each pointer type
has one spelling, and neither does a negative memory, one above 16,777,215
(LLVM's bound on address spaces), `ptr()` or another argument list. Whether
the module has memory `N` is validation's rule: its data layout must declare
`N` ([text-format-layout.md](text-format-layout.md#valid-layouts)). A dialect that adds memories
names their pointers in its own types; `ptr(N)` is the core's
(ADR-2026-11-11-1709). Rejected: `ptr<N>` in text, for the reason
`float<e,m>` was; `ptr(0)` as a second spelling of `ptr`; and rejecting an
undeclared memory at parse time, since a builder or a pass can change the
data layout without text.

## The round trip

`parse(print(m)) == m` holds for every well-formed module.
`print(parse(t)) == t` holds for every text printed from one
(ADR-2026-10-29-2014).

A well-formed module is one whose printed form says everything it holds. The
spec defines it as `Module.WellFormed` in `lean/Fir/Text/RoundTrip.lean`.

The limit exists because text writes types only where values are defined. A
parser finds an op's operand types at the definitions of its operands. So an
op whose operand is undefined or has the wrong type has no text that reads
back to it. The human ruled on 2026-10-30 to narrow the round trip to
well-formed modules (choice 1 of the rulings on #5). Rejected: a full
signature on every op, as MLIR's generic form writes `: (i32, i32) -> i1`,
which would round-trip ill-typed modules too, but writes every type twice and
makes op lines long (ADR-2026-10-29-2014).

Every valid module is well formed. Validation checks the characters of value
names and labels and the limits on numbers. Symbols that are not words are
quoted. So two different valid modules never print the same text. The spec
proves this as `validIsWellFormed`, for every dialect whose text meets the
laws of `LawfulDialectText`. #11 proves those laws for the core dialect
(ADR-2026-10-29-2014).

Round trips are tested within Rust and across Rust and Lean, including under
fuzzing. Lean proves that parsing a printed well-formed
module gives it back, and that every module that `Fir.parse` gives is well
formed, for every dialect whose text is lawful
([text-format-proofs.md](text-format-proofs.md)).

## Parse errors and validation errors

A text that follows the grammar but does not decode is not a module. The
parser rejects it with a reason and a position (ADR-2026-10-29-2014). These
texts are rejected:

- a number out of range, located at the number (ADR-2026-10-29-2007);
- a string or symbol not in its one spelling;
- an item of an unknown kind;
- a type that does not decode;
- a value defined twice;
- an operand that is not defined;
- an op whose name, attributes and types do not decode, such as a type
  mismatch.

Every other error, such as an undefined successor argument, is a validation
error on a module that parsed (ADR-2026-10-29-2014).

A type mismatch or an undefined operand in text is a parse error. Its tests
are parser tests, not verifier tests. An op that a
builder or a pass made ill-typed is a validation error (ADR-2026-10-30-1146).

Lean's and Rust's parsers must reject the same texts
(ADR-2026-10-29-2014). Tests compare only whether a text is rejected, not the
wording of the reason.

## Locations

Every op has a location field. The field always exists, and `unknown` is a
valid value (ADR-2026-10-29-2013). The human chose this on 2026-10-29 (H8 on
#5).

An op cannot be built without a location. The `funk-ir` builder requires one,
and the verifier checks that every op has one. Every pass must give each op
it creates a location (ADR-2026-10-29-2013). Rejected: an optional location,
which a pass drops by accident with nothing to notice
(ADR-2026-10-29-2013).

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
(ADR-2026-10-29-2013). The file is a string. Then come the line and column of
the start, the word `to`, and the line and column of the end. The human ruled
this on 2026-10-30 (choice 16 of the rulings on #5).

The end is exclusive. It is the position just after the range's last byte. A
range whose end equals its start is empty, so an empty range can be written
(ADR-2026-10-29-2013).

Columns count UTF-8 bytes, from 1. Column 0 means that the column is unknown.
So a column does not depend on how a tool counts characters. Lines count from
1 (ADR-2026-10-29-2013).

The separator is the word `to`, not `-`. So the lexer reads a range without
depending on context (ADR-2026-10-29-2013).

Rejected: the M0 epic's sketch, `file:line:col-line:col`, with an inclusive
end, which cannot write an empty range, and a `-` separator, which makes the
lexer depend on context (ADR-2026-10-29-2013).

The spec states this form in `lean/Fir/Syntax/Location.lean` and
`lean/Fir/Text/Grammar.lean`. The Lean printer and `funk-ir` both print it,
and `tests/fir/canonical/locations.fir` holds an empty range and a range with
column 0.
