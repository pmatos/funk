import VersoManual
import Fir.Text.ReadAccepted
import Fir.Text.Decode
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on what the grammar accepts, which
renders `Fir.Text.ReadAccepted` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "What the grammar accepts: readable blocks" =>

:::readable Fir.Succ.Writable (fingerprint := "16490823247820214509")
*Definition: a successor that can be written.* A
{ref "The-fir-specification--Abstract-syntax--Modules___-functions___-blocks-and-ops"}[successor]
_can be written_ when its label is a name, and so is each value that it
passes. These are the names that the printer writes after `^` and `%`.
:::

:::readable Fir.Location.InLimits (pin := Fir.Location.numbers) (pin := Fir.Location.refs) (pin := Fir.Location.limit) (fingerprint := "14594947355850245201")
*Definition: a location within the limits.* A
{ref "The-fir-specification--Abstract-syntax--Locations"}[location] is
_within the limits_ when each of the numbers it holds is below $`2^{32}`:
the lines and columns of a source range, or the location references that
a $`\mathsf{callsite}`, $`\mathsf{fused}` or $`\mathsf{derived}` location
is built from. Every implementation holds these numbers in 32 bits.
:::

:::readable Fir.Text.SDef.Writable (pin := Fir.Attr.IsType) (fingerprint := "18244378496080690369")
*Definition: a definition as read that can be written.* A
{ref "The-fir-specification--Text-format--Reading-the-grammar"}[definition as read],
$`\mathit{sdef}`, _can be written_ when its value's name is a name, and
its type is
{ref "The-fir-specification--Text-format--Grammar"}[written as a type]: a
word, or a word applied to attributes, that can be written.
:::

:::readable Fir.Text.SOp.Writable Fir.Text.SRegion.WritableList Fir.Text.SBlock.WritableList Fir.Text.SOp.WritableList (pin := Fir.Succ.Writable) (pin := Fir.Location.limit) (pin := Fir.Text.operandTypes) (fingerprint := "4991093508923232133")
*Definition: ops, regions and blocks as read that can be written.* These
conditions are on the
{ref "The-fir-specification--Text-format--Reading-the-grammar"}[tree]
that the grammar reads, at any depth. An op as read, $`\mathit{sop}`, _can
be written_ when:

* each of its results can be written;
* its name is a word;
* each of its attributes can be
  {ref "The-fir-specification--Text-format--Grammar"}[written];
* each of its successors can be written: its label is a name, and so is
  each value it passes;
* its regions can be written;
* its location reference is below $`2^{32}`.

A list of regions can be written when the blocks of each region can. A
list of blocks can be written when, for each block, its label is a name,
each of its arguments can be written, and its ops can. A list of ops can
be written when each of its ops can. The four are defined together, since
an op holds regions, which hold blocks, which hold ops.

An op's operands are not in the list: decoding finds each of them among
the definitions of its function, whose names are names, and rejects one
that is not there.
:::

:::readable Fir.Text.SBody.Writable Fir.Text.SItem.Writable Fir.Text.SModule.Writable (pin := Fir.LocTable.InLimits) (pin := Fir.Location.limit) (pin := Fir.Text.decodeItem) (fingerprint := "1337409852049701888")
*Definition: items and modules as read that can be written.* The body of
an item as read can be written when it holds blocks that can be written,
or when it holds items, whatever they are. An item as read can be written
when each of its parameters can be written, each of its result types is
written as a type, and its body can be written. A module as read can be
written when each of its items can be written, and every number of its
{ref "The-fir-specification--Abstract-syntax--Locations"}[location table],
each key and each number of each location, is below $`2^{32}`.

Nothing is asked of an item's kind, symbol or attributes, nor of the items
inside a body: decoding accepts only a `func` without attributes, whatever
its symbol, and rejects a body made of items unless it has no items.
:::

:::readable Fir.Text.TokensWritable.tail Fir.Text.TokensWritable.value Fir.Text.TokensWritable.label Fir.Text.TokensWritable.word Fir.Text.TokensWritable.locRef (pin := Fir.Text.TokensWritable) (pin := Fir.Text.Tok.Writable) (pin := Fir.Location.limit) (fingerprint := "13344365767966384269")
*Lemmas: what a list of tokens that can be written says of its first
token.* For every token $`t`, position and list of tokens
$`\mathit{ts}`, when the list $`t` followed by $`\mathit{ts}` can be
{ref "The-fir-specification--Text-format--What-the-lexer-accepts"}[written]:

* $`\mathit{ts}` can be written;
* when $`t` is a value $`\mathsf{value}~x` or a label
  $`\mathsf{label}~x`, $`x` is a name;
* when $`t` is a word $`\mathsf{word}~w`, $`w` is a word;
* when $`t` is a location reference $`\mathsf{locref}~r`, $`r < 2^{32}`.

These are the only facts about tokens that the readers below need: each
reader takes a name, a word or a reference from the token it reads.
:::

:::readable Fir.Text.fail_ne_ok (pin := Fir.Text.fail) (fingerprint := "3450482005068552809")
*Lemma: a reader that fails reads nothing.* For every list of tokens and
what was expected, the failure of a reader is an error, never a result.
It closes the cases of the proofs below in which a reader fails.
:::

:::readable Fir.Text.ReadsWritable (fingerprint := "16820333930195190109")
*Definition: a reader that gives a property on tokens that can be
written.* A reader $`\mathit{read}` _gives_ $`P` _on_ $`\mathit{ts}`
when, if $`\mathit{ts}` can be written and $`\mathit{read}` reads $`a`
from $`\mathit{ts}`, leaving the tokens $`r`, then $`P` holds of $`a` and
$`r` can be written:

$$`\begin{aligned} & \mathrm{writable}(\mathit{ts}) \wedge \mathit{read}(\mathit{ts}) = \mathsf{ok}(a, r) \\ & \quad \implies P(a) \wedge \mathrm{writable}(r) \end{aligned}`

for every $`a` and $`r`. Here $`\mathsf{ok}(a, r)` is the result of a
reader that reads $`a` and leaves $`r`. The tokens that a reader leaves
are always a suffix of $`\mathit{ts}`, so they can be written too; but a
reader's definition records only that there are no more of them than in
$`\mathit{ts}`, which is what shows that the parser ends, not that they
are a suffix of it. So the definition asks for it, and each lemma below
shows it.
:::

:::readable Fir.Text.expect_writable Fir.Text.keyword_writable Fir.Text.readMore_writable (pin := Fir.Text.expect) (pin := Fir.Text.keyword) (pin := Fir.Text.readMore) (fingerprint := "9387520422673248992")
*Lemmas: the basic readers.* For every list of tokens $`\mathit{ts}`:

* for every token $`t` and what was expected, the reader of the one token
  $`t` gives, on $`\mathit{ts}`, the property that always holds: it reads
  only $`t`, and leaves the rest;
* for every word, so does the reader of that keyword;
* for every reader $`\mathit{item}` and property $`P` such that
  $`\mathit{item}` gives $`P` on every list of tokens, the reader of the
  rest of a list, which reads a comma and an element with
  $`\mathit{item}` as long as a comma follows, gives on $`\mathit{ts}`
  that $`P` holds of each element it reads.
:::

:::readable Fir.Text.readAttr_writable Fir.Text.readType_writable Fir.Text.readAttrs_writable (pin := Fir.Text.readAttr) (pin := Fir.Text.readAttrArgs) (pin := Fir.Text.readMoreAttrArgs) (pin := Fir.Text.readType) (pin := Fir.Text.readAttrs) (pin := Fir.Attr.Writable) (pin := Fir.Attr.AllWritable) (pin := Fir.Attr.IsType) (fingerprint := "2210644183673439788")
*Theorems: attributes and types as read can be written.* For every list of
tokens:

* the reader of an
  {ref "The-fir-specification--Text-format--Reading-the-grammar"}[attribute]
  gives, on it, that the attribute it reads can be written: each of its
  words, and the head of each applied word, at any depth, is a word;
* the reader of the arguments of an applied attribute, after its `(`, and
  the reader of the arguments after the first, give that each argument
  they read can be written;
* the reader of a type gives that the type it reads is written as a type:
  a word, or a word applied to attributes, that can be written;
* the reader of the attributes of an op or an item gives that each
  attribute it reads can be written.

The first three readers call one another, so the first two facts are
proved together, by induction that follows the readers' own recursion.
Each word comes from a word token, which is a word.
:::

:::readable Fir.Text.readDefType_writable Fir.Text.readDef_writable Fir.Text.readDefs_writable (pin := Fir.Text.readDefType) (pin := Fir.Text.readDef) (pin := Fir.Text.readDefs) (pin := Fir.Text.SDef.Writable) (fingerprint := "4512358889900069401")
*Theorems: definitions as read can be written.* For every list of tokens:

* for every name $`x` and position, the reader of the `:` and the type of a
  definition of $`x` gives that the definition it reads is of $`x`, and
  that its type is written as a type;
* the reader of a definition gives that the definition it reads can be
  written: its value is a name, since it comes from a value token, and its
  type is written as a type;
* the reader of one or more definitions, separated by commas, gives that
  each of them can be written.
:::

:::readable Fir.Text.readSuccArgs_writable Fir.Text.readSucc_writable Fir.Text.readMoreOperands_writable Fir.Text.readOperands_writable Fir.Text.readOpLoc_writable (pin := Fir.Text.readSuccArgs) (pin := Fir.Text.readSucc) (pin := Fir.Text.readMoreOperands) (pin := Fir.Text.readOperands) (pin := Fir.Text.readOpLoc) (pin := Fir.Succ.Writable) (pin := Fir.Location.limit) (pin := Fir.Text.operandTypes) (fingerprint := "8610404709604926096")
*Theorems: successors and an op's location reference as read can be
written.* For every list of tokens:

* the reader of the values that a successor passes, after its `(`, gives
  that each of them is a name: each comes from a value token;
* the reader of a successor gives that the successor can be written: its
  label comes from a label token;
* the reader of the operands after the first, then the successors, and the
  reader of an op's operands and successors, give that each successor
  they read can be written;
* the reader of an op's location reference gives that the reference is
  below $`2^{32}`: it comes from a location reference token.

Nothing is said of the operands: decoding finds each of them among the
definitions of its function.
:::
