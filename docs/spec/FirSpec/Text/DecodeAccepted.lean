import VersoManual
import Fir.Text.DecodeAccepted
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on what the second pass accepts, which
renders `Fir.Text.DecodeAccepted` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "What the second pass accepts: readable blocks" =>

:::readable Fir.Text.WritableDef (pin := Fir.DialectText) (fingerprint := "17118176371775235432")
*Definition: a definition that can be written and read back.* Let $`d` be
a dialect with a {ref "The-fir-specification--Text-format--Grammar"}[text].
A value $`x` with its type $`t` _can be written and read back_ when $`x`
is a name, $`\mathrm{tyattr}(t)` is written as a type, and
$`\mathrm{decodety}(\mathrm{tyattr}(t)) = t`. Here $`\mathrm{tyattr}(t)`
is the attribute that the dialect writes for $`t`, and
$`\mathrm{decodety}(a)` the type that it reads back from the attribute
$`a`, when there is one. These are the conditions that a
{ref "The-fir-specification--Text-format--Round-trips"}[well-formed]
function asks of each value it defines.
:::

:::readable Fir.Text.operandTypes_ok (pin := Fir.Text.operandTypes) (fingerprint := "11110381137751027255")
*Lemma: the operands' types come from the scope.* For every dialect,
scope $`\mathit{sc}`, function symbol, list of operands
$`x_1, \dots, x_n`, each with its position, and list of types
$`\mathit{ts}`: when the types of the operands, found in the scope, are
$`\mathit{ts}`, then $`\mathit{ts}` is $`t_1, \dots, t_n` with
$`\mathrm{lookup}_{\mathit{sc}}(x_i) = t_i` for each $`i`. Here
$`\mathrm{lookup}_{\mathit{sc}}(x)` is the type that the scope
$`\mathit{sc}` gives the value $`x`. The decoder looks up each operand in
the scope, in order, and fails at the first one that the scope does not
give a type.
:::

:::readable Fir.Operation.AcceptedIn (pin := Fir.Func.OpWellFormed) (pin := Fir.Succ.Writable) (pin := Fir.Location.limit) (pin := Fir.DialectSignature) (pin := Fir.DialectText) (fingerprint := "7189482657483562352")
*Definition: an op that a scope accepts.* Let $`d` be a dialect with a
{ref "The-fir-specification--Abstract-syntax--Dialects"}[signature] and a
text, $`\mathit{sc}` a scope, and $`o` an op with the op instance $`p`.
The scope $`\mathit{sc}` _accepts_ $`o` when:

* $`\mathrm{opname}(p)` is a word;
* every attribute of $`\mathrm{opattrs}(p)` can be
  {ref "The-fir-specification--Text-format--Grammar"}[written];
* $`o` has as many operands $`x_1, \dots, x_n` as $`\mathrm{sig}(p)` has
  types $`t_1, \dots, t_n`, and $`\mathrm{lookup}_{\mathit{sc}}(x_i) = t_i`
  for each $`i`;
* the types of the results of $`o`, in order, are $`\mathrm{ret}(p)`;
* each successor of $`o` can be
  {ref "The-fir-specification--Text-format--What-the-grammar-accepts"}[written]:
  its label is a name, and so is each value that it passes;
* the location reference of $`o` is below $`2^{32}`;
* each result of $`o`, a value with its type, can be written and read
  back.

Here $`\mathrm{opname}(p)` and $`\mathrm{opattrs}(p)` are the name and the
attributes that the dialect writes for $`p`, and $`\mathrm{sig}(p)` and
$`\mathrm{ret}(p)` the types of its operands and results. The first six
conditions are those of an op
{ref "The-fir-specification--Text-format--Round-trips"}[well formed] in a
function $`f`, with the scope in place of the type that $`f` gives each
value; the second pass knows the scope, and not yet the function.
:::

:::readable Fir.Block.AcceptedIn Fir.Block.AllAcceptedIn Fir.Operation.AllAcceptedIn Fir.Region.AllAcceptedIn (pin := Fir.Block.allBlocks) (pin := Fir.Operation.regionBlocks) (pin := Fir.Region.allBlocks) (fingerprint := "6461851756803125000")
*Definition: blocks, ops and regions that a scope accepts.* Let $`d` be a
dialect with a signature and a text, and $`\mathit{sc}` a scope. The scope
$`\mathit{sc}` _accepts_ a block $`b` when:

* the label of $`b` is a name;
* each argument of $`b`, a value with its type, can be written and read
  back;
* $`\mathit{sc}` accepts each op of $`b`.

It accepts a list of blocks _at any depth_ when it accepts each of the
blocks and each block of their ops' regions, at any depth; a list of ops
at any depth, when it accepts each of the ops and each block of their
regions, at any depth; and a list of regions at any depth, when it accepts
each block of the regions, at any depth.
:::

:::readable Fir.Text.decodeType_writable (pin := Fir.Text.decodeType) (pin := Fir.LawfulDialectText) (fingerprint := "267462141306649413")
*Theorem: a type as read decodes back to itself.* Let $`d` be a dialect
with a signature, validation rules and a text, whose text is
{ref "The-fir-specification--Text-format--Grammar"}[lawful]. For every
attribute $`a` written as a type, position, and type $`t`: when decoding
$`a` gives $`t`, then $`\mathrm{tyattr}(t)` is written as a type and
$`\mathrm{decodety}(\mathrm{tyattr}(t)) = t`. A law of a lawful text says
that a type that decodes from an attribute is written as that attribute:
$`\mathrm{decodety}(a) = t` implies $`\mathrm{tyattr}(t) = a`.
:::

:::readable Fir.Text.decodeDef_writable Fir.Text.mapM_decodeDef_writable (pin := Fir.Text.decodeDef) (pin := Fir.Text.SDef.Writable) (fingerprint := "745076737604750857")
*Theorems: a definition as read decodes to one that can be written and
read back.* Let $`d` be a dialect with a signature, validation rules and a
text, whose text is lawful:

* for every definition as read that can be
  {ref "The-fir-specification--Text-format--What-the-grammar-accepts"}[written],
  and every value with its type: when the definition decodes to them,
  they can be written and read back;
* for every list of definitions as read each of which can be written, and
  every list of values with their types: when decoding each definition of
  the first list gives the second, each entry of the second can be
  written and read back.

A definition decodes to its value's name, which is a name, and to the type
that its type as read decodes to.
:::

:::readable Fir.Text.DecodesTo (fingerprint := "5539786797089077202")
*Definition: what a pass gives on a part that meets a condition.* For a
pass $`\mathrm{decode}` over parts of the tree, a condition $`W` on parts
and a property $`P` of what it gives, $`\mathrm{decode}` _takes_ a part
$`a` _from_ $`W` _to_ $`P` when, if $`W` holds of $`a`, $`P` holds of
everything that $`\mathrm{decode}` gives from $`a`:

$$`\begin{aligned} & W(a) \implies \forall x.\ \mathrm{decode}(a) = \mathsf{ok}(x) \\ & \quad \implies P(x) \end{aligned}`
:::

:::readable Fir.Text.decodes_blocks_nil Fir.Text.decodes_blocks_cons Fir.Text.decodes_ops_nil Fir.Text.decodes_ops_cons Fir.Text.decodes_regions_nil Fir.Text.decodes_regions_cons (pin := Fir.Text.decodeBlocks) (pin := Fir.Text.decodeOps) (pin := Fir.Text.decodeRegions) (pin := Fir.LawfulDialectText) (pin := Fir.Text.SOp.Writable) (pin := Fir.DialectText) (fingerprint := "4351980553499127475")
*Theorems: the second pass, part by part.* Let $`d` be a dialect with a
signature and a text, $`\mathit{sc}` a scope and $`g` a function's
symbol. Each pass below decodes in $`\mathit{sc}`, for $`g`, and
{ref "The-fir-specification--Text-format--What-the-second-pass-accepts"}[takes]
its parts from "can be written" to "accepted by $`\mathit{sc}` at any
depth":

* the second pass over blocks takes no blocks there;
* when $`d` also has validation rules and its text is lawful: for every
  label, list of arguments, list of ops and list of blocks $`B` as read,
  when the pass over ops takes those ops there and the pass over blocks
  takes $`B` there, the pass over blocks takes the block with that label,
  those arguments and those ops, followed by $`B`, there;
* the second pass over ops takes no ops there;
* when $`d` also has validation rules and its text is lawful: for every op
  as read and list of ops $`O` as read, when the pass over regions takes
  the op's regions there and the pass over ops takes $`O` there, the pass
  over ops takes the op followed by $`O` there;
* the second pass over regions takes no regions there;
* for every list of blocks and list of regions $`R` as read, when the
  pass over blocks takes those blocks there and the pass over regions
  takes $`R` there, the pass over regions takes the region of those
  blocks, followed by $`R`, there.

For an op, a law of a lawful text says that the op instance $`p` that
$`\mathrm{decodeop}(n, a^*, t^*, r^*)` gives has $`\mathrm{opname}(p) = n`,
$`\mathrm{opattrs}(p) = a^*`, $`\mathrm{sig}(p) = t^*` and
$`\mathrm{ret}(p) = r^*`. Its name $`n` and attributes $`a^*` come from
the tree, so they can be written; the operand types $`t^*` come from the
scope; and $`r^*` are the types of the op's results.
:::

:::readable Fir.Text.SBlock.decodesTo Fir.Text.SOp.decodesTo Fir.Text.SRegion.decodesTo (pin := Fir.Text.DecodesTo) (fingerprint := "3691386830373890341")
*Theorems: the second pass, at any depth.* Let $`d` be a dialect with a
signature, validation rules and a text, whose text is lawful. For every
scope $`\mathit{sc}` and function symbol $`g`, the second pass over
blocks, in $`\mathit{sc}` and for $`g`, takes every list of blocks as
read from "can be written" to "accepted by $`\mathit{sc}` at any depth";
and so do the passes over ops and over regions, for every list of ops and
every list of regions as read. They are proved together, by recursion on
the tree: each applies the theorems of the previous block to the parts
that it holds.
:::
