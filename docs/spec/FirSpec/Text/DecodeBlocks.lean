import VersoManual
import Fir.Text.DecodeBlocks
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on blocks and ops decoded back, which
renders `Fir.Text.DecodeBlocks` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Blocks and ops decoded back: readable blocks" =>

:::readable Fir.Text.Decodes (fingerprint := "4160001921508362595")
*Definition: decoding gives a part back.* Let $`\mathit{decode}` be a step
that decodes some part of a tree, or fails, $`\tau` a part without
positions, and $`x` a value. $`\mathit{decode}` _gives $`x` back from
$`\tau`_ when it succeeds with $`x` on every part that
{ref "The-fir-specification--Text-format--The-tree-that-the-grammar-reads"}[erases]
to $`\tau`, whatever its positions.
:::

:::readable Fir.Text.operandTypes_eq (pin := Fir.Text.operandTypes) (fingerprint := "11943811892251266912")
*Theorem: the operands' types are found in the scope.* For every dialect,
scope $`\mathit{sc}`, every function symbol (it names the function only
in error messages), operands $`x_1, \dots, x_n` at any positions and
types $`t_1, \dots, t_n`: if $`\mathit{sc}` gives each
$`x_i` the type $`t_i`, then finding the
{ref "The-fir-specification--Text-format--Decoding"}[types of the operands]
gives $`t_1, \dots, t_n`.
:::

:::readable Fir.decodeOps_nil Fir.decodeBlocks_nil Fir.decodeBlocks_cons Fir.decodeRegions_nil Fir.decodeRegions_cons (pin := Fir.Text.decodeOps) (pin := Fir.Text.decodeBlocks) (pin := Fir.Text.decodeRegions) (fingerprint := "4327499180448194707")
*Theorems: the second pass gives back no ops, and blocks and regions one
at a time.*
For every dialect with a
{ref "The-fir-specification--Text-format--Grammar"}[text format], every
scope and any function symbol, the
{ref "The-fir-specification--Text-format--Decoding"}[second pass] gives
back ops, blocks and regions from their trees:

* no ops, no blocks and no regions, from the trees of none;
* a block $`b` followed by blocks $`b^*`, when the types of the arguments
  of $`b` decode back to themselves, the pass on ops gives the ops of $`b`
  back from their trees, and the pass on blocks gives $`b^*` back from
  their trees;
* a region $`r` followed by regions $`r^*`, when the pass on blocks gives
  the blocks of $`r` back from their trees, and the pass on regions gives
  $`r^*` back from their trees.

A type $`T` decodes back to itself when
$`\mathrm{decodety}(\mathrm{tyattr}(T)) = T`. The case of an op follows,
once its condition is defined.
:::

:::readable Fir.Operation.DecodesIn Fir.Block.DecodesIn (pin := Fir.DialectSignature) (fingerprint := "15495677668507595244")
*Definitions: an op, and a block, that decode in a scope.* For every
dialect with signatures and a text format, an op $`o` with the op instance
$`\iota` _decodes in_ the scope $`\mathit{sc}` when:

* $`\mathit{sc}` gives the operands of $`o`, in order, the types of
  $`\mathrm{sig}(\iota)`;
* the types of the results of $`o`, in order, are $`\mathrm{ret}(\iota)`;
* the type of each result of $`o` decodes back to itself.

Here $`\mathrm{sig}(\iota)` and $`\mathrm{ret}(\iota)` are the operand and result
types that the dialect's
{ref "The-fir-specification--Abstract-syntax--Dialects"}[signature] gives
$`\iota`. A block decodes in $`\mathit{sc}` when the types of its arguments
decode back to themselves and each of its ops decodes in $`\mathit{sc}`.
These are what the second pass needs to give an op back: with them, the
dialect's decoder of ops is given exactly what the op instance encodes.
:::

:::readable Fir.Func.WellFormed.decodesIn (pin := Fir.Func.WellFormed) (pin := Fir.Func.OpWellFormed) (pin := Fir.Func.typeOf) (pin := Fir.Func.allBlocks) (fingerprint := "14807907631051090133")
*Theorem: the blocks of a well-formed function decode in a scope that
gives each value its type.* For every dialect
with signatures and a text format, every
{ref "The-fir-specification--Text-format--Round-trips"}[well-formed]
function $`f`, and every scope that gives each name $`x` the type
$`\mathrm{type}_f(x)`, and no type when $`f` does not define $`x`: each
block of $`f`, at any depth, decodes in that scope. Here
$`\mathrm{type}_f(x)` is the type of the
{ref "The-fir-specification--Validation--Scope-and-symbols"}[first definition]
of $`x` in $`f`.

A well-formed function gives the operands of each op the types of its
signature, gives its results the types it returns, and states only types
that decode back to themselves, so each condition holds.
:::

:::readable Fir.decodeOps_cons (pin := Fir.LawfulDialectText) (pin := Fir.Text.decodeOps) (fingerprint := "5965914291365676264")
*Theorem: the second pass gives an op back.* For every dialect with
signatures, validation rules and a text format whose text is
{ref "The-fir-specification--Text-format--Grammar"}[lawful], every scope
$`\mathit{sc}`, any function symbol, op $`o` and ops $`o^*`: if $`o` decodes
in $`\mathit{sc}`, the pass on regions gives the regions of $`o` back from
their trees, and the pass on ops gives $`o^*` back from their trees, then
the pass on ops gives $`o` followed by $`o^*` back from their trees.

The law of lawful text that decoding the name, attributes, operand types
and result types of an op instance $`\iota` gives $`\iota`,

$$`\begin{aligned} & \mathrm{decodeop}(\mathrm{opname}(\iota), \mathrm{opattrs}(\iota), \\ & \quad \mathrm{sig}(\iota), \mathrm{ret}(\iota)) = \iota \end{aligned}`

is what gives the op instance back. Here $`\mathrm{decodeop}` is the
dialect's decoder of ops.
:::

:::readable Fir.Block.decodesList Fir.Operation.decodesList Fir.Region.decodesList (pin := Fir.Block.allBlocks) (pin := Fir.Operation.regionBlocks) (pin := Fir.Region.allBlocks) (fingerprint := "4519125950715833119")
*Theorems: the second pass gives blocks, ops and regions back, at any
depth.* For every dialect with signatures, validation rules and a lawful
text, every scope $`\mathit{sc}` and any function symbol:

* the pass on blocks gives blocks $`b^*` back from their trees, when each
  of $`b^*` and each block of their ops' regions, at any depth, decodes in
  $`\mathit{sc}`;
* the pass on ops gives ops $`o^*` back from their trees, when each op of
  $`o^*` decodes in $`\mathit{sc}`, and so does each block of their
  regions, at any depth;
* the pass on regions gives regions $`r^*` back from their trees, when
  each of their blocks, at any depth, decodes in $`\mathit{sc}`.

The three are proved together, by recursion on the blocks, ops and
regions, from the lemmas above.
:::
