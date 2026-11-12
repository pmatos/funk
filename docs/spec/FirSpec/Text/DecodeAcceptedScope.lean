import VersoManual
import Fir.Text.DecodeAcceptedScope
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on what the first pass accepts, which
renders `Fir.Text.DecodeAcceptedScope` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "What the first pass accepts: readable blocks" =>

:::moduleDocs (fingerprint := "12357358463602932005")
:::

:::readable Fir.Text.Scope.Holds.not_mem (pin := Fir.Text.Scope.Holds) (fingerprint := "3433405947972505279")
*Lemma: a value that a scope does not contain is not in its list.* For
every dialect, every
{ref "The-fir-specification--Text-format--Decoding"}[scope] $`\mathit{sc}`
and list $`L` of values with their types such that $`\mathit{sc}`
{ref "The-fir-specification--Text-format--The-decoding-step"}[holds]
$`L`, and every name $`x` that $`\mathit{sc}` does not contain, no entry
of $`L` has the name $`x`. A scope holds $`L` when it gives each value of
$`L` its type, and gives no other value a type. The lemma lets the next
theorem add a value that the scope does not contain without naming a value
twice.
:::

:::readable Fir.Text.define_holds (pin := Fir.Text.define) (pin := Fir.Text.decodeDef) (pin := Fir.Text.Scope.Holds) (fingerprint := "17944236463424358563")
*Theorem: adding definitions names each value once.* Let $`d` be a
dialect with a {ref "The-fir-specification--Text-format--Grammar"}[text].
For every list $`\mathit{xs}` of definitions as read, scopes
$`\mathit{sc}` and $`\mathit{sc}'`, and lists $`L` and $`\mathit{ys}` of
values with their types: when adding $`\mathit{xs}` to $`\mathit{sc}`
succeeds with $`\mathit{sc}'`, decoding each definition of
$`\mathit{xs}` succeeds with $`\mathit{ys}`, $`\mathit{sc}` holds $`L`,
and the names of $`L` are distinct, then $`\mathit{sc}'` holds
$`L \mathbin{+\!\!+} \mathit{ys}`, whose names are distinct:

$$`\begin{aligned} & \mathrm{define}(\mathit{sc}, \mathit{xs}) = \mathsf{ok}(\mathit{sc}') \\ & \wedge\ \mathrm{decodedefs}(\mathit{xs}) = \mathsf{ok}(\mathit{ys}) \\ & \wedge\ \mathit{sc} \text{ holds } L \wedge \mathrm{distinct}(L) \\ & \quad \implies \mathit{sc}' \text{ holds } L \mathbin{+\!\!+} \mathit{ys} \\ & \quad \phantom{\implies} \wedge\ \mathrm{distinct}(L \mathbin{+\!\!+} \mathit{ys}) \end{aligned}`

Here $`\mathrm{define}(\mathit{sc}, \mathit{xs})` adds the definitions of
$`\mathit{xs}` to $`\mathit{sc}` one by one, and is an error at a value
that the scope already holds; $`\mathrm{decodedefs}(\mathit{xs})` decodes
each definition of $`\mathit{xs}` to its value's name and its decoded type;
$`L \mathbin{+\!\!+} \mathit{ys}` is the list $`L` followed by
$`\mathit{ys}`; and $`\mathrm{distinct}(L)` says that no two entries of
$`L` have the same name. Adding a definition decodes it just as decoding
it on its own does, so the values added are exactly $`\mathit{ys}`.
:::

:::readable Fir.Text.Adds (pin := Fir.Text.Scope.Holds) (fingerprint := "1346949199127177303")
*Definition: what the first pass adds.* Let $`d` be a dialect, $`a` a part
of the tree, such as a list of blocks, ops or regions as read,
$`\mathrm{define}` a first pass that adds $`a` to a scope,
$`\mathrm{decode}` a second pass that decodes $`a` in a scope, for a
function's symbol, and $`\mathrm{defs}` a list of the values, with their
types, of what the second pass gives. The first pass _adds_ $`a` when, for
all scopes $`\mathit{sc}`, $`\mathit{sc}'` and $`\mathit{sc}_2`, every
symbol $`g`, every list $`L` of values with their types, and everything
$`x` that the second pass gives:

$$`\begin{aligned} & \mathrm{define}(\mathit{sc}, a) = \mathsf{ok}(\mathit{sc}') \\ & \wedge\ \mathrm{decode}(\mathit{sc}_2, g, a) = \mathsf{ok}(x) \\ & \wedge\ \mathit{sc} \text{ holds } L \wedge \mathrm{distinct}(L) \\ & \quad \implies \mathit{sc}' \text{ holds } L \mathbin{+\!\!+} \mathrm{defs}(x) \\ & \quad \phantom{\implies} \wedge\ \mathrm{distinct}(L \mathbin{+\!\!+} \mathrm{defs}(x)) \end{aligned}`

That is: whatever the scope that the second pass uses, the first pass adds
to any scope that holds $`L`, with distinct names, the values that
$`\mathrm{defs}` lists, and finds no value twice.
:::

:::readable Fir.Text.adds_blocks_nil Fir.Text.adds_blocks_cons Fir.Text.adds_ops_nil Fir.Text.adds_ops_cons Fir.Text.adds_regions_nil Fir.Text.adds_regions_cons (pin := Fir.Text.defineBlocks) (pin := Fir.Text.defineOps) (pin := Fir.Text.defineRegions) (pin := Fir.Text.decodeBlocks) (pin := Fir.Text.decodeOps) (pin := Fir.Text.decodeRegions) (pin := Fir.Block.scopeDefs) (pin := Fir.Operation.scopeDefs) (pin := Fir.Region.scopeDefs) (fingerprint := "15688411651180599518")
*Theorems: the first pass, part by part.* Let $`d` be a dialect with a
text. The first pass over blocks
{ref "The-fir-specification--Text-format--What-the-first-pass-accepts"}[adds]
them, against the second pass over blocks, with the definitions of the
decoded blocks in the order of the first pass:

* it adds the empty list of blocks: the first pass adds nothing, and the
  second pass gives no definitions;
* for every label, list of arguments, list of ops and list of blocks
  $`B`: when it adds the ops and the blocks $`B`, it adds the block with
  that label, those arguments and those ops, followed by $`B`.

In the same way, the first pass over ops adds the empty list of ops, and
adds an op followed by the ops $`O`, whatever its name, attributes,
operands, successors and location reference, when it adds the op's
regions and the ops $`O`; and the first pass over regions adds the empty
list of regions, and adds a region of any kind followed by the regions
$`R` when it adds the region's blocks and the regions $`R`.

The order is that of the
{ref "The-fir-specification--Text-format--The-decoding-step"}[first pass]:
a block's arguments, then the definitions of its ops, then those of the
blocks after it; an op's results, then the definitions of the blocks of its
regions, then those of the ops after it. The first pass does not look up
an op's operands. Each theorem takes what the pass does with the parts it
holds as hypotheses, as the round trip's lemmas do
(`docs/decisions/text-format-proofs.md`).
:::

:::readable Fir.Text.SBlock.adds Fir.Text.SOp.adds Fir.Text.SRegion.adds (pin := Fir.Text.Adds) (pin := Fir.Block.scopeDefs) (pin := Fir.Operation.scopeDefs) (pin := Fir.Region.scopeDefs) (fingerprint := "16051247237858677610")
*Theorems: the first pass, at any depth.* Let $`d` be a dialect with a
text. For every list of blocks as read, the first pass over blocks adds
it, against the second pass over blocks, with the definitions of the
decoded blocks in the order of the first pass; and so for every list of
ops as read, and every list of regions as read. They are proved together,
by recursion on the tree: each applies the theorems of the previous block
to the parts that it holds.
:::
