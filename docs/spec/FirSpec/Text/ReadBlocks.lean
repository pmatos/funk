import VersoManual
import Fir.Text.ReadBlocks
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on blocks and regions read back, which
renders `Fir.Text.ReadBlocks` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Blocks and regions read back: readable blocks" =>

:::moduleDocs (fingerprint := "14359386289347756802")
:::

:::readable Fir.head_blocks (pin := Fir.Block.tokensList) (fingerprint := "17423821835765405823")
*Lemma: blocks start with a label.* For every dialect with a
{ref "The-fir-specification--Text-format--Grammar"}[text format], list of
blocks $`b^*`, tokens $`v` and test $`P` on tokens: if $`P` holds of every
label, and of the first token of $`v` if there is one, then $`P` holds of
the first token of the tokens of $`b^*` followed by $`v`, if there is one.
The proofs use it to show that the token after a block's ops ends them.
:::

:::readable Fir.readBlocks_nil_reads Fir.readBlocks_cons_reads (pin := Fir.Text.readBlocks) (pin := Fir.Block.tokensList) (fingerprint := "2349298822128858794")
*Theorems: blocks read back, one at a time.* For every dialect with a text
format, the reader of blocks
{ref "The-fir-specification--Text-format--The-grammar-step"}[reads] tokens
of blocks as their trees before `}`, up to positions:

* for no blocks: it reads nothing;
* for a block with the label $`\ell`, the arguments $`x_i : T_i` and the
  ops $`o^*`, followed by blocks $`b^*`: it reads them when each
  $`\mathrm{tyattr}(T_i)` is written as a type, the reader of ops reads the tokens of $`o^*` as
  their trees before any token that
  {ref "The-fir-specification--Text-format--Ops-read-back"}[ends a block's ops],
  and the reader of blocks reads the tokens of $`b^*` as their trees before
  `}`.

A block's tokens are the {ref "The-fir-specification--Text-format--The-parser"}[token]
$`\mathsf{label}~\ell`, then its arguments in
parentheses when it has any, then `:`, then its ops. Its ops end at the
label of the next block, or at the `}` after the last.
:::

:::readable Fir.readRegions_nil_reads Fir.readRegions_cons_reads (pin := Fir.Text.readRegions) (pin := Fir.Region.tokensList) (fingerprint := "3564753331505198229")
*Theorems: regions read back, one at a time.* For every dialect with a text
format, the reader of regions reads tokens of regions as their trees before
any location reference, up to positions:

* for no regions: it reads nothing;
* for a region with the blocks $`b^*`, followed by regions $`r^*`: it reads
  them when the reader of blocks reads the tokens of $`b^*` as their trees before `}`,
  and the reader of regions reads the tokens of $`r^*` as their trees
  before any location reference.

A region's tokens are `{`, its blocks, and `}`. The regions of an op end
at its location reference.
:::

:::readable Fir.Block.readsList Fir.Operation.readsList Fir.Operation.readsBody Fir.Region.readsList (pin := Fir.Block.allBlocks) (pin := Fir.Operation.regionBlocks) (pin := Fir.Region.allBlocks) (pin := Fir.Block.defs) (fingerprint := "12896156741841929050")
*Theorems: blocks, ops and regions read back, at any depth.* For every
dialect with a text format, write $`\mathrm{typed}(b)` when
$`\mathrm{tyattr}(T)` is written as a type for each value $`x : T` that the
block $`b` defines, its arguments and its ops' results. Then, up to
positions:

* for blocks $`b^*` such that $`\mathrm{typed}(b)` holds for each block
  $`b` of $`b^*` and of their ops' regions, at any depth, the reader of
  blocks reads the tokens of $`b^*` as their trees before `}`;
* for ops $`o^*` such that the type of each result of each op of $`o^*` is
  written as a type, and $`\mathrm{typed}(b)` holds for each block $`b`
  of their regions, at any depth, the reader of ops reads the tokens of
  $`o^*` as their trees before any token that ends a block's ops;
* for an op $`o` such that $`\mathrm{typed}(b)` holds for each block $`b`
  of its regions, at any depth, the reader of the rest of an op reads the
  tokens of $`o` after its name as
  {ref "The-fir-specification--Text-format--Ops-read-back"}[its tree with the results and name already read],
  for all results, names and positions, before any token;
* for regions $`r^*` such that $`\mathrm{typed}(b)` holds for each block
  $`b` of $`r^*`, at any depth, the reader of regions reads the tokens of
  $`r^*` as their trees before any location reference.

The four are proved together, by recursion on the blocks, ops and regions,
since each reader calls the others; each case is one of the lemmas above
and in the previous section.
:::
