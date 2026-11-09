import VersoManual
import Fir.Text.DecodeScope
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the decoding step, which renders
`Fir.Text.DecodeScope` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The decoding step: readable blocks" =>

:::moduleDocs (fingerprint := "6171007526611993748")
:::

:::readable Fir.Block.scopeDefs Fir.Operation.scopeDefs Fir.Region.scopeDefs (fingerprint := "14018173596716500762")
*Definitions: the definitions of blocks, ops and regions, in the order of
the first pass.* The
{ref "The-fir-specification--Text-format--Decoding"}[first pass] of
decoding reads definitions in the order of the text:

* for blocks, at any depth: the arguments of the first block, then the
  definitions of its ops, then those of the other blocks;
* for ops, at any depth: the results of the first op, then the definitions
  of the blocks of its regions, then those of the other ops;
* for regions: the definitions of the blocks of the first region, then
  those of the other regions.
:::

:::readable Fir.Block.scopeDefs_perm Fir.Operation.scopeDefs_perm Fir.Region.scopeDefs_perm Fir.Func.scopeDefs_perm (pin := Fir.Block.defs) (pin := Fir.Func.defs) (pin := Fir.Block.allBlocks) (pin := Fir.Operation.regionBlocks) (pin := Fir.Region.allBlocks) (fingerprint := "7002586193701472433")
*Theorems: the first pass reads the same definitions, in another order.*
For every dialect, each of these lists is a permutation of the other:

* the definitions of blocks in the order of the first pass, and the
  {ref "The-fir-specification--Validation--Scope-and-symbols"}[definitions]
  of each of those blocks and of the blocks of their ops' regions, at any
  depth, block by block;
* the definitions of ops in the order of the first pass, and the results
  of each op followed by the definitions of each block of their regions,
  at any depth;
* the definitions of regions in the order of the first pass, and the
  definitions of each of their blocks, at any depth;
* for a function $`f`, its parameters followed by the definitions of its
  blocks in the order of the first pass, and $`\mathrm{defs}(f)`, every
  value $`f` defines.

A block's definitions list its arguments and all its ops' results before
the blocks of their regions, and the first pass does not, so the lists
differ only in order. Validation and well-formedness speak of
$`\mathrm{defs}(f)`, so the order must be set aside.
:::

:::readable Fir.find?_fst_eq_some (fingerprint := "4294853859230067027")
*Theorem: with distinct names, a value has the type of its one
definition.* For every dialect and every list $`L` of values with their
types whose names are distinct, the first entry of $`L` for the name $`x`
has the type $`t` exactly when $`(x, t)` is in $`L`. It lets the proofs
replace the
{ref "The-fir-specification--Validation--Scope-and-symbols"}[type of a value in a function],
found by its first definition, by membership in the function's
definitions.
:::

:::readable Fir.Text.Scope.Holds (pin := Fir.Text.Scope) (fingerprint := "12507313161501620523")
*Definition: a scope that holds a list.* A
{ref "The-fir-specification--Text-format--Decoding"}[scope] $`\mathit{sc}`,
a table from names to types, _holds_ a list $`L` of values with their types
when it gives a value $`x` the type $`t` exactly when $`(x, t)` is in $`L`:

$$`\begin{aligned} & \mathrm{holds}(\mathit{sc}, L) \iff \\ & \quad \forall\, x, t.\ \bigl(\mathit{sc}(x) = t \iff (x, t) \in L\bigr) \end{aligned}`

So it gives each value of $`L` its type, and no other value a type.
:::

:::readable Fir.Text.Scope.holds_empty Fir.Text.Scope.Holds.contains_eq_false Fir.Text.Scope.Holds.insert (fingerprint := "2774064879980165188")
*Theorems: the empty scope, and adding a value.* For every dialect:

* the empty scope holds the empty list;
* a scope that holds $`L` does not contain a name that $`L` does not name;
* if a scope holds $`L`, and $`L` does not name $`x`, then the scope with
  $`x` added with the type $`t` holds $`L` followed by $`(x, t)`.

The first pass starts from the empty scope and adds one value at a time.
:::

:::readable Fir.Text.nodup_fst_left (fingerprint := "12412065735934775316")
*Lemma: proof plumbing.* If the names of $`L` followed by $`M` are
distinct, so are the names of $`L`.
:::

:::readable Fir.Text.decodeDef_eq Fir.Text.mapM_decodeDef (pin := Fir.Text.decodeDef) (pin := Fir.Text.decodeType) (fingerprint := "6210408333815912073")
*Theorems: definitions decode back.* For every dialect with a
{ref "The-fir-specification--Text-format--Grammar"}[text format]:

* a definition as written that
  {ref "The-fir-specification--Text-format--The-tree-that-the-grammar-reads"}[erases]
  to the tree of $`x : T` decodes as $`x : T`, when
  $`\mathrm{decodety}(\mathrm{tyattr}(T)) = T`;
* definitions as written that erase to the trees of $`x_1 : T_1, \dots,
  x_n : T_n` decode, one after the other, as those definitions, when
  $`\mathrm{decodety}(\mathrm{tyattr}(T_i)) = T_i` for each $`i`.

Here $`\mathrm{decodety}` is the dialect's reader of types. The position of
a definition matters only to an error, and there is none.
:::

:::readable Fir.Text.Defines (pin := Fir.Text.Scope) (fingerprint := "10896383341858368157")
*Definition: a pass adds definitions.* Let $`\mathit{define}` be a pass,
which adds to a scope what it reads from some part of a tree, or fails,
and let $`\tau` be a part without positions and $`y^*` a list of
values with their types. The pass _adds_ $`y^*` for $`\tau`
when, for every part $`a` that erases to $`\tau` and every scope
$`\mathit{sc}` that holds a list $`L`, if the names of $`L` followed by
$`y^*` are distinct, then the pass on $`\mathit{sc}` and $`a` succeeds with
a scope that holds $`L` followed by $`y^*`.

The condition on names is what keeps the pass from finding a value twice;
a well-formed function meets it.
:::

:::readable Fir.Text.define_defines (pin := Fir.Text.define) (fingerprint := "2850858440387593569")
*Theorem: adding definitions as written adds them.* For every dialect with a text
format and every list of definitions $`y_1 : T_1, \dots, y_n : T_n` such
that $`\mathrm{decodety}(\mathrm{tyattr}(T_i)) = T_i` for each $`i`, the
reader that adds definitions to a scope adds $`y_1 : T_1, \dots, y_n : T_n`
for their trees, in order.
:::

:::readable Fir.Text.defineBlocks_nil Fir.Text.defineBlocks_cons Fir.Text.defineOps_nil Fir.Text.defineOps_cons Fir.Text.defineRegions_nil Fir.Text.defineRegions_cons (pin := Fir.Text.defineBlocks) (pin := Fir.Text.defineOps) (pin := Fir.Text.defineRegions) (fingerprint := "7987321205122702915")
*Theorems: the first pass adds definitions, one element at a time.* For
every dialect with a text format, the first pass on blocks, on ops and on
regions adds, for their trees, their definitions in the order of the first
pass:

* for no blocks, no ops or no regions: it adds nothing;
* for a block followed by blocks $`b^*`: it adds them when the types of the
  block's arguments decode back to themselves, the pass on ops adds those
  of the block's ops, and the pass on blocks adds those of $`b^*`;
* for an op followed by ops $`o^*`: it adds them when the types of the op's
  results decode back to themselves, the pass on regions adds those of the
  op's regions, and the pass on ops adds those of $`o^*`;
* for a region followed by regions $`r^*`: it adds them when the pass on
  blocks adds those of the region's blocks, and the pass on regions adds
  those of $`r^*`.

Here a type $`T` _decodes back to itself_ when
$`\mathrm{decodety}(\mathrm{tyattr}(T)) = T`.
:::

:::readable Fir.Block.defines Fir.Operation.defines Fir.Region.defines (fingerprint := "6274973033964153100")
*Theorems: the first pass adds every definition, at any depth.* For every
dialect with a text format, the first pass on blocks adds, for their trees,
their definitions in the order of the first pass, when the type of each of
those definitions decodes back to itself; and so do the first pass on ops
and the first pass on regions. The three are proved together, by recursion
on the blocks, ops and regions, from the lemmas above.
:::

:::readable Fir.Func.WellFormed.decodeTy_def (pin := Fir.Func.WellFormed) (pin := Fir.Func.defs) (pin := Fir.Func.types) (fingerprint := "10409820501084467350")
*Theorem: every type that a well-formed function defines decodes back.* For
every dialect with signatures and a text format, every
{ref "The-fir-specification--Text-format--Round-trips"}[well-formed]
function $`f`, and every value $`y : T` of $`\mathrm{defs}(f)`, that is,
every value that $`f` defines at any depth with its type:
$`\mathrm{decodety}(\mathrm{tyattr}(T)) = T`.
:::

:::readable Fir.Func.WellFormed.scope (pin := Fir.Func.typeOf) (pin := Fir.Func.WellFormed) (pin := Fir.Text.define) (pin := Fir.Text.defineBlocks) (fingerprint := "4990254789688537331")
*Theorem: the first pass on a well-formed function gives each value its
type.* For every dialect with
signatures and a text format, every well-formed function $`f`, parameters
as written that erase to the trees of the parameters of $`f`, and blocks as
written that erase to the trees of the blocks of $`f`: adding the
parameters to the empty scope succeeds with a scope $`\mathit{sc}_1`,
adding the definitions of the blocks to $`\mathit{sc}_1` succeeds with a
scope $`\mathit{sc}`, and $`\mathit{sc}` gives each name $`x` the type
$`\mathrm{type}_f(x)`, and no type when $`f` does not define $`x`.

Here $`\mathrm{type}_f(x)` is the type of the
{ref "The-fir-specification--Validation--Scope-and-symbols"}[first definition]
of $`x` in $`f`. A well-formed function names each value once, so the
pass finds no value twice, and the order of the first pass does not
matter.
:::
