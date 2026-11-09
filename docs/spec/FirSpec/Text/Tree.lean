import VersoManual
import Fir.Text.Tree
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the tree that the grammar reads,
which renders `Fir.Text.Tree` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The tree that the grammar reads: readable blocks" =>

:::moduleDocs (fingerprint := "3888398671219957908")
:::

:::readable Fir.TextPos.zero (pin := Fir.TextPos) (fingerprint := "10810081565763310123")
*Definition: the empty position.* $`p_0` is the
{ref "The-fir-specification--Text-format--Round-trips"}[position] at line 0,
column 0. No token of a text stands there, since lines and columns count
from 1. A module has no text, so its tree puts $`p_0` at every position.
:::

:::readable Fir.Text.SDef.erase Fir.Text.eraseAt (pin := Fir.Text.SDef) (fingerprint := "6228989577258180851")
*Definitions: a definition, and a part with its position, without
positions.* A
{ref "The-fir-specification--Text-format--Reading-the-grammar"}[definition as written]
keeps its value's name and its type, and both its positions become $`p_0`:

$$`\begin{aligned} & \mathrm{erase}(\{\mathsf{name}~x,~\mathsf{pos}~p,~\mathsf{ty}~a,~\mathsf{ty\_pos}~q\}) \\ & \quad = \{\mathsf{name}~x,~\mathsf{pos}~p_0,~\mathsf{ty}~a,~\mathsf{ty\_pos}~p_0\} \end{aligned}`

A part $`v` written at a position $`p`, such as an operand or a result
type, keeps $`v` and moves to $`p_0`: $`\mathrm{erase}(v, p) = (v, p_0)`.
:::

:::readable Fir.Text.SOp.erase Fir.Text.SRegion.eraseList Fir.Text.SBlock.eraseList Fir.Text.SOp.eraseList (pin := Fir.Text.SOp) (pin := Fir.Text.SBlock) (pin := Fir.Text.SRegion) (fingerprint := "6142680531305349951")
*Definitions: ops, regions and blocks without positions, at any depth.*
$`\mathrm{erase}` of an
{ref "The-fir-specification--Text-format--Reading-the-grammar"}[op as written]
erases its results and puts its name at $`p_0` and each operand at
$`p_0`. It keeps the op's name, attributes, successors and location
reference, and erases its regions. Erasing a region erases its blocks, and
erasing a block keeps its label and erases its arguments and its ops. A
list is erased element by element. The four definitions call one another,
as an op may hold regions.
:::

:::readable Fir.Text.SItem.erase Fir.Text.SBody.erase Fir.Text.SItem.eraseList (pin := Fir.Text.SItem) (pin := Fir.Text.SBody) (fingerprint := "9664042224910379088")
*Definitions: items and their bodies without positions, at any depth.*
$`\mathrm{erase}` of an
{ref "The-fir-specification--Text-format--Reading-the-grammar"}[item as written]
keeps its kind and its symbol, puts its kind at $`p_0`, erases its
parameters, and puts each result type and each attribute at $`p_0`. A body
of blocks erases its blocks, and a body of items erases its items.
:::

:::readable Fir.Text.SModule.erase (pin := Fir.Text.SModule) (fingerprint := "15885566561963633564")
*Definition: a module as written, without positions.* $`\mathrm{erase}` of
a module as written erases each of its items and keeps its location table,
which holds no position.

A tree $`s` _erases to_ a tree $`t` when $`\mathrm{erase}(s) = t`: the
two differ at most in their positions.
:::

:::readable Fir.Text.SOp.eraseList_eq_map Fir.Text.SItem.eraseList_eq_map (fingerprint := "2025288017054542167")
*Lemmas: proof plumbing.* Erasing a list of ops, or of items, element by
element is mapping $`\mathrm{erase}` over it. The proofs rewrite with them.
:::

:::readable Fir.defTree (pin := Fir.DialectText) (fingerprint := "15963093472231929533")
*Definition: the tree of a definition.* For every dialect with a
{ref "The-fir-specification--Text-format--Grammar"}[text format], which
writes each type $`T` as the attribute $`\mathrm{tyattr}(T)`, the tree of a
definition $`x : T` is

$$`\begin{aligned} & \mathrm{tree}(x : T) = \{\mathsf{name}~x,~\mathsf{pos}~p_0, \\ & \quad \mathsf{ty}~\mathrm{tyattr}(T),~\mathsf{ty\_pos}~p_0\} \end{aligned}`
:::

:::readable Fir.Operation.tree Fir.Region.treeList Fir.Block.treeList Fir.Operation.treeList (pin := Fir.Operation) (pin := Fir.Block) (pin := Fir.Region) (pin := Fir.DialectText) (fingerprint := "8847471298669668753")
*Definitions: the trees of ops, regions and blocks.* The tree of an
{ref "The-fir-specification--Abstract-syntax--Modules___-functions___-blocks-and-ops"}[op]
with the op instance $`\iota` holds:

* the trees of its results;
* its name $`\mathrm{opname}(\iota)` and its attributes
  $`\mathrm{opattrs}(\iota)`, as the dialect writes them, with the name at
  $`p_0`;
* each operand at $`p_0`;
* its successors, the trees of its regions, and its location reference.

The tree of a region is the trees of its blocks, and the tree of a block
holds its label, the trees of its arguments and the trees of its ops. The
tree of a list is the tree of each element.
:::

:::readable Fir.Func.tree Fir.Item.tree (pin := Fir.Func) (pin := Fir.Item) (pin := Fir.DialectText) (fingerprint := "17692060576293912157")
*Definitions: the tree of a function, and of an item.* The tree of a
function $`f` is the item of kind `func`, at $`p_0`, with:

* the symbol of $`f` and the trees of its parameters;
* each result type $`t` as $`\mathrm{tyattr}(t)` at $`p_0`;
* no attributes;
* as its body, the trees of the blocks of $`f`: a body of blocks, even
  when $`f` has none.

The tree of an item is the tree of its function, since every item of M0 is
a function.
:::

:::readable Fir.Module.tree (pin := Fir.Module) (fingerprint := "15411300045204652981")
*Definition: the tree of a module.* The tree of a module $`m`,
$`\mathrm{tree}(m)`, holds the trees of its items, in order, and its
location table.

It is what the grammar would read from the text of $`m` if the text had
no positions. The
{ref "The-fir-specification--Text-format--The-module-read-back"}[grammar step]
shows that reading the printed text gives a tree that erases to
$`\mathrm{tree}(m)`, and the
{ref "The-fir-specification--Text-format--The-module-decoded-back"}[decoding step]
that decoding such a tree gives $`m` back.
:::

:::readable Fir.Operation.treeList_eq_map (fingerprint := "194155182859344640")
*Lemma: proof plumbing.* The trees of a list of ops are the tree of each
op, mapped over the list.
:::

:::readable Fir.SDef.erase_eq_defTree (fingerprint := "9965501536329559617")
*Theorem: a definition erases to the tree of $`x : T` exactly when it
names $`x` and writes $`T`.* For every
dialect with a text format, a definition as written erases to the tree of
the definition $`x : T` exactly when its value's name is $`x` and its type
as written is $`\mathrm{tyattr}(T)`.
:::

:::readable Fir.SOp.erase_eq_tree (fingerprint := "8455489951576911098")
*Theorem: what an op that erases to an op's tree holds.* For every dialect
with a text format, if an op as written $`s` erases to the tree of an op
$`o` with the op instance $`\iota`, then:

* the results of $`s` erase to the trees of the results of $`o`;
* the name of $`s` is $`\mathrm{opname}(\iota)`, and its attributes are
  $`\mathrm{opattrs}(\iota)`;
* the names of the operands of $`s`, without their positions, are the
  operands of $`o`;
* the successors of $`s` are those of $`o`;
* the regions of $`s` erase to the trees of the regions of $`o`;
* the location reference of $`s` is that of $`o`.

The decoding step reads each part of the op off these equations.
:::

:::readable Fir.SOp.eraseList_eq_nil Fir.SOp.eraseList_eq_cons Fir.SBlock.eraseList_eq_nil Fir.SBlock.eraseList_eq_cons Fir.SRegion.eraseList_eq_nil Fir.SRegion.eraseList_eq_cons (fingerprint := "17433017824174039419")
*Theorems: lists that erase to the trees of lists.* For every dialect with
a text format:

* the only list of ops as written that erases to the trees of no ops is
  the empty list, and the same holds for blocks and for regions;
* a list of ops as written that erases to the trees of $`o` followed by
  $`o^*` is an op that erases to the tree of $`o`, followed by ops that
  erase to the trees of $`o^*`;
* a list of blocks as written that erases to the trees of a block $`b`
  followed by $`b^*` is a block with the label of $`b`, whose arguments
  and ops erase to the trees of those of $`b`, followed by blocks that
  erase to the trees of $`b^*`;
* a list of regions as written that erases to the trees of a region $`r`
  followed by $`r^*` is a region whose blocks erase to the trees of the
  blocks of $`r`, followed by regions that erase to the trees of $`r^*`.

The decoding step goes down a tree with them, one element at a time.
:::

:::readable Fir.SItem.erase_eq_funcTree (fingerprint := "11907866414717876360")
*Theorem: what an item that erases to a function's tree holds.* For every
dialect with a text format, if an item as written $`s` erases to the tree
of a function $`f`, then:

* the kind of $`s` is `func`, and its symbol is that of $`f`;
* its parameters erase to the trees of the parameters of $`f`;
* its result types, without their positions, are $`\mathrm{tyattr}(t)`
  for each result type $`t` of $`f`;
* it has no attributes;
* its body is a body of blocks, which erase to the trees of the blocks of
  $`f`.
:::

:::readable Fir.SModule.erase_eq_tree (fingerprint := "3050767672788089428")
*Theorem: what a module that erases to a module's tree holds.* For every
dialect with a text format, if a module as written $`s` erases to the tree
of a module $`m`, then the items of $`s` erase to the trees of the items
of $`m`, and the location table of $`s` is that of $`m`.
:::
