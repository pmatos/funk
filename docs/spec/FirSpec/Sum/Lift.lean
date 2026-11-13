import VersoManual
import Fir.Sum.Lift
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on lifting an extension, which renders
`Fir.Sum.Lift` (ADR-2026-11-05-2012). Each block explains declarations of
that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Lifting an extension: readable blocks" =>

:::moduleDocs (fingerprint := "14235670759959532070")
:::

:::readable Fir.Dialect.lift Fir.Dialect.lift.instDialectName Fir.Dialect.lift.instTyDenote Fir.Dialect.lift.instTyPoison Fir.Dialect.lift.instTyRefinement Fir.Dialect.lift.instDecidableEqOp Fir.Dialect.lift.instDecidableEqTy (fingerprint := "11332194699468969674")
*Definition: the lift of an extension.* Let $`e` be an extension written
over $`d`, the dialects it depends on, $`\iota` an inclusion of $`d`'s
types in those of a larger base $`B`, and $`\mu` a _memory map_, which
gives each memory of $`d` its name in $`B`. The lift $`e{\uparrow}_\iota`
has the ops of $`e` and the own types of $`e`, and $`e`'s name. Its own
types mean, are poison and refine as $`e`'s do, and its ops and types
compare as $`e`'s.

The lift names $`d`, $`\iota` and $`\mu`, so the classes below find them,
and $`B \boxplus e{\uparrow}_\iota` is a sum like any other.
:::

:::readable Fir.Dialect.lift.incl (fingerprint := "9817543705762984987")
*Definition: the types of the lift.* The types of $`e` over $`d`,
$`\mathrm{Ty}_d \uplus \mathrm{Ty}_e`, are included in those of the lift over
$`B`, $`\mathrm{Ty}_B \uplus \mathrm{Ty}_e`, by $`\iota` over $`e`'s own
types. This inclusion is written $`\hat\iota` below.
:::

:::readable Fir.Dialect.lift.projFuncType Fir.Dialect.lift.projContext Fir.Dialect.lift.projView (fingerprint := "5791310562306388736")
*Definition: the context that the lift sees.* A function type of the lift
is one of $`e` over $`d` when all its types project by $`\hat\iota`. The
lift sees the symbols whose types project, and no other. It sees the op
context $`C` only when the result types of $`C` project:

$$`\mathrm{proj}(C) = (\mathrm{symtab}_C|_{d,e},\ \hat\iota^{-1}(r^*)) \quad\text{when every } r \in \mathrm{results}_C \text{ projects}`

and has no context otherwise. Its view of a host keeps the host's ops that
are $`e`'s, and the host's types that project.
:::

:::readable Fir.Dialect.lift.ValidOp Fir.Dialect.lift.instDecidableValidOp (fingerprint := "5179808654070511145")
*Definition: an op of the lift in a context.* An op $`q` of $`e` obeys its
rule in the context $`C` of the lift when the lift can see $`C` and $`q`
obeys $`e`'s rule there:

$$`\frac{\mathrm{proj}(C) = C' \qquad C' \vdash_{d.\mathrm{over}(e)} q~\text{valid}}{C \vdash_{B.\mathrm{over}(e\uparrow_\iota)} q~\text{valid}}`

This is the rule for a base op in a sum (ADR-2026-11-09-2353), with $`e` in
place of the base. It can be decided when $`e`'s rule can.
:::

:::readable Fir.Dialect.lift.instDialectSignature Fir.Dialect.lift.instDialectValidation Fir.Dialect.lift.instDecidableDialectValidation (fingerprint := "12639027576233195331")
*Definition: the signature and the rules of the lift.* An op of the lift
has $`e`'s signature, with its types included by $`\hat\iota`:

$$`\mathrm{sig}(q) = \hat\iota(t)^* \text{ where } \mathrm{sig}_{d.\mathrm{over}(e)}(q) = t^*`

and the same for its result types; it ends a block, has successors and
owns regions of kinds as in $`e`. A type of $`B` is valid, and names a
memory, as $`B` says, and an own type of $`e` as $`e` says. An op refers to the symbols that $`e`
says, and obeys its rule as above. A function obeys $`e`'s function rule
through the lift's view. The lift registers $`e`'s region kinds, and a
region of one of them obeys $`e`'s rule for it through the lift's view;
so do $`e`'s kinds of item and an item of one of them.
Each rule can be decided when $`B`'s and $`e`'s can.
:::

:::readable Fir.Dialect.lift.liftMem Fir.Dialect.lift.liftMem_ofBase Fir.Dialect.lift.instDialectEffects Fir.Dialect.lift.instDialectMemOver (fingerprint := "9787371898634028682")
*Definition: the memories of the lift.* The memories of the lift over
$`B` are $`B`'s and $`e`'s own, $`M_B + O_e`. The lift's memory map sends
$`e`'s name for a memory $`x` of $`d` to $`\mu(x)`, and keeps $`e`'s own:

$$`\hat\mu(n) = \begin{cases} \mathsf{inl}\ \mu(x) & \text{if } \mathrm{split}(n) = \mathsf{inl}\ x \\ \mathsf{inr}\ o & \text{if } \mathrm{split}(n) = \mathsf{inr}\ o \end{cases}`

So $`\hat\mu(\mathrm{ofBase}(x)) = \mathsf{inl}\ \mu(x)`: the lift names
each memory of $`d` as $`B` does, and the memory has one name in
$`B \boxplus e{\uparrow}_\iota` (ADR-2026-11-09-2306). An op of the lift has
$`e`'s
{ref "The-fir-specification--Execution--Effect-sets"}[poison class and effects],
with its memories renamed by $`\hat\mu`.
:::

:::readable Fir.Dialect.lift.instDialectCall Fir.Dialect.lift.instDialectDenote (fingerprint := "14255937332289603584")
*Definition: how an op of the lift runs.* An op of the lift calls what it
calls in $`e`. It runs by $`e`'s rule on its
operands moved down across $`\hat\iota`, and its results move up:

$$`[\![q]\!](v^*) = \uparrow_{\hat\iota} [\![q]\!]_{d.\mathrm{over}(e)}(\downarrow_{\hat\iota} v^*)`

A terminator's exit is $`e`'s on the operands moved down.
:::

:::readable Fir.Dialect.lift.decodeOp Fir.Dialect.lift.tyAttr Fir.Dialect.lift.decodeTy Fir.Dialect.lift.instDialectText (fingerprint := "18348881999016279676")
*Definition: the text of the lift.* The lift writes each op as $`e` does.
It writes a type of $`B` as $`B` does, and an own type of $`e` as $`e`
does. It reads an op by projecting its operand and result types by
$`\hat\iota`, and reading it with $`e`. It reads a type $`a` with
$`\mathrm{dialect}(\mathrm{head}(a)) = n_e` with $`e`, which must read one
of its own types, and every other type with $`B`.
:::
