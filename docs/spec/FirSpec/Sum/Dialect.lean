import VersoManual
import Fir.Sum.Dialect
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on sums of dialects, which renders
`Fir.Sum.Dialect` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "The sum of dialects: readable blocks" =>

:::moduleDocs (fingerprint := "17623863330440996922")
:::

:::readable Fir.Dialect.over Fir.Dialect.sum (fingerprint := "6781788953757055949")
*Definition: an extension over a base, and their sum.* Let $`b` be a
dialect, the _base_, and $`e` a dialect with ops $`\mathrm{Op}_e` and types
of its own $`\mathrm{Ty}_e`. The dialect $`e` _over_ $`b` has the ops of
$`e` and the types of both:

$$`b.\mathrm{over}(e) = (\mathrm{Op}_e,\ \mathrm{Ty}_b \uplus \mathrm{Ty}_e)`

The _sum_ $`b \boxplus e` has the ops of both and the types of both:

$$`b \boxplus e = (\mathrm{Op}_b \uplus \mathrm{Op}_e,\ \mathrm{Ty}_b \uplus \mathrm{Ty}_e)`

Here $`A \uplus B` is the disjoint union: an element of $`A`, tagged
$`\mathsf{inl}`, or one of $`B`, tagged $`\mathsf{inr}`. The extension
states each class of a dialect for $`b.\mathrm{over}(e)`, so its ops can
take and give values of the base's types. The sum is left-nested:
$`b \boxplus e_1 \boxplus e_2` adds $`e_2` to $`b \boxplus e_1`.
:::

:::readable Fir.instTyDenoteEmpty Fir.instTyPoisonEmpty Fir.instTyRefinementEmpty (fingerprint := "4013406741606831454")
*Definition: no types of its own.* A dialect with no types of its own takes
the empty type set. It has no values, so none is poison and none refines
another.
:::

:::readable Fir.instTyDenoteSum Fir.instTyPoisonSum Fir.instTyRefinementSum Fir.instTyDenoteSumTy Fir.instTyPoisonSumTy Fir.instTyRefinementSumTy (fingerprint := "10356629448207356528")
*Definition: the values of summed types.* A summed type denotes what it
denotes on its own side, and its values are poison, and refine one
another, as on that side:

$$`[\![\mathsf{inl}\ t]\!] = [\![t]\!] \qquad [\![\mathsf{inr}\ t]\!] = [\![t]\!]`

The types of a sum are summed types.
:::

:::readable Fir.instDecidableEqSumOp Fir.instDecidableEqSumTy (fingerprint := "6348055299131146135")
*Definition: comparing ops and types of a sum.* Two ops, or two types, of a
sum are equal when they are on the same side and equal there. So the
validation check, which compares types, works on a sum when it works on
each side.
:::

:::readable Fir.HVector.toSum Fir.HVector.ofSum (fingerprint := "1822864197566416814")
*Definition: values of the base in the sum.* A value of the base's type
$`t` is a value of the sum's type $`\mathsf{inl}\ t`, and the other way
round. $`\uparrow` moves a vector of values of the base's types $`t^*` to
the sum's types $`(\mathsf{inl}\ t)^*`, and $`\downarrow` moves it back.
:::

:::readable Fir.Dialect.sum.baseFuncType Fir.Dialect.sum.baseSymbols Fir.Dialect.sum.baseContext Fir.Dialect.sum.extContext (fingerprint := "6738591554538404080")
*Definition: the context that each side sees.* A function type of the sum
is a function type of the base when all its types are the base's. The base
sees the symbols whose types it can write, and no other. It sees the op
context $`C` of the sum only when it can write the result types of $`C`:

$$`\mathrm{base}(C) = (\mathrm{symtab}_C|_b,\ r^*) \quad\text{when } \mathrm{results}_C = (\mathsf{inl}\ r)^*`

and has no context otherwise. The extension $`e` sees all of $`C`, since
its types are the sum's.
:::

:::readable Fir.Dialect.sum.baseView Fir.Dialect.sum.extView (fingerprint := "1151120134815078247")
*Definition: each side's view of a function.* A function rule sees a
function of a host dialect through a
{ref "The-fir-specification--Validation--Scope-and-symbols"}[view]. The
base's view of a host that holds the sum keeps the sum's view of the
host's ops and types that are the base's. The extension's view keeps the
host's ops that are $`e`'s, and every type of the sum.
:::

:::readable Fir.Dialect.sum.BaseValidOp Fir.Dialect.sum.instDecidableBaseValidOp (fingerprint := "2778241861756789920")
*Definition: a base op in a context of the sum.* An op $`p` of the base
obeys its rule in the op context $`C` of the sum when the base can see
$`C` and $`p` obeys the base's rule there:

$$`\frac{\mathrm{base}(C) = C' \qquad C' \vdash_b p~\text{valid}}{C \vdash_{b \boxplus e} \mathsf{inl}\ p~\text{valid}}`

So no base op is valid in a function whose result types the base cannot
write. A base op there could not be judged: the base's $`\mathsf{ret}`
must return the function's result types, and the base has no word for
the extension's (ADR-2026-11-09-2353). This can be decided when the base's
rule can.
:::

:::readable Fir.Dialect.sum.ValidRegion (fingerprint := "7317452533583571498")
*Definition: the rule of a region kind in a sum.* A region of the kind
$`k` obeys, in the sum, the base's rule for $`k`, through the base's view,
when the base registers $`k`; and otherwise $`e`'s rule for $`k`, through
$`e`'s view:

$$`\vdash_{b \boxplus e} r : k~\text{valid} \iff \begin{cases} \vdash_b r : k~\text{valid by the base's view} & k \in \mathrm{kinds}_b \\ \vdash_{b.\mathrm{over}(e)} r : k~\text{valid by } e\text{'s view} & \text{otherwise} \end{cases}`

The laws of names say that $`e` registers only words of its own name, and
the base only words of its own set, which does not hold $`e`'s name, so
each kind goes to the dialect that registers it.
:::

:::readable Fir.Dialect.sum.ValidItem (fingerprint := "10283173853771968966")
*Definition: the rule for items in a sum.* An item $`i` of a dialect's
kind $`k` obeys, in the sum, the base's rule, through the base's view, when
the base registers $`k`; and otherwise $`e`'s rule, through $`e`'s view:

$$`\vdash_{b \boxplus e} i~\text{valid} \iff \begin{cases} \vdash_b i~\text{valid by the base's view} & k \in \mathrm{itemkinds}_b \\ \vdash_{b.\mathrm{over}(e)} i~\text{valid by } e\text{'s view} & \text{otherwise} \end{cases}`

As for region kinds, the laws of names send each kind of item to the
dialect that registers it.
:::

:::readable Fir.Dialect.sum.instDialectSignature Fir.Dialect.sum.instDialectValidation Fir.Dialect.sum.instDecidableDialectValidation (fingerprint := "1536494424229976565")
*Definition: the signature and the rules of a sum.* An op of the sum has
the signature of its side. A base op's types are the base's, tagged
$`\mathsf{inl}`:

$$`\mathrm{sig}(\mathsf{inl}\ p) = (\mathsf{inl}\ t)^* \text{ where } \mathrm{sig}_b(p) = t^* \qquad \mathrm{sig}(\mathsf{inr}\ q) = \mathrm{sig}_{b.\mathrm{over}(e)}(q)`

and the same for its result types, whether it ends a block, its number
of successors and the kinds of its regions. A type of the sum is valid as
its side says, an op refers
to the symbols that its side says, and obeys its side's rule as above. A
function of the sum obeys the function rule of each side, each through its
own view:

$$`\frac{\vdash_b f~\text{valid by the base's view} \qquad \vdash_{b.\mathrm{over}(e)} f~\text{valid by } e\text{'s view}}{\vdash_{b \boxplus e} f~\text{valid}}`

The sum registers the region kinds of the base, then those of $`e`, and a
region obeys the rule of its kind in the sum, as above. In the same way,
the sum registers the kinds of item of the base, then those of $`e`; an
item of a kind that the base registers obeys the base's rule through the
base's view, and any other obeys $`e`'s rule through $`e`'s view. Each rule
of the sum can be decided when each side's can.
:::

:::readable Fir.DialectMemOver Fir.DialectMemOver.ofBase (fingerprint := "16129074969842651274")
*Definition: the memories of an extension.* The memory names $`M_e` of
$`e` over the base are the base's memory names $`M_b` and $`e`'s own
$`O_e`, as its types are the base's and its own: a map
$`\mathrm{split} : M_e \to M_b + O_e` and its inverse $`\mathrm{join}`.
$`e` names the base's memory $`x` as
$`\mathrm{ofBase}(x) = \mathrm{join}(\mathsf{inl}\ x)`.
:::

:::readable Fir.Dialect.sum.instDialectEffects Fir.Dialect.sum.instDialectCall Fir.Dialect.sum.instDialectDenote (pin := Fir.Effects.map) (fingerprint := "5103561852968972671")
*Definition: how an op of a sum runs.* The memories of the sum are
$`e`'s, $`M_e`, which name the base's: so a memory has one name in the
sum, whichever side names it (ADR-2026-11-09-2306). An op of the sum has
its side's
{ref "The-fir-specification--Execution--Effect-sets"}[poison class and effects],
a base op's with its memories renamed by $`\mathrm{ofBase}`:

$$`\mathrm{eff}(\mathsf{inl}\ p) = \mathrm{ofBase}(\mathrm{eff}_b(p)) \qquad \mathrm{eff}(\mathsf{inr}\ q) = \mathrm{eff}_{b.\mathrm{over}(e)}(q)`

It calls the function that it calls on its side. It runs by its side's
rule: a base op takes its operands moved down to the base's types, and its
results are moved up to the sum's.

$$`[\![\mathsf{inl}\ p]\!](v^*) = \uparrow [\![p]\!]_b(\downarrow v^*) \qquad [\![\mathsf{inr}\ q]\!](v^*) = [\![q]\!]_{b.\mathrm{over}(e)}(v^*)`

A terminator's exit is its side's, in the same way.
:::

:::readable Fir.Dialect.sum.decodeOp Fir.Dialect.sum.decodeTy Fir.Dialect.sum.instDialectText (fingerprint := "930447549735669784")
*Definition: the text of a sum.* The sum writes each op and each type as
its side writes it. It reads a word back by the dialect that the word
names. Let $`n_e` be $`e`'s name.

* An op named $`n` with $`\mathrm{dialect}(n) = n_e` is read by $`e` over
  the base. Every other op is read by the base, at its operand and result
  types, which must all be the base's.
* A type $`a` with $`\mathrm{dialect}(\mathrm{head}(a)) = n_e` is read by
  $`e`, and must be one of $`e`'s own types. Every other type is read by
  the base.

So the base never sees a word of $`e`, and $`e` reads its own words. An
op's attributes go with the op to the side that its name picks.
:::

:::readable Fir.Dialect.sum.instDialectSet (fingerprint := "3705957954386165517")
*Definition: the dialect set of a sum.* The set of $`b \boxplus e` is the
base's set, then $`e`'s name:

$$`\mathrm{names}(b \boxplus e) = \mathrm{names}(b) \cdot n_e`

So the set of $`\mathrm{core} \boxplus e_1 \boxplus e_2` is
$`n_{e_1} \cdot n_{e_2}`.
:::
