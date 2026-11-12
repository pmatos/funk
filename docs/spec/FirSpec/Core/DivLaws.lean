import VersoManual
import Fir.Core.DivLaws
import Fir.Core.Validation
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on division obligations, which renders
`Fir.Core.DivLaws` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Division obligations: readable blocks" =>

:::moduleDocs (fingerprint := "6317374750478558262")
:::

:::readable Fir.Core.divEv_poison (pin := Fir.Core.divEv) (fingerprint := "4996376901287475333")
*Theorem: on a poison operand, a division that gives a result gives
poison.* The four division ops share one
{ref "The-fir-specification--Execution--Division-rules"}[rule]:
$`\mathrm{div}_{s,q}(a, b)` is the way a division of $`a` by $`b` ends,
where $`s` says whether the op reads its operands as signed, and $`q`
gives its result on two values when the divisor is not zero and the
division is not the signed minimum by $`-1`. The rule also takes the op's name, for its UB
reasons.

For every name, $`s` and $`q`, every width $`w`, and all
$`a, b \in \llbracket \mathsf{i}w \rrbracket` of which one is poison: if
$`\mathrm{div}_{s,q}(a, b) = \mathsf{ok}~r`, then $`r = \mathsf{poison}`.
:::

:::readable Fir.Core.divEv_fill (pin := Fir.Core.divEv) (fingerprint := "14536795940362131326")
*Theorem: on a poison operand, a division that is UB is UB with values in
place of each poison.* For every name, $`s` and $`q`, every width $`w`,
and all $`a, b \in \llbracket \mathsf{i}w \rrbracket` of which one is
poison, if $`\mathrm{div}_{s,q}(a, b) = \mathsf{ub}~r`,
there are vectors $`x` and $`y` of $`w` bits such that $`a` is poison or
$`x`, $`b` is poison or $`y`, and $`\mathrm{div}_{s,q}(x, y) = \mathsf{ub}~r'`
for some reason $`r'`.

A poison divisor is UB because it might be zero, so $`y = 0` does it. A
poison dividend is UB only by a divisor that is zero, or $`-1` for a
signed op, and then $`x`, the signed minimum, does it. This is the
{ref "The-fir-specification--Execution--Poison-classes"}[clause]
"UB only by the op's own rules", for the shared rule.
:::

:::readable Fir.Ev.isRefinedBy_refl (pin := Fir.Ev.IsRefinedBy) (fingerprint := "1951273152512717798")
*Theorem: a way to end allows itself, when the relation on results is
reflexive.* A step in the proofs below: for every relation
$`\mathrel{R}` such that $`a \mathrel{R} a` for all $`a`, every way to end
$`e` {ref "The-fir-specification--Execution--Poison-classes"}[allows] $`e`.
:::

:::readable Fir.Core.divEv_isRefinedBy (pin := Fir.Core.divEv) (pin := Fir.Ev.IsRefinedBy) (pin := Fir.PoisonOr.IsRefinedBy) (fingerprint := "3429884219294839487")
*Theorem: refining the operands of a division refines how it ends.* For
every name, $`s` and $`q`, every width $`w`, and all
$`a, b, a', b' \in \llbracket \mathsf{i}w \rrbracket` with
$`a \sqsubseteq a'` and $`b \sqsubseteq b'`, the way
$`\mathrm{div}_{s,q}(a, b)` ends allows the way
$`\mathrm{div}_{s,q}(a', b')` ends: UB allows anything, and a result
allows a result that refines it.

A value is refined only by itself, so only a poison operand can change. A
poison divisor is UB. A poison dividend is UB by a divisor that is zero or,
when signed, $`-1`; by any other divisor it gives poison, and $`a'`,
poison or a value, then gives a result there, never UB. That last case is
the one the
{ref "The-fir-specification--Execution--Semantics-the-obligations-reject"}[rejected rule]
broke.
:::

:::readable Fir.Core.divEv_zero_one Fir.Core.divEv_width_zero (pin := Fir.Core.divEv) (fingerprint := "4448250696595415200")
*Theorem: at a width above zero, $`0` divided by $`1` gives a result.* For
every name, $`s` and $`q`, and every $`w > 0`,
$`\mathrm{div}_{s,q}(0, 1) = \mathsf{ok}~q(0, 1)`.

*Theorem: at width zero, every division by a value is UB.* For every
name, $`s` and $`q`, every $`a \in \llbracket \mathsf{i}0 \rrbracket` and
every vector $`y` of zero bits, $`\mathrm{div}_{s,q}(a, y)` is UB: the only vector of zero bits is
$`0`, so every divisor is zero.
:::

:::readable Fir.Core.ruleOfEv_iff Fir.Core.ruleOfEv_total (pin := Fir.Core.ruleOfEv) (fingerprint := "4510518696897632747")
*Theorem: an op rule made from a way to end ends that way.* A division
ends in one way and never chooses, so its rule is a function $`g` from two
operands to a way to end, and the
{ref "The-fir-specification--Execution--Division-rules"}[division rules]
make it an op rule $`\mathrm{rule}_g`. Where $`g` gives the value $`v`,
the rule ends with the one-element result vector $`(v)`, whose one
element is $`v`, as $`()` is the empty one; where $`g` gives UB, it ends
with UB. In the set monad, for all operands $`a, b` and every
way $`e` to end:

$$`\begin{aligned} & e \in \mathrm{rule}_g(a, b) \iff \\ & \quad (\exists v.\ g(a, b) = \mathsf{ok}~v \wedge e = \mathsf{ok}~(v)) \\ & \quad \lor (\exists r.\ g(a, b) = \mathsf{ub}~r \wedge e = \mathsf{ub}~r) \end{aligned}`

*Theorem: such a rule has an outcome on every operand vector.* For every
$`g`, $`\mathrm{rule}_g(a, b)` is not empty, for all $`a` and $`b`.
:::

:::readable Fir.Core.div_poisonOut Fir.Core.div_ubByOwnRules (pin := Fir.Core.ruleOfEv) (pin := Fir.Core.divEv) (pin := Fir.HVector.Any) (pin := Fir.HVector.All) (pin := Fir.HVector.IsFilledBy) (pin := Fir.Core.Ty.IsPoison) (fingerprint := "554385857023679519")
*Theorem: the two poison clauses, for a division.* For every name, $`s`
and $`q`, the op rule $`\mathrm{rule}_{\mathrm{div}}` made from
$`\mathrm{div}_{s,q}` meets the two clauses of an op that
{ref "The-fir-specification--Execution--Poison-classes"}[propagates poison],
on every operand vector $`(a, b)` some element of which is poison:

* _Poison out_: if it ends with the result vector $`\vec{r}`, every
  element of $`\vec{r}` is poison.
* _UB only by the op's own rules_: if it ends with UB, some vector that
  fills $`(a, b)` makes it end with UB too.

The first follows from the first theorem above, the second from the
second.
:::

:::readable Fir.Core.div_returnsOnDefined Fir.Core.div_width_zero_noResult (pin := Fir.Core.ruleOfEv) (pin := Fir.Core.divEv) (pin := Fir.HVector.Any) (pin := Fir.Core.Ty.IsPoison) (fingerprint := "3590146221175145122")
*Theorem: at a width above zero, a division returns a result on defined
operands.* For every name, $`s` and $`q`, and every $`w > 0`, some
operand vector of $`\mathsf{i}w` with no poison, namely $`(0, 1)`, makes
$`\mathrm{rule}_{\mathrm{div}}` end with a result.

*Theorem: at width zero, a division returns no result on defined
operands.* For every name, $`s` and $`q`, and every operand vector of
$`\mathsf{i}0` with no poison, $`\mathrm{rule}_{\mathrm{div}}` never ends
with a result: it is UB.
:::

:::readable Fir.Core.div_monotone (pin := Fir.Core.ruleOfEv) (pin := Fir.Core.divEv) (pin := Fir.SetM.IsRefinedBy) (pin := Fir.HVector.Forall₂) (fingerprint := "14342705339474605535")
*Theorem: a division is monotone.* For every name, $`s` and $`q`, and
all operand vectors $`\vec{v}` and
$`\vec{v}'` of two values of $`\mathsf{i}w` such that each $`v'_i` refines
$`v_i`, $`\mathrm{rule}_{\mathrm{div}}(\vec{v}')`
{ref "The-fir-specification--Execution--Poison-classes"}[refines]
$`\mathrm{rule}_{\mathrm{div}}(\vec{v})`, by refinement of the results
position by position. It is the theorem on refined operands above, carried
to the op rule.
:::

:::readable Fir.Core.sdiv_propagatesPoison Fir.Core.sdiv_returnsOnDefined Fir.Core.sdiv_total Fir.Core.sdiv_monotone Fir.Core.udiv_propagatesPoison Fir.Core.udiv_returnsOnDefined Fir.Core.udiv_total Fir.Core.udiv_monotone Fir.Core.srem_propagatesPoison Fir.Core.srem_returnsOnDefined Fir.Core.srem_total Fir.Core.srem_monotone Fir.Core.urem_propagatesPoison Fir.Core.urem_returnsOnDefined Fir.Core.urem_total Fir.Core.urem_monotone (pin := Fir.PropagatesPoison) (pin := Fir.ReturnsOnDefined) (pin := Fir.OpTotal) (pin := Fir.OpMonotone) (pin := Fir.Core.Op.denote?) (pin := Fir.Core.sdivWith) (pin := Fir.Core.udivWith) (pin := Fir.Core.sremValues) (pin := Fir.Core.uremValues) (fingerprint := "8460908753953926554")
*Theorem: $`\mathsf{sdiv}`, $`\mathsf{udiv}`, $`\mathsf{srem}` and
$`\mathsf{urem}` are lawful at every width above zero.* For every width
$`w`, under fir's execution rules, each of $`\mathsf{sdiv}_w` and
$`\mathsf{udiv}_w`, with or without $`\mathsf{exact}`, and each of
$`\mathsf{srem}_w` and $`\mathsf{urem}_w`:

* {ref "The-fir-specification--Execution--Poison-classes"}[propagates poison];
* when $`w > 0`, returns a result on defined operands;
* is total;
* is monotone.

Each op's rule is the shared rule, with its own name, signedness and
result on two values, so each follows from the theorems above.
$`\mathsf{exact}` changes only that result, poison in place of a quotient,
so the theorems hold with it and without it.
:::

:::readable Fir.Core.div_zero_width (pin := Fir.ReturnsOnDefined) (pin := Fir.LawfulDialectPoison) (pin := Fir.Core.Ty.Valid) (fingerprint := "18111245168969966839")
*Theorem: at width zero, no division returns a result on defined
operands.* With or without $`\mathsf{exact}`, none of
$`\mathsf{sdiv}_0`, $`\mathsf{udiv}_0`, $`\mathsf{srem}_0` and
$`\mathsf{urem}_0` returns a result on defined operands: every divisor of
zero bits is zero.

So the four ops break that obligation at width zero. $`\mathsf{i}0` is
not a {ref "The-fir-specification--Abstract-syntax--Core-types"}[type]:
validation accepts $`\mathsf{i}N` only for $`N \ge 1`. A
{ref "The-fir-specification--Execution--Poison-classes"}[lawful dialect]
asks the obligations only of valid op instances, so the core dialect is
lawful while division at $`\mathsf{i}0` keeps its rule
(ADR-2026-10-29-2006). The theorem shows why that restriction is needed.
:::
