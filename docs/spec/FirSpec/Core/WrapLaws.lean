import VersoManual
import Fir.Core.WrapLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on arithmetic obligations, which renders
`Fir.Core.WrapLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Arithmetic obligations: readable blocks" =>

:::moduleDocs (fingerprint := "10798246534216229047")
:::

:::readable Fir.Core.Strict Fir.Core.Strict.isRefinedBy (pin := Fir.PoisonOr.IsRefinedBy) (fingerprint := "16972614351431241810")
*Definition: a strict rule.* A rule $`g` that maps two values of
$`\mathsf{i}N` to one is _strict_ when a poison operand gives poison:

$$`\begin{aligned} \forall a\, b.\ & a = \mathsf{poison} \,\lor\, b = \mathsf{poison} \\ & \implies g(a, b) = \mathsf{poison} \end{aligned}`

*Theorem: a strict rule keeps refinement.* For every strict $`g` and all
$`a, b, a', b' \in \llbracket \mathsf{i}N \rrbracket`, if
$`a \sqsubseteq a'` and $`b \sqsubseteq b'`, then
$`g(a, b) \sqsubseteq g(a', b')`.

Here $`\sqsubseteq` is the
{ref "The-fir-specification--Execution--Core-values"}[refinement of core values].
If an operand on the left is poison, $`g(a, b)` is poison, which every
value refines. If neither is, each operand on the right is the same value,
and so is the result. Most binary core ops have a strict rule, so this one
theorem gives most of their
{ref "The-fir-specification--Execution--Poison-classes"}[monotonicity]
proofs, here and in the next sections.
:::

:::readable Fir.Core.strict_addValues Fir.Core.strict_subValues Fir.Core.strict_mulValues (pin := Fir.Core.addValues) (pin := Fir.Core.subValues) (pin := Fir.Core.mulValues) (fingerprint := "8218471344286748590")
*Theorem: the sum, the difference and the product are strict.* At every
width, the rules of $`\mathsf{add}`, $`\mathsf{sub}` and
$`\mathsf{mul}` without flags are strict: each gives the result modulo
$`2^N` of two values, and poison when either operand is poison
({ref "The-fir-specification--Execution--Arithmetic-rules"}[arithmetic rules],
{ref "The-fir-specification--Execution--Wrap-flag-rules"}[wrap flag rules]).
:::

:::readable Fir.Core.Strict.wrapValues Fir.Core.strict_addWith Fir.Core.strict_subWith Fir.Core.strict_mulWith (pin := Fir.Core.wrapValues) (pin := Fir.Core.addWith) (pin := Fir.Core.subWith) (pin := Fir.Core.mulWith) (fingerprint := "10685068778918726507")
*Theorem: the flags keep a rule strict.* Let $`g` be a strict rule,
$`f` any
{ref "The-fir-specification--Abstract-syntax--Core-ops"}[wrap flags], and
$`u` and $`s` any two tests on two vectors of $`N` bits. The rule
that gives poison on two values when $`f` sets $`\mathsf{nuw}` and
$`u` holds of them, or sets $`\mathsf{nsw}` and $`s` holds, and
otherwise gives what $`g` gives, is strict.

A flag is checked only on two values, so on a poison operand the rule
gives what $`g` gives, which is poison. In fir's
{ref "The-fir-specification--Execution--Wrap-flag-rules"}[wrap flag rules],
$`u` and $`s` say that the exact result does not fit in $`N` bits,
read as unsigned and as signed. So $`\mathsf{add}`, $`\mathsf{sub}`
and $`\mathsf{mul}` with any flags have strict rules.
:::

:::readable Fir.Core.add_propagatesPoison Fir.Core.add_returnsOnDefined Fir.Core.add_total Fir.Core.add_monotone (pin := Fir.PropagatesPoison) (pin := Fir.PoisonOut) (pin := Fir.UBByOwnRules) (pin := Fir.ReturnsOnDefined) (pin := Fir.OpTotal) (pin := Fir.OpMonotone) (pin := Fir.Core.Op.denote?) (pin := Fir.Core.addWith) (fingerprint := "3291689630042203968")
*Theorem: $`\mathsf{add}` is lawful, with any flags.* For every width
$`w` and flags $`f`, under fir's execution rules,
$`\mathsf{add}_w~f` meets every obligation of an op that
{ref "The-fir-specification--Execution--Poison-classes"}[propagates poison]:

* _Poison out_: on two operands of which one is poison, every result it
  gives is poison, since its rule is strict.
* _UB only by the op's own rules_: it is never UB, so the clause holds
  with nothing to check.
* _A result on defined operands_: on $`0` and $`0` it gives a result.
* _Totality and monotonicity_: it gives exactly one result on every two
  operands, and that result keeps refinement, since its rule is strict.
:::

:::readable Fir.Core.sub_propagatesPoison Fir.Core.sub_returnsOnDefined Fir.Core.sub_total Fir.Core.sub_monotone (pin := Fir.PropagatesPoison) (pin := Fir.PoisonOut) (pin := Fir.UBByOwnRules) (pin := Fir.ReturnsOnDefined) (pin := Fir.OpTotal) (pin := Fir.OpMonotone) (pin := Fir.Core.Op.denote?) (pin := Fir.Core.subWith) (fingerprint := "3120770644592111923")
*Theorem: $`\mathsf{sub}` is lawful, with any flags.* For every width
$`w` and flags $`f`, under fir's execution rules,
$`\mathsf{sub}_w~f` propagates poison, returns a result on defined
operands, and is total and monotone. The reasons are those of
$`\mathsf{add}`: its rule is strict, never UB, gives a result on
$`0` and $`0`, and gives exactly one result on every two operands.
:::

:::readable Fir.Core.mul_propagatesPoison Fir.Core.mul_returnsOnDefined Fir.Core.mul_total Fir.Core.mul_monotone (pin := Fir.PropagatesPoison) (pin := Fir.PoisonOut) (pin := Fir.UBByOwnRules) (pin := Fir.ReturnsOnDefined) (pin := Fir.OpTotal) (pin := Fir.OpMonotone) (pin := Fir.Core.Op.denote?) (pin := Fir.Core.mulWith) (fingerprint := "16348539734160995288")
*Theorem: $`\mathsf{mul}` is lawful, with any flags.* For every width
$`w` and flags $`f`, under fir's execution rules,
$`\mathsf{mul}_w~f` propagates poison, returns a result on defined
operands, and is total and monotone, for the reasons that
$`\mathsf{add}` is: its rule is strict, never UB, gives a result on
$`0` and $`0`, and gives exactly one result on every two operands.
:::
