import VersoManual
import Fir.Core.CompareLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on comparison and selection
obligations, which renders `Fir.Core.CompareLaws` (ADR-2026-11-05-2012).
Each block explains declarations of that module and pins their
fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "Comparison and selection obligations: readable blocks" =>

:::moduleDocs (fingerprint := "3474095909161458154")
:::

:::readable Fir.Core.icmpValues_poison Fir.Core.icmpValues_isRefinedBy (pin := Fir.Core.icmpValues) (pin := Fir.PoisonOr.IsRefinedBy) (fingerprint := "4056786543972866582")
*Theorem: a poison operand of a comparison gives poison.* For every
{ref "The-fir-specification--Abstract-syntax--Core-ops"}[predicate]
$`p`, width $`w` and $`a, b \in \llbracket \mathsf{i}w \rrbracket`, if
$`a` or $`b` is poison, the
{ref "The-fir-specification--Execution--Comparison-and-selection-rules"}[comparison]
$`\mathrm{icmp}_p(a, b)` is the poison of $`\mathsf{i1}`. On two values it
is $`1` when $`p` holds of them and $`0` when it does not.

*Theorem: comparing refined operands refines the comparison.* For all
$`a, b, a', b' \in \llbracket \mathsf{i}w \rrbracket`, if
$`a \sqsubseteq a'` and $`b \sqsubseteq b'`, then
$`\mathrm{icmp}_p(a, b) \sqsubseteq \mathrm{icmp}_p(a', b')`.

These are the facts that the proofs that $`\mathsf{icmp}` is lawful need
of its rule. Its result is an $`\mathsf{i1}`, not an $`\mathsf{i}w`, so
the {ref "The-fir-specification--Execution--Arithmetic-obligations"}[strict rules]
of binary ops, which keep the width, do not apply as they are stated.
:::

:::readable Fir.Core.icmp_propagatesPoison Fir.Core.icmp_returnsOnDefined Fir.Core.icmp_total Fir.Core.icmp_monotone (pin := Fir.PropagatesPoison) (pin := Fir.PoisonOut) (pin := Fir.UBByOwnRules) (pin := Fir.ReturnsOnDefined) (pin := Fir.OpTotal) (pin := Fir.OpMonotone) (pin := Fir.Core.Op.denote?) (pin := Fir.Core.icmpValues) (fingerprint := "13380994339209071070")
*Theorem: $`\mathsf{icmp}` is lawful, with every predicate.* For every
predicate $`p` and width $`w`, under fir's execution rules,
$`\mathsf{icmp}_w~p` meets every obligation of an op that
{ref "The-fir-specification--Execution--Poison-classes"}[propagates poison]:

* _Poison out_: on two operands of which one is poison, its result is the
  poison of $`\mathsf{i1}`.
* _UB only by the op's own rules_: it is never UB, so the clause holds
  with nothing to check.
* _A result on defined operands_: on $`0` and $`0` it gives a result.
* _Totality and monotonicity_: it gives exactly one result on every two
  operands, and that result keeps refinement, by the theorems above.
:::

:::readable Fir.Core.selectValues_isRefinedBy (pin := Fir.Core.selectValues) (pin := Fir.PoisonOr.IsRefinedBy) (fingerprint := "15867863522020130414")
*Theorem: selecting with refined operands refines the selection.* For
every width $`w`, all $`c, c' \in \llbracket \mathsf{i1} \rrbracket` and
all $`a, b, a', b' \in \llbracket \mathsf{i}w \rrbracket`, if
$`c \sqsubseteq c'`, $`a \sqsubseteq a'` and $`b \sqsubseteq b'`, then

$$`\mathrm{select}(c, a, b) \sqsubseteq \mathrm{select}(c', a', b')`

Here $`\mathrm{select}(c, a, b)` is the
{ref "The-fir-specification--Execution--Comparison-and-selection-rules"}[rule]
of $`\mathsf{select}`: $`a` when $`c` is $`1`, $`b` when $`c` is $`0`,
each as it is, poison or not, and poison when $`c` is poison. A poison
condition gives poison, which every value refines. A defined condition is
refined only by itself, so both sides choose the same operand, and the
chosen operand on the right refines the one on the left. The operand not
chosen plays no part, so it may be poison.
:::

:::readable Fir.Core.select_total Fir.Core.select_monotone (pin := Fir.OpTotal) (pin := Fir.OpMonotone) (pin := Fir.Core.Op.denote?) (pin := Fir.Core.selectValues) (fingerprint := "1058401768696949246")
*Theorem: $`\mathsf{select}` is total and monotone.* For every width
$`w`, under fir's execution rules, $`\mathsf{select}_w` is
{ref "The-fir-specification--Execution--Poison-classes"}[total] and
{ref "The-fir-specification--Execution--Poison-classes"}[monotone]. It
gives exactly one result on every three operands, and that result keeps
refinement, by the theorem above. $`\mathsf{select}` is an exception to
poison propagation, since a poison operand that it does not choose gives
no poison, so these are the only obligations it has.
:::
