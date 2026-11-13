import VersoManual
import Fir.Core.PointerLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on pointer offset obligations, which
renders `Fir.Core.PointerLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Pointer offset obligations: readable blocks" =>

:::moduleDocs (fingerprint := "4913524385505399095")
:::

:::readable Fir.Core.ptraddValue_poison Fir.Core.ptraddValue_isRefinedBy (pin := Fir.Core.ptraddValue) (fingerprint := "5412114453367785822")
*Theorems: the rule of $`\mathsf{ptradd}` is strict, and keeps
refinement.* For every width $`W`, the
{ref "The-fir-specification--Execution--Pointer-offset-rules"}[rule] of
$`\mathsf{ptradd}_W` gives $`\mathsf{poison}` when either operand is
$`\mathsf{poison}`. So on operands that refine others, it gives a result
that refines the other's: a poison operand gives poison, which every
pointer refines, and a pointer or an integer is refined only by itself.
:::

:::readable Fir.Core.ptradd_propagatesPoison Fir.Core.ptradd_returnsOnDefined Fir.Core.ptradd_total Fir.Core.ptradd_monotone (pin := Fir.PropagatesPoison) (pin := Fir.PoisonOut) (pin := Fir.UBByOwnRules) (pin := Fir.ReturnsOnDefined) (pin := Fir.OpTotal) (pin := Fir.OpMonotone) (pin := Fir.Core.Op.denote?) (pin := Fir.Core.ptraddValue) (fingerprint := "11773334422015642486")
*Theorem: the pointer offset is lawful.* For every memory $`N` and width
$`W`, under fir's execution rules, $`\mathsf{ptradd}_{N,W}` meets every
obligation of an op that
{ref "The-fir-specification--Execution--Poison-classes"}[propagates poison]:

* _Poison out_: on a poison operand, its one result is poison.
* _UB only by the op's own rules_: it is never UB, so the clause holds
  with nothing to check.
* _A result on defined operands_: on the pointer with no provenance at
  offset 0 and the integer 0, it gives a result.
* _Totality and monotonicity_: it gives exactly one result on every
  operand vector, and that result keeps refinement, since its rule is
  strict.

The theorems hold at every memory and every width, even ones that
validation rejects.
:::

:::readable Fir.Core.ptradd_neverUB Fir.Core.ptradd_makesNoPoison (pin := Fir.NeverUBSetM) (pin := Fir.MakesNoPoisonSetM) (pin := Fir.Core.Op.denote?) (pin := Fir.Core.ptraddValue) (fingerprint := "2120500762697677806")
*Theorems: the pointer offset is pure.* $`\mathsf{ptradd}_{N,W}` is
never UB, and on a pointer and an integer, neither poison, it gives a
pointer, not poison. So it meets the
{ref "The-fir-specification--Execution--Effect-obligations"}[effect obligations]
of the empty set of effects that it declares.
:::
