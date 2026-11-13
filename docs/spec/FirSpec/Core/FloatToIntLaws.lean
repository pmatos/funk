import VersoManual
import Fir.Core.FloatToIntLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the obligations of the conversions
from floats to integers, which renders `Fir.Core.FloatToIntLaws`
(ADR-2026-11-05-2012). Each block explains declarations of that module and
pins their fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "Integer conversion obligations: readable blocks" =>

:::moduleDocs (fingerprint := "5273593330559932615")
:::

:::readable Fir.Core.floatToIntOp (pin := Fir.Core.Op) (fingerprint := "15379204975273843069")
*Definition: the conversion of a signedness.* $`\mathrm{conv}_{e,m,N}(\mathit{true})`
is $`\mathsf{fptosi}_{e,m,N}`, and $`\mathrm{conv}_{e,m,N}(\mathit{false})`
is $`\mathsf{fptoui}_{e,m,N}`, so that the theorems below are stated once
for both.
:::

:::readable Fir.Core.unaryStrict_floatToInt (pin := Fir.Core.UnaryStrict) (pin := Fir.Core.floatToInt) (fingerprint := "10453927260904731693")
*Theorem: the rule is strict.* For every format, width and signedness,
the rule of the conversion gives $`\mathsf{poison}` on
$`\mathsf{poison}`, as the
{ref "The-fir-specification--Execution--Width-change-obligations"}[width changes]
do.
:::

:::readable Fir.Core.floatToInt_propagatesPoison Fir.Core.floatToInt_returnsOnDefined Fir.Core.floatToInt_total Fir.Core.floatToInt_monotone (pin := Fir.PropagatesPoison) (pin := Fir.PoisonOut) (pin := Fir.UBByOwnRules) (pin := Fir.ReturnsOnDefined) (pin := Fir.OpTotal) (pin := Fir.OpMonotone) (pin := Fir.Core.Op.denote?) (fingerprint := "7718149681668267806")
*Theorem: $`\mathsf{fptosi}` and $`\mathsf{fptoui}` are lawful, from every
format to every width.* Under fir's execution rules, each meets every
obligation of an op that
{ref "The-fir-specification--Execution--Poison-classes"}[propagates poison]:

* _Poison out_: on a poison operand, its one result is poison.
* _UB only by the op's own rules_: it is never UB, so the clause holds
  with nothing to check.
* _A result on defined operands_: on the bits $`0`, which are $`+0`, it
  gives a result.
* _Totality_: it gives exactly one result on every operand.
* _Monotonicity_: its rule is strict, so a poison operand gives poison,
  which every result refines, and a defined operand is refined only by
  itself.

Unlike the conversions from integers, neither meets the obligation of no
poison: an integer out of range, an infinity or a NaN gives poison on a
defined operand, so each declares $`\mathsf{mayPoison}`. The theorems hold
at every format and width, even ones that validation rejects: they need
nothing of $`e`, $`m` and $`N`.
:::
