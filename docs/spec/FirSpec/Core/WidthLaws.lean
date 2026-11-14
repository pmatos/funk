import VersoManual
import Fir.Core.WidthLaws
import Fir.Core.Validation
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on width change obligations, which
renders `Fir.Core.WidthLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Width change obligations: readable blocks" =>

:::moduleDocs (fingerprint := "4452560916230905096")
:::

:::readable Fir.Core.UnaryStrict Fir.Core.UnaryStrict.isRefinedBy (pin := Fir.PoisonOr.IsRefinedBy) (fingerprint := "2141592877862596573")
*Definition: a strict rule on one value.* A rule $`g` that maps a value of
$`\mathsf{i}M` to a value of $`\mathsf{i}N` is _strict_ when
$`g(\mathsf{poison}) = \mathsf{poison}`.

*Theorem: a strict rule on one value keeps refinement.* For every strict
$`g` and all $`a, a' \in \llbracket \mathsf{i}M \rrbracket`, if
$`a \sqsubseteq a'`, then $`g(a) \sqsubseteq g(a')`.

If $`a` is poison, $`g(a)` is poison, which every value refines;
otherwise $`a'` is $`a`, and gives the same. It is the one-operand
counterpart of the
{ref "The-fir-specification--Execution--Arithmetic-obligations"}[strict rules]
of binary ops, and gives the monotonicity of the width changes below.
:::

:::readable Fir.Core.unaryStrict_zextValue Fir.Core.unaryStrict_sextValue Fir.Core.unaryStrict_truncValue (pin := Fir.Core.zextValue) (pin := Fir.Core.sextValue) (pin := Fir.Core.truncValue) (fingerprint := "2792057861907017526")
*Theorem: the width changes are strict.* For all widths $`M` and $`N`,
the {ref "The-fir-specification--Execution--Width-change-rules"}[rules] of
$`\mathsf{zext}`, $`\mathsf{sext}` and $`\mathsf{trunc}` from
$`\mathsf{i}M` to $`\mathsf{i}N` give poison on poison. On a value, at
the widths validation accepts, they put zeros above its bits, put copies of its top bit above them, or keep
its low $`N` bits.
:::

:::readable Fir.Core.zext_propagatesPoison Fir.Core.zext_returnsOnDefined Fir.Core.zext_total Fir.Core.zext_monotone (pin := Fir.PropagatesPoison) (pin := Fir.PoisonOut) (pin := Fir.UBByOwnRules) (pin := Fir.ReturnsOnDefined) (pin := Fir.OpTotal) (pin := Fir.OpMonotone) (pin := Fir.Core.Op.denote?) (pin := Fir.Core.zextValue) (pin := Fir.Core.Op.Valid) (fingerprint := "6461532806751948721")
*Theorem: $`\mathsf{zext}` is lawful.* For all widths $`m` and $`n`,
under fir's execution rules, $`\mathsf{zext}_{m \to n}`, from $`\mathsf{i}m`
to $`\mathsf{i}n`, meets every obligation of an op that
{ref "The-fir-specification--Execution--Poison-classes"}[propagates poison]:

* _Poison out_: on a poison operand, its one result is poison.
* _UB only by the op's own rules_: it is never UB, so the clause holds
  with nothing to check.
* _A result on defined operands_: on $`0` it gives a result.
* _Totality and monotonicity_: it gives exactly one result on every
  operand, and that result keeps refinement, since its rule is strict.

The theorems hold at every pair of widths, even where $`n \le m`, which
validation rejects for $`\mathsf{zext}`: they need nothing of the widths.
:::

:::readable Fir.Core.sext_propagatesPoison Fir.Core.sext_returnsOnDefined Fir.Core.sext_total Fir.Core.sext_monotone (pin := Fir.PropagatesPoison) (pin := Fir.PoisonOut) (pin := Fir.UBByOwnRules) (pin := Fir.ReturnsOnDefined) (pin := Fir.OpTotal) (pin := Fir.OpMonotone) (pin := Fir.Core.Op.denote?) (pin := Fir.Core.sextValue) (fingerprint := "3600743820617804349")
*Theorem: $`\mathsf{sext}` is lawful.* For all widths $`m` and $`n`,
under fir's execution rules, $`\mathsf{sext}_{m \to n}`, from $`\mathsf{i}m`
to $`\mathsf{i}n`, propagates poison, returns a result on defined operands,
and is total and monotone, for the reasons that $`\mathsf{zext}` is.
:::

:::readable Fir.Core.trunc_propagatesPoison Fir.Core.trunc_returnsOnDefined Fir.Core.trunc_total Fir.Core.trunc_monotone (pin := Fir.PropagatesPoison) (pin := Fir.PoisonOut) (pin := Fir.UBByOwnRules) (pin := Fir.ReturnsOnDefined) (pin := Fir.OpTotal) (pin := Fir.OpMonotone) (pin := Fir.Core.Op.denote?) (pin := Fir.Core.truncValue) (fingerprint := "150713247520905855")
*Theorem: $`\mathsf{trunc}` is lawful.* For all widths $`m` and $`n`,
under fir's execution rules, $`\mathsf{trunc}_{m \to n}`, from $`\mathsf{i}m`
to $`\mathsf{i}n`, propagates poison, returns a result on defined operands,
and is total and monotone, for the reasons that $`\mathsf{zext}` is.
:::
