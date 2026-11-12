import VersoManual
import Fir.Core.FloatCompareLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the float comparison obligations,
which renders `Fir.Core.FloatCompareLaws` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Float comparison obligations: readable blocks" =>

:::moduleDocs (fingerprint := "16333021387507876316")
:::

:::readable Fir.Core.fcmpValues_poison Fir.Core.fcmpValues_isRefinedBy (pin := Fir.Core.fcmpValues) (pin := Fir.PoisonOr.IsRefinedBy) (fingerprint := "5197640117760213564")
*Theorem: a poison operand of a float comparison gives poison.* For every
float predicate $`p`, flags $`\phi`, format $`\mathsf{float}\langle e,m \rangle` and
$`a, b \in \llbracket \mathsf{float}\langle e,m \rangle \rrbracket`, if
$`a` or $`b` is poison, $`\mathsf{fcmp}_{e,m}~\phi~p\,(a, b)` is the poison of
$`\mathsf{i1}`.

*Theorem: comparing refined operands refines the comparison.* If
$`a \sqsubseteq a'` and $`b \sqsubseteq b'`, then
$`\mathsf{fcmp}_{e,m}~\phi~p\,(a, b) \sqsubseteq \mathsf{fcmp}_{e,m}~\phi~p\,(a', b')`.
A defined float is refined only by itself, so the two sides compare the
same bits under the same flags, or the left side is poison.
:::

:::readable Fir.Core.fcmp_propagatesPoison Fir.Core.fcmp_returnsOnDefined Fir.Core.fcmp_total Fir.Core.fcmp_monotone (pin := Fir.PropagatesPoison) (pin := Fir.ReturnsOnDefined) (pin := Fir.OpTotal) (pin := Fir.OpMonotone) (pin := Fir.Core.Op.denote?) (pin := Fir.Core.fcmpValues) (fingerprint := "10449641329668636775")
*Theorem: $`\mathsf{fcmp}` is lawful, with every predicate and flag and at
every format.* Under fir's execution rules, $`\mathsf{fcmp}_{e,m}~\phi~p` meets every
obligation of an op that
{ref "The-fir-specification--Execution--Poison-classes"}[propagates poison]:

* _Poison out_: on two operands of which one is poison, its result is the
  poison of $`\mathsf{i1}`.
* _UB only by the op's own rules_: it is never UB, so the clause holds
  with nothing to check.
* _A result on defined operands_: on $`+0` and $`+0` it gives a result,
  poison or a bit.
* _Totality and monotonicity_: it gives exactly one result on every two
  operands, and that result keeps refinement, by the theorems above.

None of the proofs looks at how the model compares two floats.
:::
