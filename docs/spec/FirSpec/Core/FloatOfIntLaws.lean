import VersoManual
import Fir.Core.FloatOfIntLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the obligations of the conversions
from integers to floats, which renders `Fir.Core.FloatOfIntLaws`
(ADR-2026-11-05-2012). Each block explains declarations of that module and
pins their fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "Conversion obligations: readable blocks" =>

:::moduleDocs (fingerprint := "12947573626106326802")
:::

:::readable Fir.Core.intToFloat_ends Fir.Core.intToFloat_map (pin := Fir.Core.intToFloat) (pin := Fir.Core.Ends) (pin := Fir.MonadMorphism.KeepsChoiceUB) (fingerprint := "1397656925286651098")
*Theorems: the rules of the conversions end, and mean the same in
another monad.* On every operand, the rule of $`\mathsf{sitofp}` and of
$`\mathsf{uitofp}`
{ref "The-fir-specification--Execution--Float-arithmetic-obligations"}[ends]:
on a value it is a float result, and on poison it is
$`\mathsf{pure}~\mathsf{poison}`. A monad morphism that
{ref "The-fir-specification--Execution--Monad-morphisms"}[keeps choice and UB]
maps each rule in one monad to the same rule in the other. So in
`fir-ref`'s
{ref "The-fir-specification--Execution--Choice-trees"}[tree of choices]
each rule has as its set what it is in the set monad, and `fir-ref run`'s
modes give the spec's outcomes on the conversions.
:::

:::readable Fir.Core.intToFloatOp (pin := Fir.Core.Op) (fingerprint := "15035836613155861848")
*Definition: the conversion of a signedness.* $`\mathrm{conv}_{N,e,m}(\mathit{true})`
is $`\mathsf{sitofp}_{N,e,m}`, and $`\mathrm{conv}_{N,e,m}(\mathit{false})`
is $`\mathsf{uitofp}_{N,e,m}`, so that the theorems below are stated once
for both.
:::

:::readable Fir.Core.intToFloat_propagatesPoison Fir.Core.intToFloat_returnsOnDefined Fir.Core.intToFloat_total Fir.Core.intToFloat_monotone Fir.Core.intToFloat_neverUB Fir.Core.intToFloat_makesNoPoison (pin := Fir.PropagatesPoison) (pin := Fir.ReturnsOnDefined) (pin := Fir.OpTotal) (pin := Fir.OpMonotone) (pin := Fir.NeverUBSetM) (pin := Fir.MakesNoPoisonSetM) (pin := Fir.Core.Op.denote?) (fingerprint := "12774677476342323033")
*Theorem: $`\mathsf{sitofp}` and $`\mathsf{uitofp}` are lawful, from every
width to every format.* Under fir's execution rules, each meets every
obligation of an op that
{ref "The-fir-specification--Execution--Poison-classes"}[propagates poison],
and the obligations of a pure op, by the reasons the
{ref "The-fir-specification--Execution--Float-arithmetic-obligations"}[float arithmetic of one operand]
does, on an integer operand:

* _Poison out_: on a poison operand, its one result is poison.
* _UB only by the op's own rules_: it is never UB, so the clause holds
  with nothing to check.
* _A result on defined operands_: on the integer $`0` it gives a result.
* _Totality_: it has a way to end on every operand.
* _Monotonicity_: a poison operand gives poison, which every result
  refines, and a defined operand is refined only by itself.
* _No UB and no poison_: it is never UB, and on a defined operand every
  result is defined.

The theorems hold at every width and format, even ones that validation
rejects: they need nothing of $`N`, $`e` and $`m`.
:::
