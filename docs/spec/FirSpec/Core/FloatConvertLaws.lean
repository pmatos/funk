import VersoManual
import Fir.Core.FloatConvertLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the obligations of the conversions
between float formats, which renders `Fir.Core.FloatConvertLaws`
(ADR-2026-11-05-2012). Each block explains declarations of that module and
pins their fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "Format conversion obligations: readable blocks" =>

:::moduleDocs (fingerprint := "13944966831994002610")
:::

:::readable Fir.Core.convertFloat_ends Fir.Core.convertFloat_map (pin := Fir.Core.convertFloat) (pin := Fir.Core.Ends) (pin := Fir.MonadMorphism.KeepsChoiceUB) (fingerprint := "8878047545628183774")
*Theorems: the rules of the conversions between formats end, and mean the same in
another monad.* On every operand, the rule of $`\mathsf{fpext}` and
of $`\mathsf{fptrunc}`
{ref "The-fir-specification--Execution--Float-arithmetic-obligations"}[ends]:
on a value it is a float result, and on poison it is
$`\mathsf{pure}~\mathsf{poison}`. A monad morphism that
{ref "The-fir-specification--Execution--Monad-morphisms"}[keeps choice and UB]
maps each rule in one monad to the same rule in the other. So in
`fir-ref`'s
{ref "The-fir-specification--Execution--Choice-trees"}[tree of choices]
each rule has as its set what it is in the set monad, and `fir-ref run`'s
modes give the spec's outcomes on the conversions between formats.
:::

:::readable Fir.Core.convertOp (pin := Fir.Core.Op) (fingerprint := "4552996230438127180")
*Definition: the conversion of a kind.* $`\mathrm{conv}_{e,m,e',m'}(\mathit{true})`
is $`\mathsf{fpext}_{e,m,e',m'}`, and $`\mathrm{conv}_{e,m,e',m'}(\mathit{false})`
is $`\mathsf{fptrunc}_{e,m,e',m'}`, so that the theorems below are stated
once for both.
:::

:::readable Fir.Core.convertFloat_propagatesPoison Fir.Core.convertFloat_returnsOnDefined Fir.Core.convertFloat_total Fir.Core.convertFloat_monotone Fir.Core.convertFloat_neverUB Fir.Core.convertFloat_makesNoPoison (pin := Fir.PropagatesPoison) (pin := Fir.ReturnsOnDefined) (pin := Fir.OpTotal) (pin := Fir.OpMonotone) (pin := Fir.NeverUBSetM) (pin := Fir.MakesNoPoisonSetM) (pin := Fir.Core.Op.denote?) (fingerprint := "8115891059058339468")
*Theorem: $`\mathsf{fpext}` and $`\mathsf{fptrunc}` are lawful, between
every two formats.* Under fir's execution rules, each meets every
obligation of an op that
{ref "The-fir-specification--Execution--Poison-classes"}[propagates poison],
and the obligations of a pure op, by the reasons the
{ref "The-fir-specification--Execution--Float-arithmetic-obligations"}[float arithmetic of one operand]
does, with its result in another format:

* _Poison out_: on a poison operand, its one result is poison.
* _UB only by the op's own rules_: it is never UB, so the clause holds
  with nothing to check.
* _A result on defined operands_: on the bits $`0`, which are $`+0`, it
  gives a result.
* _Totality_: it has a way to end on every operand.
* _Monotonicity_: a poison operand gives poison, which every result
  refines, and a defined operand is refined only by itself.
* _No UB and no poison_: it is never UB, and on a defined operand every
  result is defined, a NaN's included.

The theorems hold at every two formats, even a pair that validation
rejects for the op: they need nothing of $`e`, $`m`, $`e'` and $`m'`.
:::
