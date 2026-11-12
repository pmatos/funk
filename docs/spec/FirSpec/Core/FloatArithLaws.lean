import VersoManual
import Fir.Core.FloatArithLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the float arithmetic obligations,
which renders `Fir.Core.FloatArithLaws` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Float arithmetic obligations: readable blocks" =>

:::moduleDocs (fingerprint := "3340853658294908848")
:::

:::readable Fir.Core.fbinValues_ends Fir.Core.funaryValue_ends Fir.Core.fmaValues_ends (pin := Fir.Core.fbinValues) (pin := Fir.Core.funaryValue) (pin := Fir.Core.fmaValues) (fingerprint := "2194462485675605231")
*Theorem: the rules of the float arithmetic end.* On every operands and
under all flags, the rule of each float op of arithmetic ends: on defined
operands it is a float result, and on a poison operand it is
$`\mathsf{pure}~\mathsf{poison}`.
:::

:::readable Fir.Core.oneFloat Fir.Core.oneFloat_ok Fir.Core.oneFloat_of Fir.Core.oneFloat_not_ub Fir.Core.oneFloat_poison_isRefinedBy Fir.Core.oneFloat_defined (pin := Fir.Core.Ends) (fingerprint := "1952775520341092492")
*Definition and theorems: a rule that gives one float.* $`\mathrm{one}(s)`
runs $`s` and gives its value as the one result of an op. When $`s` ends:

* each way $`\mathrm{one}(s)` ends is a value $`v` of $`s`, as the one
  result, and each value of $`s` is one way it ends;
* it is never UB;
* $`\mathrm{one}(\mathsf{pure}~\mathsf{poison})` is refined by
  $`\mathrm{one}(s)`: a poison result is refined by every value.

A result vector of one defined float holds no poison.
:::

:::readable Fir.Core.fbin_propagatesPoison Fir.Core.fbin_returnsOnDefined Fir.Core.fbin_total Fir.Core.fbin_monotone Fir.Core.fbin_neverUB Fir.Core.fbin_makesNoPoison (pin := Fir.PropagatesPoison) (pin := Fir.ReturnsOnDefined) (pin := Fir.OpTotal) (pin := Fir.OpMonotone) (pin := Fir.NeverUBSetM) (pin := Fir.MakesNoPoisonSetM) (pin := Fir.Core.Op.denote?) (fingerprint := "15250295935770345067")
*Theorem: $`\mathsf{fadd}`, $`\mathsf{fsub}`, $`\mathsf{fmul}` and
$`\mathsf{fdiv}` are lawful, at every format.* Under fir's execution
rules, each meets every obligation of an op that
{ref "The-fir-specification--Execution--Poison-classes"}[propagates poison],
and the obligations of a pure op:

* _Poison out_: on two operands of which one is poison, its one result is
  poison.
* _UB only by the op's own rules_: it is never UB, so the clause holds
  with nothing to check.
* _A result on defined operands_: on $`+0` and $`+0` it gives a result.
* _Totality_: it has a way to end on every two operands.
* _Monotonicity_: a poison operand gives poison, which every result
  refines, and defined operands are refined only by themselves.
* _No UB, and no poison without $`\mathsf{nnan}` and $`\mathsf{ninf}`_:
  it is never UB, and on defined operands, under flags that may not make
  poison, every result is defined, a NaN's bits and a zero of either sign
  included. With $`\mathsf{nnan}` or $`\mathsf{ninf}` the op declares
  that it may produce poison, so there is nothing to show.
:::

:::readable Fir.Core.funary_propagatesPoison Fir.Core.funary_returnsOnDefined Fir.Core.funary_total Fir.Core.funary_monotone Fir.Core.funary_neverUB Fir.Core.funary_makesNoPoison (pin := Fir.PropagatesPoison) (pin := Fir.ReturnsOnDefined) (pin := Fir.OpTotal) (pin := Fir.OpMonotone) (pin := Fir.NeverUBSetM) (pin := Fir.MakesNoPoisonSetM) (pin := Fir.Core.Op.denote?) (fingerprint := "16131216264622624205")
*Theorem: $`\mathsf{fneg}`, $`\mathsf{fabs}` and $`\mathsf{sqrt}` are
lawful, at every format.* They meet the same obligations as the ops of two
operands, by the same reasons, on one operand: a poison operand gives
poison, $`+0` gives a result, every operand has a way to end, refined
operands give refined results, and none is ever UB or, without
$`\mathsf{nnan}` and $`\mathsf{ninf}`, gives poison on a defined operand.
:::

:::readable Fir.Core.fma_propagatesPoison Fir.Core.fma_returnsOnDefined Fir.Core.fma_total Fir.Core.fma_monotone Fir.Core.fma_neverUB Fir.Core.fma_makesNoPoison (pin := Fir.PropagatesPoison) (pin := Fir.ReturnsOnDefined) (pin := Fir.OpTotal) (pin := Fir.OpMonotone) (pin := Fir.NeverUBSetM) (pin := Fir.MakesNoPoisonSetM) (pin := Fir.Core.Op.denote?) (fingerprint := "13352190550858574830")
*Theorem: $`\mathsf{fma}` is lawful, at every format.* It meets the same
obligations on three operands: any poison operand gives poison, three
$`+0` give a result, every operand vector has a way to end, refined
operands give refined results, and it is never UB or, without
$`\mathsf{nnan}` and $`\mathsf{ninf}`, gives poison on defined operands.
:::

:::readable Fir.Core.fbinValues_toSet Fir.Core.funaryValue_toSet Fir.Core.fmaValues_toSet (pin := Fir.ChoiceTree.toSet) (fingerprint := "1205190481222606760")
*Theorem: the rules in the tree of choices.* Each rule of the float
arithmetic, and the float result it is built from, run in `fir-ref`'s
{ref "The-fir-specification--Execution--Choice-trees"}[tree of choices],
has as its set what it is in the set monad: the choice of a NaN result is
a choice of $`m + 1` bits in the tree, and every NaN of the format is one
path, and the sign of a zero under $`\mathsf{nsz}` is a choice of one
bit. So `fir-ref run`'s modes give the spec's outcomes on the float
arithmetic.
:::
