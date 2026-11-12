import VersoManual
import Fir.Core.BitwiseLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on bitwise and shift obligations, which
renders `Fir.Core.BitwiseLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Bitwise and shift obligations: readable blocks" =>

:::moduleDocs (fingerprint := "15860657129012602685")
:::

:::readable Fir.Core.strict_andValues Fir.Core.strict_orValues Fir.Core.strict_xorValues (pin := Fir.Core.Strict) (pin := Fir.Core.andValues) (pin := Fir.Core.orValues) (pin := Fir.Core.xorValues) (fingerprint := "7956797132507196145")
*Theorem: the rules of $`\mathsf{and}`, $`\mathsf{or}` and $`\mathsf{xor}`
are strict.* At every width, each of the three
{ref "The-fir-specification--Execution--Bitwise-and-shift-rules"}[rules]
combines two values bit by bit, and gives poison when either operand is
poison, so it is
{ref "The-fir-specification--Execution--Arithmetic-obligations"}[strict]:
a poison operand gives poison.
:::

:::readable Fir.Core.strict_shiftValues Fir.Core.strict_shlValues Fir.Core.strict_lshrValues Fir.Core.strict_ashrValues (pin := Fir.Core.Strict) (pin := Fir.Core.shiftValues) (pin := Fir.Core.shlValues) (pin := Fir.Core.lshrValues) (pin := Fir.Core.ashrValues) (fingerprint := "16823717942633141533")
*Theorem: a shift is strict, whatever it shifts by.* For every way $`s` to
shift a vector of $`N` bits by an amount, the
{ref "The-fir-specification--Execution--Bitwise-and-shift-rules"}[shift rule]
built on $`s` is strict. That rule gives $`s(a, n)` on a value $`a` and an
amount $`n`, read as unsigned, when $`n < N`; poison when $`n \ge N`; and
poison when either operand is poison. So the rules of $`\mathsf{shl}`,
$`\mathsf{lshr}` and $`\mathsf{ashr}`, which shift left, right filling
with zeros, and right filling with the sign bit, are strict.

A shift by $`N` or more gives poison on two values as well. That does not
stop the rule being strict, which speaks only of poison operands, and a
defined amount is refined only by itself, so it changes no proof below.
:::

:::readable Fir.Core.and_propagatesPoison Fir.Core.and_returnsOnDefined Fir.Core.and_total Fir.Core.and_monotone (pin := Fir.PropagatesPoison) (pin := Fir.PoisonOut) (pin := Fir.UBByOwnRules) (pin := Fir.ReturnsOnDefined) (pin := Fir.OpTotal) (pin := Fir.OpMonotone) (pin := Fir.Core.Op.denote?) (pin := Fir.Core.andValues) (fingerprint := "3606814103211963528")
*Theorem: $`\mathsf{and}` is lawful.* For every width $`w`, under fir's
execution rules, $`\mathsf{and}_w` meets every obligation of an op that
{ref "The-fir-specification--Execution--Poison-classes"}[propagates poison]:

* _Poison out_: on two operands of which one is poison, every result it
  gives is poison, since its rule is
  {ref "The-fir-specification--Execution--Arithmetic-obligations"}[strict].
* _UB only by the op's own rules_: it is never UB, so the clause holds
  with nothing to check.
* _A result on defined operands_: on $`0` and $`0` it gives a result.
* _Totality and monotonicity_: it gives exactly one result on every two
  operands, and that result keeps refinement, since its rule is strict.
:::

:::readable Fir.Core.or_propagatesPoison Fir.Core.or_returnsOnDefined Fir.Core.or_total Fir.Core.or_monotone (pin := Fir.PropagatesPoison) (pin := Fir.PoisonOut) (pin := Fir.UBByOwnRules) (pin := Fir.ReturnsOnDefined) (pin := Fir.OpTotal) (pin := Fir.OpMonotone) (pin := Fir.Core.Op.denote?) (pin := Fir.Core.orValues) (fingerprint := "704386965778241276")
*Theorem: $`\mathsf{or}` is lawful.* For every width $`w`, under fir's
execution rules, $`\mathsf{or}_w` propagates poison, returns a result on
defined operands, and is total and monotone, for the reasons that
$`\mathsf{and}` is: its rule is strict, never UB, gives a result on $`0`
and $`0`, and gives exactly one result on every two operands.
:::

:::readable Fir.Core.xor_propagatesPoison Fir.Core.xor_returnsOnDefined Fir.Core.xor_total Fir.Core.xor_monotone (pin := Fir.PropagatesPoison) (pin := Fir.PoisonOut) (pin := Fir.UBByOwnRules) (pin := Fir.ReturnsOnDefined) (pin := Fir.OpTotal) (pin := Fir.OpMonotone) (pin := Fir.Core.Op.denote?) (pin := Fir.Core.xorValues) (fingerprint := "6708760049217499061")
*Theorem: $`\mathsf{xor}` is lawful.* For every width $`w`, under fir's
execution rules, $`\mathsf{xor}_w` propagates poison, returns a result on
defined operands, and is total and monotone, for the reasons that
$`\mathsf{and}` is.
:::

:::readable Fir.Core.shl_propagatesPoison Fir.Core.shl_returnsOnDefined Fir.Core.shl_total Fir.Core.shl_monotone (pin := Fir.PropagatesPoison) (pin := Fir.PoisonOut) (pin := Fir.UBByOwnRules) (pin := Fir.ReturnsOnDefined) (pin := Fir.OpTotal) (pin := Fir.OpMonotone) (pin := Fir.Core.Op.denote?) (pin := Fir.Core.shlValues) (fingerprint := "17358436313817332086")
*Theorem: $`\mathsf{shl}` is lawful.* For every width $`w`, under fir's
execution rules, $`\mathsf{shl}_w` propagates poison, returns a result on
defined operands, and is total and monotone. A poison value or a poison
amount gives only poison, and a shift is never UB. On the value $`0` and
the amount $`0` it gives a result: at a width above zero, the value
itself, and at width zero, where every amount is too large, poison, which
is a result too. It gives exactly one result on every two operands, and
its rule is strict, so it is monotone.
:::

:::readable Fir.Core.lshr_propagatesPoison Fir.Core.lshr_returnsOnDefined Fir.Core.lshr_total Fir.Core.lshr_monotone (pin := Fir.PropagatesPoison) (pin := Fir.PoisonOut) (pin := Fir.UBByOwnRules) (pin := Fir.ReturnsOnDefined) (pin := Fir.OpTotal) (pin := Fir.OpMonotone) (pin := Fir.Core.Op.denote?) (pin := Fir.Core.lshrValues) (fingerprint := "13398049719288732724")
*Theorem: $`\mathsf{lshr}` is lawful.* For every width $`w`, under fir's
execution rules, $`\mathsf{lshr}_w` propagates poison, returns a result
on defined operands, and is total and monotone, for the reasons that
$`\mathsf{shl}` is.
:::

:::readable Fir.Core.ashr_propagatesPoison Fir.Core.ashr_returnsOnDefined Fir.Core.ashr_total Fir.Core.ashr_monotone (pin := Fir.PropagatesPoison) (pin := Fir.PoisonOut) (pin := Fir.UBByOwnRules) (pin := Fir.ReturnsOnDefined) (pin := Fir.OpTotal) (pin := Fir.OpMonotone) (pin := Fir.Core.Op.denote?) (pin := Fir.Core.ashrValues) (fingerprint := "10525770451660545999")
*Theorem: $`\mathsf{ashr}` is lawful.* For every width $`w`, under fir's
execution rules, $`\mathsf{ashr}_w` propagates poison, returns a result
on defined operands, and is total and monotone, for the reasons that
$`\mathsf{shl}` is.
:::
