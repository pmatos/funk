import VersoManual
import Fir.Core.EffectLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the core dialect's effect
obligations, which renders `Fir.Core.EffectLaws` (ADR-2026-11-05-2012).
Each block explains declarations of that module and pins their
fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "The core dialect's effect obligations: readable blocks" =>

:::moduleDocs (fingerprint := "14473149069114112062")
:::

:::readable Fir.Core.Op.neverUB_all (pin := Fir.Core.Op.effects) (pin := Fir.NeverUB) (fingerprint := "5074657499700953264")
*Theorem: each core op that does not declare may-UB never ends in UB.*
Every core op but $`\mathsf{sdiv}`, $`\mathsf{udiv}`, $`\mathsf{srem}`,
$`\mathsf{urem}` and $`\mathsf{cond\_br}` never ends in UB, at every
width. Each rule gives its result at once, $`\mathsf{freeze}` after
choosing bits, and $`\mathsf{br}` and $`\mathsf{ret}` go to their
successor or return. $`\mathsf{call}` has no rule of its own, so it has no
outcome by one.
:::

:::readable Fir.Core.defined₁ Fir.Core.defined₂ Fir.Core.not_any_of_ne (pin := Fir.HVector.Any) (pin := Fir.Core.Ty.IsPoison) (fingerprint := "16379849913816239761")
*Theorems: defined operands hold values.* An operand vector of one or two
integers with no poison element holds values: $`(v)` is
$`(\mathsf{value}~x)` for some $`x`, and $`(v_1, v_2)` is
$`(\mathsf{value}~x, \mathsf{value}~y)`. A vector of one integer that is
not poison has no poison element.
:::

:::readable Fir.Core.ruleOfEv_divEv_defined (pin := Fir.Core.divEv) (pin := Fir.Core.ruleOfEv) (fingerprint := "3900238260210989617")
*Theorem: a division whose quotient is defined makes no poison.* If the
quotient $`q(x, y)` is a value for all $`x` and $`y`, then on two values
$`\mathsf{value}~x` and $`\mathsf{value}~y` the division with that
quotient, when it gives a result, gives a value.
:::

:::readable Fir.Core.flags_none (fingerprint := "9505051277240368478")
*Theorem: an instance of $`\mathsf{add}`, $`\mathsf{sub}` or
$`\mathsf{mul}` that does not declare $`\mathsf{mayPoison}` has no flags.*
Its flags $`f` are neither $`\mathsf{nuw}` nor $`\mathsf{nsw}`.
:::

:::readable Fir.Core.Op.makesNoPoison_all (pin := Fir.Core.Op.effects) (pin := Fir.MakesNoPoison) (fingerprint := "4743314408651579304")
*Theorem: each core op that does not declare $`\mathsf{mayPoison}` makes no
poison.* On operands with no poison, $`\mathsf{const}`, $`\mathsf{add}`,
$`\mathsf{sub}` and $`\mathsf{mul}` without flags, $`\mathsf{sdiv}` and
$`\mathsf{udiv}` without $`\mathsf{exact}`, $`\mathsf{srem}`,
$`\mathsf{urem}`, the bitwise ops, $`\mathsf{icmp}`, $`\mathsf{select}`,
the width changes and $`\mathsf{freeze}` give defined results, at every
width. $`\mathsf{select}` chooses one of its defined operands, and
$`\mathsf{freeze}` gives bits. $`\mathsf{call}` gives no result by a rule
of its own, and the terminators give none.
:::

:::readable Fir.Core.Op.notControl_all (pin := Fir.Core.Op.effects) (fingerprint := "8544232680631904298")
*Theorem: each core op that does not declare $`\mathsf{control}` is not a
terminator.* The core terminators are $`\mathsf{br}`,
$`\mathsf{cond\_br}` and $`\mathsf{ret}`, and each declares
$`\mathsf{control}`.
:::

:::readable Fir.Core.lawfulDialectEffects (pin := Fir.LawfulDialectEffects) (fingerprint := "12820253841310700615")
*Theorem: the core dialect is lawful in its effects.* Every effect that a
core op leaves out, it does not have: the three theorems above, for every
core op instance. So a pass may rely on the core ops' effect sets
(ADR-2026-11-09-1541).
:::
