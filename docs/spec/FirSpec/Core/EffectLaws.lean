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

:::moduleDocs (fingerprint := "3710124410224607556")
:::

:::readable Fir.Core.Op.neverUB_all (pin := Fir.Core.Op.effects) (pin := Fir.NeverUBSetM) (fingerprint := "14270453042974384340")
*Theorem: each core op that does not declare may-UB never ends in UB in
the set monad.*
Every core op but $`\mathsf{sdiv}`, $`\mathsf{udiv}`, $`\mathsf{srem}`,
$`\mathsf{urem}`, $`\mathsf{cond\_br}` and $`\mathsf{unreachable}` never
ends in UB, at every width. Each rule gives its result at once, $`\mathsf{freeze}` after
choosing bits, and $`\mathsf{br}` and $`\mathsf{ret}` go to their
successor or return. $`\mathsf{call}` has no rule of its own, so it has no
outcome by one.
:::

:::readable Fir.Core.defined₁ Fir.Core.defined₂ Fir.Core.not_any_of_ne (pin := Fir.HVector.Any) (pin := Fir.Core.Ty.IsPoison) (fingerprint := "9970722609581778881")
*Theorems: defined operands hold values.* An operand vector of one or two
integers with no poison element holds values: $`(v)` is
$`(\mathsf{value}~x)` for some $`x`, and $`(v_1, v_2)` is
$`(\mathsf{value}~x, \mathsf{value}~y)`. A vector of one integer that is
not poison has no poison element.
:::

:::readable Fir.Core.defined₂Float Fir.Core.not_any_of_ne_float (pin := Fir.HVector.Any) (pin := Fir.Core.Ty.IsPoison) (fingerprint := "10131071272920059735")
*Theorems: defined float operands hold values.* An operand vector of two
floats of one format with no poison element holds values,
$`(\mathsf{value}~x, \mathsf{value}~y)`; and a vector of one float that
is not poison has no poison element. The proofs for $`\mathsf{fcmp}` and
the float $`\mathsf{const}` use them, as those for $`\mathsf{icmp}` and
the integer $`\mathsf{const}` use the theorems above.
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

:::readable Fir.Core.Op.makesNoPoison_all (pin := Fir.Core.Op.effects) (pin := Fir.MakesNoPoisonSetM) (fingerprint := "12947137012330194290")
*Theorem: each core op that does not declare $`\mathsf{mayPoison}` makes no
poison in the set monad.* On operands with no poison, $`\mathsf{const}`, $`\mathsf{add}`,
$`\mathsf{sub}` and $`\mathsf{mul}` without flags, $`\mathsf{sdiv}` and
$`\mathsf{udiv}` without $`\mathsf{exact}`, $`\mathsf{srem}`,
$`\mathsf{urem}`, the bitwise ops, $`\mathsf{icmp}`, $`\mathsf{fcmp}`,
$`\mathsf{select}`, the width changes, $`\mathsf{freeze}`, the float
$`\mathsf{const}`, the float arithmetic, the bit casts, the conversions from integers, the conversions between formats and $`\mathsf{ptradd}` give defined results, at every width and format. $`\mathsf{select}` chooses one of its defined operands,
$`\mathsf{freeze}` gives bits, and a float op's NaN is defined bits too. $`\mathsf{call}` gives no result by a rule
of its own, and the terminators give none.
:::

:::readable Fir.Core.Op.notControl_all (pin := Fir.Core.Op.effects) (fingerprint := "3924791895621950856")
*Theorem: each core op that does not declare $`\mathsf{control}` is not a
terminator.* The core terminators are $`\mathsf{br}`,
$`\mathsf{cond\_br}`, $`\mathsf{ret}` and $`\mathsf{unreachable}`, and each
declares
$`\mathsf{control}`.
:::

:::readable Fir.Core.instDialectMemDenote Fir.Core.liftsSetM Fir.Core.lawfulDialectEffects (pin := Fir.LawfulDialectEffects) (fingerprint := "18044563165928081954")
*Definition: the core's semantics with memory.* No core op touches memory:
at every naming of the core's memories, each op runs by its rule in the
set monad and keeps the memories
({ref "The-fir-specification--Memory--Meeting-the-memory-obligations"}[a dialect whose ops touch no memory]).
So its semantics with memory lifts its semantics in the set monad.

*Theorem: the core dialect is lawful in its effects.* Every effect that a
core op leaves out, it does not have: the three theorems above, for every
core op instance, carried from the set monad to the semantics with memory,
and the memory obligations, which every op of a dialect
whose ops touch no memory meets. So a pass may rely on the core ops'
effect sets (ADR-2026-11-09-1541).
:::

:::readable Fir.Core.Unlawful.sdivNoUB Fir.Core.Unlawful.sdivNoUB_unlawful (pin := Fir.Core.Op.effects) (pin := Fir.NeverUB) (fingerprint := "2510408745143418969")
*Definition and theorem: the obligations reject a wrong declaration.* The
declaration $`\mathrm{eff}'` gives each core op its set but
$`\mathsf{sdiv}`, which it declares without $`\mathsf{mayUB}`. A dialect
lawful in its effects under $`\mathrm{eff}'` would make $`\mathsf{sdiv}_8`
never end in UB, with memory and so from the empty memories, but
$`\mathsf{sdiv}_8(1, 0)` is UB, so no such dialect
exists: the obligations reject the declaration. The soundness proofs have
teeth.
:::
