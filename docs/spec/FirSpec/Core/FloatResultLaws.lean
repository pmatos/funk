import VersoManual
import Fir.Core.FloatResultLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on what a float result may be, which
renders `Fir.Core.FloatResultLaws` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Float result obligations: readable blocks" =>

:::moduleDocs (fingerprint := "12171358981833708055")
:::

:::readable Fir.Core.anyNaN_iff Fir.Core.anySign_iff Fir.Core.flipSign_zero (pin := Fir.Core.anyNaN) (pin := Fir.Core.anySign) (fingerprint := "8297353477926480975")
*Theorem: the choices of a NaN and of a sign.* In the set monad,
$`\mathrm{anynan}_{e,m}` ends with a value $`v` exactly when
$`v = \mathrm{nan}_{e,m}(c)` for some $`c \in \mathbb{B}^{m+1}`, and
$`\mathrm{anysign}_{e,m}(b)` exactly when $`v = \mathrm{flip}_{e,m}(c, b)`
for some bit $`c`. Flipping by $`c = 0` keeps $`b`.
:::

:::readable Fir.Core.operandsBreak_eq_false Fir.Core.operandsBreak_mono (pin := Fir.Core.operandsBreak) (fingerprint := "4050810589304272843")
*Theorem: breaking the flags.* No operand breaks flags that may not make
poison. Operands that break flags $`\phi'` break every $`\phi` with
$`\phi' \le \phi`.
:::

:::readable Fir.Core.Ends Fir.Core.pure_ends (fingerprint := "2944906794587738064")
*Definition: a computation that ends.* A computation of the set monad
_ends_ when it has at least one way to end, and each way it ends is a
value, never UB. A $`\mathsf{pure}` computation ends.
:::

:::readable Fir.Core.flagResult_ok Fir.Core.flagResult_some Fir.Core.floatResult_ok Fir.Core.floatResult_ends (pin := Fir.Core.flagResult) (pin := Fir.Core.floatResult) (fingerprint := "8684640785302355909")
*Theorem: a float result ends.* For every format, every operation of the
model and all flags $`\phi`, $`\mathrm{result}^\phi_{e,m}` ends, and so
does $`\mathrm{flag}_\phi`. Each way either ends is a value, and when
$`\phi` may not make poison it is defined bits: the model's, a NaN, or a
zero of either sign.
:::

:::readable Fir.Core.floatResult_defined (fingerprint := "6538437391169733287")
*Theorem: a float result without flags is defined.* With no flags,
$`\mathrm{result}^{\emptyset}_{e,m}` ends only with defined bits, since
no flag may make poison. The conversions build their results this way.
:::

:::readable Fir.Core.flagResult_drop Fir.Core.floatResult_drop (pin := Fir.Core.FastMath.Le) (fingerprint := "1035138939333451007")
*Theorem: a flag only adds results.* Let $`\phi' \le \phi`. Every value
$`v` that $`\mathrm{result}^{\phi'}_{e,m}` may give on operands,
$`\mathrm{result}^{\phi}_{e,m}` may give on them too, or it may give
$`\mathsf{poison}`; and the same holds of $`\mathrm{flag}_{\phi'}` and
$`\mathrm{flag}_\phi`.

The cases follow the rule. Operands that break $`\phi` give poison. Else
they break $`\phi'` neither. A NaN result is poison under $`\phi` with
$`\mathsf{nnan}`; else $`\phi'` lacks it too, and both choose any NaN. An
infinity under $`\mathsf{ninf}` in $`\phi` is poison. Else, a zero under
$`\mathsf{nsz}` in $`\phi'` is a zero of either sign under $`\phi` as
well, and a value that $`\phi'` keeps is the choice $`c = 0` of
$`\mathrm{anysign}` when $`\phi` sets $`\mathsf{nsz}`.
:::

:::readable Fir.Core.anyNaN_map Fir.Core.anySign_map Fir.Core.flagResult_map Fir.Core.floatResult_map (pin := Fir.MonadMorphism.KeepsChoiceUB) (fingerprint := "16245639884445466971")
*Theorem: a float result in another monad.* For every monad morphism
$`\varphi` that
{ref "The-fir-specification--Execution--Monad-morphisms"}[keeps choice and UB],
$`\varphi` maps any NaN, a value of either sign, $`\mathrm{flag}_\phi` and
$`\mathrm{result}^\phi_{e,m}` in one monad to the same in the other: the
choice of a NaN is a choice of $`m + 1` bits in both, and the choice of a
zero's sign one bit. So run in the tree of choices that `fir-ref run`
computes in, $`\mathrm{result}^\phi_{e,m}` has the set monad's result as
its set.
:::
