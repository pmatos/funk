import VersoManual
import Fir.Core.EffectUnlawful
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on a declaration that the obligations
reject, which renders `Fir.Core.EffectUnlawful` (ADR-2026-11-05-2012).
Each block explains declarations of that module and pins their
fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "A declaration that the obligations reject: readable blocks" =>

:::moduleDocs (fingerprint := "5842347595972846721")
:::

:::readable Fir.Core.Unlawful.sdivNoUB Fir.Core.Unlawful.sdivNoUB_unlawful (pin := Fir.Core.Op.effects) (pin := Fir.NeverUB) (pin := Fir.Core.memDenoteAt) (fingerprint := "10094827677507255900")
*Definition and theorem: the obligations reject a wrong declaration.* The
declaration $`\mathrm{eff}'` gives each core op its set but
$`\mathsf{sdiv}`, which it declares without $`\mathsf{mayUB}`, keeping
only $`\mathsf{mayPoison}` under $`\mathsf{exact}`. Over the
core's own semantics with memory, a dialect lawful in its effects under
$`\mathrm{eff}'` would make $`\mathsf{sdiv}_8` never end in UB, with
memory and so from the empty memories, but $`\mathsf{sdiv}_8(1, 0)` is UB,
so no such dialect exists: the obligations reject the declaration. The
soundness proofs have teeth.
:::
