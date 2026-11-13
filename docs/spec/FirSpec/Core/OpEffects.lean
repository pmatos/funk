import VersoManual
import Fir.Core.OpEffects
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the effects of the core ops, which
renders `Fir.Core.OpEffects` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Core effects: readable blocks" =>

:::moduleDocs (fingerprint := "6643374963358279061")
:::

:::readable Fir.Core.Mem (fingerprint := "11401156343561318334")
*Definition: the core dialect's memories.* The core dialect names each
memory of a module by its number, a natural number: memory $`N` is the
memory of the pointer type $`\mathsf{ptr}\langle N \rangle`
(ADR-2026-11-09-1542), and memory $`0` is the default memory, which every
module has. The module's data layout declares the others by number
(ADR-2026-11-12-1821;
{ref "The-fir-specification--Validation--The-data-layout___s-rules"}[the data layout's rules]).
No core op names a memory in its effects yet.
:::

:::readable Fir.Core.Op.effects (fingerprint := "7977178472251343384")
*Definition: the effects of each core op.* For each
{ref "The-fir-specification--Abstract-syntax--Core-ops"}[core op instance]:

$$`\begin{aligned} \emptyset:\ & \mathsf{const},\ \mathsf{and},\ \mathsf{or},\ \mathsf{xor},\ \mathsf{icmp},\ \mathsf{fcmp}, \\ & \mathit{fbin},\ \mathit{funary},\ \mathsf{fma}, \\ & \mathsf{select},\ \mathsf{zext},\ \mathsf{sext},\ \mathsf{trunc},\ \mathsf{freeze},\ \mathsf{call}, \\ & \mathsf{bitcast}^{\to \mathsf{i}},\ \mathsf{bitcast}^{\mathsf{i} \to},\ \mathsf{sitofp},\ \mathsf{uitofp}, \\ & \mathsf{fpext},\ \mathsf{fptrunc},\ \mathsf{ptradd} \end{aligned}`

$$`\mathsf{add}_f,\ \mathsf{sub}_f,\ \mathsf{mul}_f:\ \{\mathsf{mayPoison}\} \text{ if } f \text{ has a flag, else } \emptyset`

$$`\mathsf{sdiv}_x,\ \mathsf{udiv}_x:\ \{\mathsf{mayUB}\} \cup \{\mathsf{mayPoison} \mid x = \mathsf{exact}\}`

$$`\mathsf{srem},\ \mathsf{urem}:\ \{\mathsf{mayUB}\}`

$$`\mathsf{shl},\ \mathsf{lshr},\ \mathsf{ashr},\ \mathsf{poison}:\ \{\mathsf{mayPoison}\}`

$$`\mathsf{br},\ \mathsf{ret}:\ \{\mathsf{control}\} \qquad \mathsf{cond\_br},\ \mathsf{unreachable}:\ \{\mathsf{mayUB},\ \mathsf{control}\}`

$`\mathsf{const}` here is a constant of any type, an integer's or a
float's. The float arithmetic is pure: a NaN result is a defined
value, and M1 has no floating-point exceptions (ADR-2026-11-09-1549). So
are the two bit casts, which keep their operand's bits, the two
conversions from integers, whose result is never a NaN, and the two
conversions between formats, whose NaN result is a defined value too.
$`\mathsf{call}`'s own rule only runs its callee, so its own set is empty;
a call has its callee's effects. The definition lists every op, with no
case for the rest, so a new core op does not build until it declares its
effects (ADR-2026-11-03-0600).
:::
