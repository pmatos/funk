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

:::moduleDocs (fingerprint := "13350650603332787761")
:::

:::readable Fir.Core.Mem (fingerprint := "2052658102503826680")
*Definition: the core dialect's memories.* The core dialect has no memory
yet, so no memory has a name: the set of its memory names is empty. It
gains memories with the memory model (ADR-2026-11-09-1542).
:::

:::readable Fir.Core.Op.effects (fingerprint := "9656962251309293370")
*Definition: the effects of each core op.* For each
{ref "The-fir-specification--Abstract-syntax--Core-ops"}[core op instance]:

$$`\begin{aligned} \emptyset:\ & \mathsf{const},\ \mathsf{and},\ \mathsf{or},\ \mathsf{xor},\ \mathsf{icmp}, \\ & \mathsf{select},\ \mathsf{zext},\ \mathsf{sext},\ \mathsf{trunc},\ \mathsf{freeze},\ \mathsf{call} \end{aligned}`

$$`\mathsf{add}_f,\ \mathsf{sub}_f,\ \mathsf{mul}_f:\ \{\mathsf{poison}\} \text{ if } f \text{ has a flag, else } \emptyset`

$$`\mathsf{sdiv}_x,\ \mathsf{udiv}_x:\ \{\mathsf{mayUB}\} \cup \{\mathsf{poison} \mid x = \mathsf{exact}\}`

$$`\mathsf{srem},\ \mathsf{urem}:\ \{\mathsf{mayUB}\}`

$$`\mathsf{shl},\ \mathsf{lshr},\ \mathsf{ashr},\ \mathsf{poison}:\ \{\mathsf{poison}\}`

$$`\mathsf{br},\ \mathsf{ret}:\ \{\mathsf{control}\} \qquad \mathsf{cond\_br}:\ \{\mathsf{mayUB},\ \mathsf{control}\}`

$`\mathsf{call}`'s own rule only runs its callee, so its own set is empty;
a call has its callee's effects. The definition lists every op, with no
case for the rest, so a new core op does not build until it declares its
effects (ADR-2026-11-03-0600).
:::
