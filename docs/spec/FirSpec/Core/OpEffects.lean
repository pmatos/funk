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

:::moduleDocs (fingerprint := "3484219231566044875")
:::

:::readable Fir.Core.Mem (fingerprint := "11401156343561318334")
*Definition: the core dialect's memories.* The core dialect names each
memory of a module by its number, a natural number: memory $`N` is the
memory of the pointer type $`\mathsf{ptr}\langle N \rangle`
(ADR-2026-11-09-1542), and memory $`0` is the default memory, which every
module has. The module's data layout declares the others by number
(ADR-2026-11-12-1821;
{ref "The-fir-specification--Validation--The-data-layout___s-rules"}[the data layout's rules]).
$`\mathsf{alloca}` names the memory of its result in its effects, and
$`\mathsf{load}`, $`\mathsf{store}`, $`\mathsf{memcpy}`,
$`\mathsf{memmove}`, $`\mathsf{memset}`, $`\mathsf{ptr\_expose}` and
$`\mathsf{ptr\_from\_int}` the memory of their pointers; no other core op
names a memory.
:::

:::readable Fir.Core.Op.effects (fingerprint := "16705256922747536990")
*Definition: the effects of each core op.* For each
{ref "The-fir-specification--Abstract-syntax--Core-ops"}[core op instance]:

$$`\begin{aligned} \emptyset:\ & \mathsf{const},\ \mathsf{and},\ \mathsf{or},\ \mathsf{xor},\ \mathsf{icmp}, \\ & \mathsf{select},\ \mathsf{zext},\ \mathsf{sext},\ \mathsf{trunc},\ \mathsf{freeze},\ \mathsf{call}, \\ & \mathsf{bitcast}^{\to \mathsf{i}},\ \mathsf{bitcast}^{\mathsf{i} \to},\ \mathsf{sitofp},\ \mathsf{uitofp}, \\ & \mathsf{fpext},\ \mathsf{fptrunc},\ \mathsf{ptradd},\ \mathsf{fieldaddr} \end{aligned}`

$$`\mathsf{fcmp}_\phi,\ \mathit{fbin}_\phi,\ \mathit{funary}_\phi,\ \mathsf{fma}_\phi:\ \{\mathsf{mayPoison}\} \text{ if } \phi \text{ sets } \mathsf{nnan} \text{ or } \mathsf{ninf}, \text{ else } \emptyset`

$$`\mathsf{add}_f,\ \mathsf{sub}_f,\ \mathsf{mul}_f:\ \{\mathsf{mayPoison}\} \text{ if } f \text{ has a flag, else } \emptyset`

$$`\mathsf{sdiv}_x,\ \mathsf{udiv}_x:\ \{\mathsf{mayUB}\} \cup \{\mathsf{mayPoison} \mid x = \mathsf{exact}\}`

$$`\mathsf{srem},\ \mathsf{urem}:\ \{\mathsf{mayUB}\}`

$$`\mathsf{shl},\ \mathsf{lshr},\ \mathsf{ashr},\ \mathsf{poison},\ \mathsf{fptosi},\ \mathsf{fptoui}:\ \{\mathsf{mayPoison}\}`

$$`\mathsf{br},\ \mathsf{ret}:\ \{\mathsf{control}\} \qquad \mathsf{cond\_br},\ \mathsf{unreachable}:\ \{\mathsf{mayUB},\ \mathsf{control}\}`

$$`\mathsf{alloca}_N:\ \{\mathsf{allocates}(N)\} \qquad \mathsf{load}_N:\ \{\mathsf{reads}(N),\ \mathsf{mayUB},\ \mathsf{mayPoison}\}`

$$`\mathsf{store}_N,\ \mathsf{memset}_N:\ \{\mathsf{writes}(N),\ \mathsf{mayUB}\} \qquad \mathsf{memcpy}_N,\ \mathsf{memmove}_N:\ \{\mathsf{reads}(N),\ \mathsf{writes}(N),\ \mathsf{mayUB}\}`

$$`\mathsf{ptr\_expose}_N:\ \{\mathsf{reads}(N),\ \mathsf{allocates}(N),\ \mathsf{mayUB}\} \qquad \mathsf{ptr\_from\_int}_N:\ \{\mathsf{reads}(N),\ \mathsf{allocates}(N)\}`

The load and store of a pointer, $`\mathsf{load}_N~o~\mathsf{ptr}\langle M \rangle~a`
and $`\mathsf{store}_N~o~\mathsf{ptr}\langle M \rangle~a` (`loadPtr` and
`storePtr` in the Lean), have the sets of $`\mathsf{load}_N` and
$`\mathsf{store}_N`: the memory is $`N`, the pointer's they access
through, never the memory $`M` of the pointer they load or store. So do
the load and store of a float,
$`\mathsf{load}_N~o~\mathsf{float}\langle e,m \rangle~a` and
$`\mathsf{store}_N~o~\mathsf{float}\langle e,m \rangle~a` (`loadFloat`
and `storeFloat`).

$`\mathsf{const}` here is a constant of any type, an integer's or a
float's. The float ops without $`\mathsf{nnan}` and $`\mathsf{ninf}`
are pure: a NaN result and a zero of either sign under $`\mathsf{nsz}`
are defined values, and M1 has no floating-point exceptions
(ADR-2026-11-09-1549). So are the two bit casts, which keep their
operand's bits, the two conversions from integers, whose result is never
a NaN, and the two conversions between formats, whose NaN result is a
defined value too. The two conversions to integers may produce poison: an
integer that the width does not hold, an infinity or a NaN gives poison.
$`\mathsf{alloca}_N` allocates in the memory $`N` of its result, and does
nothing else that an effect names: it is never UB and gives a defined
pointer, and the frame of its call frees the allocation.
$`\mathsf{load}_N` reads the memory $`N` of its pointer, may be UB, on a
poison pointer or an access that faults, and may give poison, for units
that are not an encoding of its type, such as fresh memory's or a punned
load's.
$`\mathsf{store}_N` writes the memory $`N` of its pointer and may be UB,
on a poison pointer or an access that faults. It reads no memory, its own
included, since whether it faults depends on the allocations and not on
their units, and it gives no result, so it makes no poison.
$`\mathsf{memcpy}_N` and $`\mathsf{memmove}_N` read and write the memory
$`N` of their pointers and may be UB, on a poison pointer, an access that
faults and, for $`\mathsf{memcpy}_N`, ranges that partly overlap, unless
the length is 0. They give no result, so they make no poison, though they
may carry poison units. $`\mathsf{memset}_N` writes the memory $`N` of its
pointer and may be UB, on a poison pointer or an access that faults,
unless the length is 0; as $`\mathsf{store}_N`, it reads no memory and
makes no poison, though it may write poison units.
$`\mathsf{ptr\_expose}_N` and $`\mathsf{ptr\_from\_int}_N` read the
memory $`N` of their pointer, since their results depend on its addresses,
and allocate in it: exposing gives an allocation an address, which counts
as allocating (the human's ruling of 2026-11-20 on #232, question B), and
turning an integer back into a pointer counts the call, which until the
human rules on it declares an allocation too, an over-approximation.
$`\mathsf{ptr\_expose}_N` may be UB, on a poison pointer or when no
address may be given; $`\mathsf{ptr\_from\_int}_N` never is. On defined
operands neither gives poison.
$`\mathsf{call}`'s own rule only runs its callee, so its own set is empty;
a call has its callee's effects. The definition lists every op, with no
case for the rest, so a new core op does not build until it declares its
effects (ADR-2026-11-03-0600).
:::
