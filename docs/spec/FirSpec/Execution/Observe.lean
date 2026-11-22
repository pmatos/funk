import VersoManual
import Fir.Execution.Observe
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on pointers under a renaming, which
renders `Fir.Execution.Observe` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Pointers under a renaming: readable blocks" =>

:::moduleDocs (fingerprint := "8450188009969374392")
:::

:::readable Fir.Renaming Fir.Renaming.Injective Fir.Renaming.id Fir.Renaming.comp Fir.Renaming.id_injective Fir.Renaming.Injective.comp (fingerprint := "13519277966737651583")
*Definition: a renaming.* A renaming $`R` gives, for each memory $`x` and
allocation $`a` of the source, the allocation $`R_x(a)` of the target that
$`a` is renamed to, if it is renamed. It is _one-to-one_ when
$`R_x(a) = R_x(b)` only for $`a = b`. The identity renames each allocation
to itself, and $`R_1 ; R_2` renames $`a` to $`R_2(R_1(a))`.

*Theorem: one-to-one renamings compose.* The identity is one-to-one, and so
is $`R_1 ; R_2` when $`R_1` and $`R_2` are.
:::

:::readable Fir.Memory.Memories.freed Fir.Renaming.ptr Fir.Renaming.Covers (fingerprint := "5118820785626008416")
*Definition: a pointer under a renaming.* The allocation $`a` of the memory
$`x` is _freed_ in $`S` when $`S` has it and it is not live; a pointer into
it is _dangling_. Where the memory numbered $`n` is $`\mu(n)`, the pointer
$`p` of the memory numbered $`n` of a source whose memories are $`S` is seen
under $`R` as:

$$`R^{S}_n(p) = \begin{cases} p & \text{if } p \text{ has no provenance} \\ \mathsf{poison} & \text{if } p \text{ points into an allocation freed in } S \\ p[\mathrm{prov} := R_{\mu(n)}(a)] & \text{if } p \text{ points into } a \text{ otherwise} \end{cases}`

The renaming _covers_ $`p` when it renames $`a` in the last case.
:::

:::readable Fir.HasPtrs (fingerprint := "12447194532554206250")
*Definition: values that hold pointers.* A type of values holds pointers
when each value $`v` has a list of pointers, each with the number of its
memory, and $`f(v)` replaces each pointer $`p` of the memory numbered $`n`
by $`f_n(p)`, or by poison when that is $`\mathsf{poison}`. The laws:
replacing each pointer by itself changes nothing; two replacements in turn
are one; replacing keeps refinement; replacing more pointers by poison
refines less; and a pointer that a replacement keeps, as $`q`, is in each
value that refines the result.
:::

:::readable Fir.Memory.MemUnit.ptrs Fir.Memory.MemUnit.mapPtr (pin := Fir.instHasPtrsMemUnit) (fingerprint := "5323824944280981881")
*Definition: the pointers of a unit.* A unit of memory holds the pointer of
its fragment, if it is one, with the number of the pointer's memory.
Replacing it gives the fragment of the replacement, or a poison unit.
:::

:::readable Fir.TyPointers Fir.instHasPtrsDVal (pin := Fir.instHasPtrsList) (fingerprint := "3444632649485410239")
*Definition: a dialect's values that hold pointers.* A dialect says, for
each of its types, which pointers a value holds and how they are replaced,
with the laws of values that hold pointers. A typed value holds the
pointers of its value, and a list the pointers of its elements, in order.
:::
