import VersoManual
import Fir.Execution.MemoryEffect
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the memory effect, which renders
`Fir.Execution.MemoryEffect` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The memory effect: readable blocks" =>

:::moduleDocs (fingerprint := "8352164345079083580")
:::

:::readable Fir.MonadMemory (fingerprint := "8352164345079083580")
*Definition: the memory effect.* A way of computing has the memory
effect, on memories named by $`X` whose units are $`u(x)` bits wide, when
it gives five operations of the memory model, each on a named memory:

* $`\mathrm{alloc}(x, k, n, \alpha)` allocates $`n` units of kind $`k`,
  aligned to $`\alpha` units, in the memory $`x`, and gives the pointer
  to the first;
* $`\mathrm{free}(x, a)` frees the allocation $`a` of $`x`;
* $`\mathrm{load}(x, p, n, \alpha)` loads $`n` units of $`x` through
  $`p`, an access aligned to $`\alpha` units;
* $`\mathrm{store}(x, p, \vec{y}, \alpha)` stores the units $`\vec{y}`
  to $`x` through $`p`, an access aligned to $`\alpha` units;
* $`\mathrm{expose}(x, g, P, p)` turns $`p` into an integer of $`P` bits,
  the width of the pointers of $`x`: its allocation's address plus its
  offset, wrapped, where an allocation with no address is given one under
  the {ref "The-fir-specification--Memory--Address-policies"}[address policy]
  $`g`.

The alignment of a load or a store is the op's promise that its address
is a multiple of $`\alpha`. A load or a store that faults, misaligned
included, is immediate UB (ADR-2026-11-09-1542; the human's ruling of
2026-11-11 on #231). An exposure when no address may be given is immediate UB too
(the human's ruling of 2026-11-18 on #232, Q5).
:::
