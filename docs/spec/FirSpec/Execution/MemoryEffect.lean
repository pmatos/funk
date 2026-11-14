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

:::moduleDocs (fingerprint := "1309479453290689319")
:::

:::readable Fir.MonadMemory (fingerprint := "1309479453290689319")
*Definition: the memory effect.* A way of computing has the memory
effect, on memories named by $`X` whose units are $`u(x)` bits wide, when
it gives the memory model's four operations, each on a named memory:

* $`\mathrm{alloc}(x, k, n, \alpha)` allocates $`n` units of kind $`k`,
  aligned to $`\alpha` units, in the memory $`x`, and gives the pointer
  to the first;
* $`\mathrm{free}(x, a)` frees the allocation $`a` of $`x`;
* $`\mathrm{load}(x, p, n)` loads $`n` units of $`x` through $`p`;
* $`\mathrm{store}(x, p, \vec{y})` stores the units $`\vec{y}` to $`x`
  through $`p`.

A load or a store that faults is immediate UB (ADR-2026-11-09-1542).
:::
