import VersoManual
import Fir.Execution.ObserveEnd
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the end of a return, which renders
`Fir.Execution.ObserveEnd` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The end of a return: readable blocks" =>

:::moduleDocs (fingerprint := "17341858152562055603")
:::

:::readable Fir.AddrRule Fir.AddrRule.ignore Fir.AddrRule.same Fir.AddrRule.exposed (fingerprint := "15094722826430448788")
*Definition: an address rule.* An address rule $`\approx` is a reflexive
and transitive relation on the addresses of two allocations that the
renaming relates, each $`\bot` until its allocation is exposed. The laws
of the end of a return hold for each such rule. Three rules are defined:

* $`\mathsf{ignore}`: every two addresses match;
* $`\mathsf{same}`: two addresses match when they are equal, as
  refinement of blocks compares them;
* $`\mathsf{exposed}`: two addresses match when both are $`\bot` or
  neither is.

The spec takes $`\mathsf{ignore}`: the end of a return does not compare
addresses, and an address is seen only through the integers a run shows.
The human ruled this on 2026-11-20, on #233. Rejected: $`\mathsf{same}`,
under which a pass could not move an exposed allocation.
:::

:::readable Fir.Memory.Block.SeenIn Fir.Memory.Block.OptSeenIn (fingerprint := "785370159542493421")
*Definition: an allocation seen in another.* The block $`b` of the source
is seen in the block $`b'` of the target, its pointers replaced by $`f`,
when both have the same kind, alignment, liveness and size, $`b.\mathrm{addr}
\approx b'.\mathrm{addr}`, and, while $`b` is live, the units of $`b` with
their pointers replaced by $`f` are refined by those of $`b'`, one by one.
An allocation is seen in another when both are blocks, the first seen in the
second, or neither is an allocation the run made.
:::

:::readable Fir.End Fir.End.SeenUnder (pin := Fir.End.instHRefinement) (fingerprint := "4945845669367599135")
*Definition: the end of a return.* The end of a return is a triple
$`\langle \vec{v}, S, E\rangle` of the returned values, the memories, and
the list of the allocations that escaped.

*Definition: refinement of the ends of returns.* $`\langle \vec{v}, S,
E\rangle \sqsubseteq \langle \vec{v}', S', E'\rangle` when some one-to-one
renaming $`R` shows the first in the second:

* $`|E| = |E'|`, and at each place $`k`, $`E_k = (x, a)` and $`E'_k = (x,
  a')` with $`R_x(a) = a'`;
* $`R` covers each pointer of $`\vec{v}`, and $`R^{S}(\vec{v}) \sqsubseteq
  \vec{v}'`;
* for each $`R_x(a) = a'`, the allocation $`a` of $`S_x` is seen in the
  allocation $`a'` of $`S'_x`, its pointers replaced by $`R^S`, and $`R`
  covers each pointer of its units while it is live.

So the world's handles keep their places, a dangling pointer of the source
is poison wherever it is, and the memory that no observer reaches is never
compared.
:::

:::readable Fir.ObservedEnd (fingerprint := "3012597159288658516")
*Definition: the end of a return, as the spec compares it.* The spec
compares the ends of returns by the address rule $`\mathsf{ignore}`, so
the addresses of the allocations the renaming relates are never compared.
:::

:::readable Fir.End.Reachable Fir.End.SeenUnder.reachable (fingerprint := "3270551615548019583")
*Definition: what an observer reaches.* An allocation is reachable from the
end of a return when it escaped; when a returned pointer that is not
dangling points into it; or when a pointer that is not dangling, held by a
unit of a live reachable allocation, points into it.

*Theorem: a renaming renames what an observer reaches.* A renaming that
shows the end of a return in another renames each reachable allocation.
:::
