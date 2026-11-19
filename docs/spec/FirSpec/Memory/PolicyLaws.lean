import VersoManual
import Fir.Memory.PolicyLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on address policy laws, which renders
`Fir.Memory.PolicyLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Address policy laws: readable blocks" =>

:::moduleDocs (fingerprint := "18110770503810780608")
:::

:::readable Fir.Memory.Memory.choose_fits Fir.Memory.Memory.choose_eq_none Fir.Memory.Memory.choose_of_fits Fir.Memory.Memory.lt_of_fits (pin := Fir.Memory.Memory.choose) (fingerprint := "722093360197852963")
*Theorems: the address given fits.* Whatever the proposal, the address
given fits; none is given exactly when no address fits; and an address
that fits is given when it is proposed. An allocation that some address
fits is one of the memory.
:::

:::readable Fir.Memory.Memory.IsRefinedBy.places Fir.Memory.Memory.IsRefinedBy.choose (pin := Fir.Memory.Memory.places) (fingerprint := "6364140748173594842")
*Theorems: refinement keeps the places.* Memories that refine each other
have the same places, so a policy proposes the same address in both, and
the same address is given on the same proposal.
:::

:::readable Fir.Memory.Memories.expose_of_none Fir.Memory.Memories.expose_of_some Fir.Memory.Memories.expose_eq_none Fir.Memory.Memories.expose_cases (pin := Fir.Memory.Memories.expose) (fingerprint := "15964147305685620831")
*Theorems: what exposing gives.* Exposing $`(a, o)` when $`a` has no
address gives the address that $`\mathrm{choose}` gives, and the
memories with $`a` exposed there. When $`a` has the address $`y`, it gives
$`y + o`, wrapped, and changes nothing. It gives none exactly when $`a`
has no address and no address between $`1` and $`2^P - 1` fits it. So
exposing either changes nothing, or gives an allocation that had no
address one that fits.
:::

:::readable Fir.Memory.Memories.expose_of_fits Fir.Memory.Memories.expose_expose (fingerprint := "6403182355404188503")
*Theorems: every address that fits, once.* Every address $`y` that fits an
allocation with no address is the one given by the policy that proposes
$`y`. So the runs of every policy together give each address that the spec
allows. Exposing the same pointer again, under any policy, gives the same
integer and changes nothing.
:::

:::readable Fir.Memory.Memories.IsRefinedBy.expose (fingerprint := "9620125716848926687")
*Theorem: exposing keeps refinement.* Exposing the same pointer under the
same policy in memories $`S \sqsubseteq S'` gives none in both, or the same
integer in both with memories that refine each other.
:::
