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

:::moduleDocs (fingerprint := "9629907209478465606")
:::

:::readable Fir.Memory.alignUp_le (fingerprint := "13573724838874798906")
*Theorem: aligning up.* A multiple of $`\alpha` that is at least $`c` is
at least $`\lceil c \rceil_\alpha`.
:::

:::readable Fir.Memory.Memory.admits_of_fits Fir.Memory.Memory.lt_of_admits Fir.Memory.Memory.fallback_admits Fir.Memory.Memory.admits_alignUp Fir.Memory.Memory.fallback_eq_none (pin := Fir.Memory.Memory.admits) (pin := Fir.Memory.Memory.fallback) (fingerprint := "13589898158671568480")
*Theorems: the fallback.* An address that fits may be given, and only to
an allocation of the memory. The fallback may be given. When no address
fits a freed allocation but some may be given, $`\lceil lo \rceil_\alpha`
may be given, so the fallback is none exactly when no address may be
given.
:::

:::readable Fir.Memory.Memory.choose_admits Fir.Memory.Memory.choose_eq_none Fir.Memory.Memory.choose_of_admits (pin := Fir.Memory.Memory.choose) (fingerprint := "10701143210617362353")
*Theorems: the address given may be given.* Whatever the proposal, the
address given may be given; none is given exactly when no address may be;
and an address that may be given is the one given when it is proposed.
:::

:::readable Fir.Memory.Memory.IsRefinedBy.places Fir.Memory.Memory.IsRefinedBy.admits Fir.Memory.Memory.IsRefinedBy.choose (pin := Fir.Memory.Memory.places) (fingerprint := "3364662152324875263")
*Theorems: refinement keeps the places.* Memories that refine each other
have the same places, so a policy proposes the same address in both, the
same addresses may be given in both, and the same address is given on the
same proposal.
:::

:::readable Fir.Memory.Memories.expose_of_some Fir.Memory.Memories.expose_of_none Fir.Memory.Memories.expose_transfer Fir.Memory.Memories.expose_eq_none Fir.Memory.Memories.expose_cases (pin := Fir.Memory.Memories.expose) (fingerprint := "6110478029810255681")
*Theorems: what exposing gives.* Exposing $`(a, o)` when $`a` has the
address $`y` gives $`y + o`, wrapped, and changes nothing. When $`a` has no
address, it gives the address that $`\mathrm{choose}` gives, and the
memories with $`a` exposed there. Exposing in two memories of a run with
the same memory $`x` gives the same integer, or none in both, and keeps
both or replaces $`x` in both by the same memory. Exposing gives none
exactly when $`a` is an allocation of $`x` with no address and no address
from $`1` to $`2^P - 1` may be given to it. So exposing either changes
nothing, or gives an allocation that had no address one that may be given.
:::

:::readable Fir.Memory.Memories.expose_of_admits Fir.Memory.Memories.expose_expose (fingerprint := "23814475695963899")
*Theorems: every address that may be given, once.* At each exposure, every
address $`y` that may be given to an allocation with no address is the one
given under the policy that proposes $`y`. Exposing the same pointer again,
under any policy, gives the same integer and changes nothing.
:::

:::readable Fir.Memory.Memories.IsRefinedBy.expose (fingerprint := "9620125716848926687")
*Theorem: exposing keeps refinement.* Exposing the same pointer under the
same policy in memories $`S \sqsubseteq S'` gives none in both, or the same
integer in both with memories that refine each other.
:::
