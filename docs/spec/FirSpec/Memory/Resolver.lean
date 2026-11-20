import VersoManual
import Fir.Memory.Resolver
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on address resolvers, which renders
`Fir.Memory.Resolver` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Address resolvers: readable blocks" =>

:::moduleDocs (fingerprint := "4017797863689267341")
:::

:::readable Fir.Memory.Resolver Fir.Memory.Resolver.canonical (pin := Fir.Memory.Place) (fingerprint := "1042354504430014978")
*Definition: an address resolver.* An address resolver $`k` for a memory
maps the number $`c` of integers the run has turned back into pointers
before, the places of the memory's blocks and an address $`z` to the
allocation it proposes, $`k(c, \mathrm{places}(M), z)`, or to none. It
sees the count, so each call may pick differently (the human's ruling of
2026-11-20 on #232, question A). The canonical resolver, which `fir-ref`
follows, proposes none.
:::

:::readable Fir.Memory.Memory.holds Fir.Memory.Memory.within (fingerprint := "8291348009940736794")
*Definitions: the allocations that hold an address.* The allocation $`a`
of $`M`, with $`M[a] = (k, \alpha, \vec{x}, \ell, y^?)`, holds the address
$`z` when it is live, has an address $`y`, and

$$`y \le z \le y + |\vec{x}|`

its end included (the human's ruling of 2026-11-18 on #232, Q3). A freed
allocation, or one with no address, holds none. The address $`z` is
_within_ $`a` when $`a` holds both $`z` and $`z + 1`: it is the address of
one of its units.
:::

:::readable Fir.Memory.Memory.pick Fir.Memory.Memory.resolve Fir.Memory.Memory.rebuild (pin := Fir.Memory.Memory.addrOf) (fingerprint := "16933549399704389872")
*Definitions: the allocation picked, and the pointer.* The memory model's
own pick for $`z` is the first allocation, in the order they were made,
that $`z` is within, and when there is none, the first that holds $`z`:
the one whose end it is. It is `fir-ref`'s choice, not a rule of the
spec. On the proposal $`a^?`,

$$`\mathrm{resolve}_M(z, a^?) = \begin{cases} a & \text{if } a^? = a \text{ and } a \text{ holds } z \\ \mathrm{pick}_M(z) & \text{otherwise} \end{cases}`

which is none when no allocation holds $`z`. The pointer that $`z`
becomes in the allocation $`a` with the address $`y` is $`(a, z - y)`,
and with no allocation $`(\bot, z)`: a pointer with no provenance, through
which every access is UB.
:::

:::readable Fir.Memory.Memories.fromAddr (pin := Fir.Memory.Memories) (fingerprint := "11215263979195153777")
*Definition: turning an integer back into a pointer.* Turning the integer
$`i` of $`P` bits of the memory $`x` of $`S` back into a pointer, under the
resolver $`k`, with $`z` the value of $`i` and $`c` the count of $`S`,
gives the pointer that $`z` becomes in
$`\mathrm{resolve}_{S(x)}(z, k(c, \mathrm{places}(S(x)), z))`, and the
memories $`S` with the count $`c + 1`. It never fails.
:::
