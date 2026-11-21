import VersoManual
import Fir.Memory.Policy
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on address policies, which renders
`Fir.Memory.Policy` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Address policies: readable blocks" =>

:::moduleDocs (fingerprint := "822173333255341496")
:::

:::readable Fir.Memory.Place Fir.Memory.Memory.places (pin := Fir.Memory.Block.shape) (fingerprint := "12043594272512453898")
*Definition: what a policy sees.* The place of a block is its shape, its
kind, alignment, size and liveness, with its address $`y^?`. The places of
a memory $`M` are the places of its blocks, in the order the allocations
were made. They hold no unit, so memories that refine each other have the
same places.
:::

:::readable Fir.Memory.Policy Fir.Memory.Policy.canonical (fingerprint := "11519449038154744995")
*Definition: an address policy.* An address policy $`g` for a memory maps
the places of its blocks and an allocation $`a` to the address it
proposes for $`a`, or to none. The canonical policy proposes none.
:::

:::readable Fir.Memory.Memory.admits Fir.Memory.Memory.fallback Fir.Memory.Memory.choose (pin := Fir.Memory.Memory.fits) (pin := Fir.Memory.Memory.canonical) (pin := Fir.Memory.alignUp) (fingerprint := "14642826520430930220")
*Definitions: the addresses that may be given, and the one given.* Between
the bounds $`lo` and $`hi`, the address $`z` may be given to the
allocation $`a` of $`M`, with $`M[a] = (k, \alpha, \vec{x}, \ell, y^?)`,
when $`z` fits $`a`, or when $`a` is freed and

$$`lo \le z \;\land\; \alpha \mid z \;\land\; z + |\vec{x}| \le hi`

No access reaches a freed allocation, and a live one may take its
addresses, so a freed one takes room from none: a dangling pointer may be
given the address of a live allocation, as a native stack slot is reused.
The human ruled this on 2026-11-20 (#232).

The fallback is the canonical address, or, when there is none, the first
multiple $`\lceil lo \rceil_\alpha` of $`\alpha` from $`lo`, when it may be
given. The address given on the proposal $`y^?` is

$$`\mathrm{choose}_M(a, y^?) = \begin{cases} y & \text{if } y^? = y \text{ and } y \text{ may be given to } a \\ \mathrm{fallback}_M(a) & \text{otherwise} \end{cases}`

which is none when no address may be given.
:::

:::readable Fir.Memory.addrHi Fir.Memory.noAddressReason (fingerprint := "17041647454500680883")
*Definitions: the bounds of a run, and the UB of exhaustion.* A memory of
$`P`-bit pointers gives addresses between $`lo = 1` and $`hi = 2^P - 1`
(the human's ruling of 2026-11-18 on #232, Q4). When no address may be
given, the run's UB gives the reason "an exposure that no address fits"
(Q5).
:::

:::readable Fir.Memory.Memories.expose (pin := Fir.Memory.Memory.addrOf) (pin := Fir.Memory.Memory.expose) (fingerprint := "7634160338223627702")
*Definition: exposing a pointer.* Exposing the pointer $`p = (a^?, o)` of
the memory $`x` of $`S`, of $`P`-bit pointers, under the policy $`g`,
gives an integer of $`P` bits and the memories after:

* with no provenance, $`(o \bmod 2^P, S)`;
* when $`a` has the address $`y`, $`((y + o) \bmod 2^P, S)`;
* when $`a` has none, and
  $`\mathrm{choose}_{S(x)}(a, g(\mathrm{places}(S(x)), a)) = y` between
  $`1` and $`2^P - 1`, $`((y + o) \bmod 2^P, S')`, where $`S'` is $`S`
  with $`a` exposed at $`y` in $`x`;
* when $`x` has no allocation $`a`, which no run makes, $`(o \bmod 2^P, S)`;
* none otherwise: no address may be given.

The remainder is taken on integers, so a negative sum wraps from the top.
:::
