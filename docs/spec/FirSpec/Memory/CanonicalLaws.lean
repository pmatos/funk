import VersoManual
import Fir.Memory.CanonicalLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on canonical layout laws, which renders
`Fir.Memory.CanonicalLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Canonical layout laws: readable blocks" =>

:::moduleDocs (fingerprint := "8055350114286254482")
:::

:::readable Fir.Memory.le_bumpFrom Fir.Memory.dvd_bumpFrom (pin := Fir.Memory.bumpFrom) (fingerprint := "1386793675836362666")
*Theorems: where a canonical address is.* A layout from $`c` puts every
block at $`c` or above, and a block of alignment $`\alpha > 0` at a
multiple of $`\alpha`.
:::

:::readable Fir.Memory.bumpFrom_lt Fir.Memory.Memory.bump_lt (pin := Fir.Memory.Memory.bump) (fingerprint := "4712497797334815345")
*Theorems: canonical addresses do not overlap.* For $`i < j` and a block
$`M[i]` of size $`n`, $`\mathrm{bump}_M(i) + n < \mathrm{bump}_M(j)`: the
earlier block ends, with the address after it, before the later starts.
:::

:::readable Fir.Memory.bumpFrom_append Fir.Memory.Memory.bump_alloc (fingerprint := "2598379184173479996")
*Theorems: allocating moves no canonical address.* Adding a block after
the others keeps the canonical address of each of them, so
$`\mathrm{bump}_{M'}(a) = \mathrm{bump}_M(a)` for every $`a < |M|`, where
$`M'` is $`M` after an allocation.
:::

:::readable Fir.Memory.Memory.fits_bump Fir.Memory.Memory.canonical_bump (pin := Fir.Memory.Memory.canonical) (fingerprint := "16381179846115768055")
*Theorems: the canonical address fits.* Let $`M[a]` have alignment
$`\alpha > 0` and size $`n`, and let every allocation $`j` of $`M` with
an address have $`\mathrm{bump}_M(j)` as its address. If
$`\mathrm{bump}_M(a) + n \le hi`, then $`\mathrm{bump}_M(a)` fits $`a`:
blocks made before $`a` end before it, and blocks made after start after
it. The canonical layout then gives $`\mathrm{bump}_M(a)`.
:::

:::readable Fir.Memory.reuseWitness Fir.Memory.reuseWitness_reuses Fir.Memory.addresses_not_fresh (fingerprint := "2450235480177967124")
*Theorems: addresses are not fresh.* In the memory of the witness, an
allocation of 4 bytes aligned to 4 is given the address 4 and freed, then
a second one like it is made. The first has the address 4 and is freed,
the address 4 fits the second with 64-bit pointers under the strictest
reading of the bounds, and exposing the
second at 4 gives it the address 4. So the spec does not imply that a
freed allocation's address is never given to a later allocation:

$$`\lnot\, \forall M, lo, hi, a < a', z.\ \mathrm{addr}_M(a) = z \land M[a]\ \text{freed} \implies \lnot\, \mathrm{fits}_M(a', z)`

No law may assume fresh addresses, since native stack slots are reused
(the human's ruling of 2026-11-10 on #232).
:::
