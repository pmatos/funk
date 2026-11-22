import VersoManual
import Fir.Memory.Address
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on addresses, which renders
`Fir.Memory.Address` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Addresses: readable blocks" =>

:::moduleDocs (fingerprint := "8870463966010300475")
:::

:::readable Fir.Memory.alignUp (fingerprint := "5903328988636615743")
*Definition: aligning up.* For $`\alpha > 0`, $`\lceil c \rceil_\alpha`
is the least multiple of $`\alpha` that is at least $`c`:

$$`\lceil c \rceil_\alpha = \left\lfloor \frac{c + \alpha - 1}{\alpha} \right\rfloor \cdot \alpha`

So $`\lceil 1 \rceil_4 = 4`, $`\lceil 5 \rceil_4 = 8` and
$`\lceil 7 \rceil_1 = 7`. For $`\alpha = 0` it is $`c`: no address but 0 is
a multiple of 0, so an allocation aligned to 0 fits only at 0.
:::

:::readable Fir.Memory.Block.leavesRoom Fir.Memory.roomFrom (fingerprint := "6977827549227237265")
*Definition: leaving room.* A block $`(k, \alpha, \vec{x}, \ell, y^?)`
leaves room for $`n` units from the address $`z` when it is freed, or has
no address, or its addresses and those from $`z` to $`z + n` do not
overlap:

$$`\ell = \mathsf{false} \;\lor\; y^? = \bot \;\lor\; z + n \le y \;\lor\; y + |\vec{x}| \le z`

The blocks of a memory but the allocation $`a` leave room when each of
them does. A freed block always leaves room, so its addresses may be given
again. An allocation of no units takes no address, so it may share its
address with another, as zero-sized objects may in LLVM and Rust; no op
of M1 makes one.
:::

:::readable Fir.Memory.Block.giveAddr (fingerprint := "7905469697570646947")
*Definition: giving a block an address.* A block with no address gets
$`z`; a block that has one keeps it. Either way it keeps its constness
$`c`:

$$`\mathrm{give}_z(k, \alpha, \vec{x}, \ell, \bot, c) = (k, \alpha, \vec{x}, \ell, z, c) \qquad \mathrm{give}_z(k, \alpha, \vec{x}, \ell, y, c) = (k, \alpha, \vec{x}, \ell, y, c)`
:::

:::readable Fir.Memory.Memory.addrOf (fingerprint := "1378434035811052063")
*Definition: an allocation's address.* $`\mathrm{addr}_M(a)` is the
address of the block $`M[a]`, when $`M` has that block and it was given
one, and $`\bot` otherwise.
:::

:::readable Fir.Memory.Memory.fits (fingerprint := "15420125501033846395")
*Definition: an address that fits.* Between the bounds $`lo` and $`hi`,
the address $`z` fits the allocation $`a` of $`M`, with
$`M[a] = (k, \alpha, \vec{x}, \ell, y^?)`, when

$$`lo \le z \;\land\; \alpha \mid z \;\land\; z + |\vec{x}| \le hi`

and every other block of $`M` leaves room for $`|\vec{x}|` units from
$`z`. No address fits an allocation that $`M` does not have. The spec
allows any address that fits, and a freed allocation also any aligned
address between the bounds (the section on address policies). Every law
holds at every bound, and a run exposes in a memory of $`P`-bit pointers
with $`lo = 1` and $`hi = 2^P - 1` (the human's ruling of 2026-11-18 on
#232, Q4): no
allocation is at 0, and the address one past its end is an address of the
memory and not 0.
:::

:::readable Fir.Memory.Memory.expose (fingerprint := "14914568477453096129")
*Definition: exposing an allocation.* Exposing the allocation $`a` of
$`M` at $`z` gives its block the address $`z`, unless it has one:
$`M[a] := \mathrm{give}_z(M[a])`. Nothing else changes, and an id the
memory does not have changes nothing.
:::

:::readable Fir.Memory.bumpFrom Fir.Memory.Memory.bump (fingerprint := "4710689305863777439")
*Definition: the canonical addresses.* The canonical layout lays the blocks
$`b_0, b_1, \ldots` of $`M` out in the order they were made, from $`lo`.
With $`c_0 = lo`, the block $`b_i`, of alignment $`\alpha_i` and size
$`n_i`, is at

$$`\mathrm{bump}_M(i) = \lceil c_i \rceil_{\alpha_i} \qquad c_{i+1} = \mathrm{bump}_M(i) + n_i + 1`

So one address is left unused after each block. From 1, two blocks of 4
and 2 units, aligned to 4 and 8, are at 4 and 16. The address of $`b_i`
depends only on the blocks made before it.
:::

:::readable Fir.Memory.lowestFrom (fingerprint := "3098750353783868438")
*Definition: the lowest candidate.* For the allocation $`a`, aligned to
$`\alpha`, $`\mathrm{lowest}_M(a, z^?, \vec{c})` walks the blocks
$`\vec{c}` in order, starting from the address $`z^?` found so far, if
any. For each live block of $`\vec{c}` at $`y`, of size $`n`, for which
$`\lceil y + n \rceil_\alpha` fits $`a`, it keeps the lower of that
address and the one found so far. It gives the one found at the end.
:::

:::readable Fir.Memory.Memory.lowestFit (fingerprint := "63834399341398295")
*Definition: the lowest address that fits.* For the allocation $`a` of
$`M`, aligned to $`\alpha`, $`\mathrm{lowest}_M(a)` starts from
$`\lceil lo \rceil_\alpha` when it fits, and walks every block of $`M`.
The {ref "The-fir-specification--Memory--Address-laws"}[next section]
proves that it is the lowest address that fits $`a`, and $`\bot` when no
address fits.
:::

:::readable Fir.Memory.Memory.canonical (fingerprint := "15824697222970042406")
*Definition: the canonical layout.* The address that the canonical layout
gives the allocation $`a` of $`M` is its canonical address,
$`\mathrm{bump}_M(a)`, when that fits $`a`, and the lowest address that
fits $`a` otherwise, or $`\bot` when none does. While every exposed
allocation has its canonical address and the layout stays below $`hi`,
the first one fits. `fir-ref` gives addresses so (#232).
:::
