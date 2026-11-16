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

:::moduleDocs (fingerprint := "11415205262792294873")
:::

:::readable Fir.Memory.alignUp (fingerprint := "5903328988636615743")
*Definition: aligning up.* For $`\alpha > 0`, $`\lceil c \rceil_\alpha`
is the least multiple of $`\alpha` that is at least $`c`:

$$`\lceil c \rceil_\alpha = \left\lfloor \frac{c + \alpha - 1}{\alpha} \right\rfloor \cdot \alpha`

So $`\lceil 1 \rceil_4 = 4`, $`\lceil 5 \rceil_4 = 8` and
$`\lceil 7 \rceil_1 = 7`. For $`\alpha = 0` it is $`c`: no address but 0 is
a multiple of 0, so an allocation aligned to 0 gets no address anyway.
:::

:::readable Fir.Memory.Block.leavesRoom Fir.Memory.roomFrom (fingerprint := "731093680196006974")
*Definition: leaving room.* A block $`(k, \alpha, \vec{x}, \ell, y^?)`
leaves room for $`n` units from the address $`x` when it is freed, or has
no address, or its addresses and those of the new range do not overlap:

$$`\ell = \mathsf{false} \;\lor\; y^? = \bot \;\lor\; x + n \le y \;\lor\; y + |\vec{x}| \le x`

The blocks of a memory but the allocation $`a` leave room when each of
them does. A freed block always leaves room, so its addresses may be given
again.
:::

:::readable Fir.Memory.Block.giveAddr (fingerprint := "15790123385326876867")
*Definition: giving a block an address.* A block with no address gets
$`x`; a block that has one keeps it:

$$`\mathrm{give}_x(k, \alpha, \vec{x}, \ell, \bot) = (k, \alpha, \vec{x}, \ell, x) \qquad \mathrm{give}_x(k, \alpha, \vec{x}, \ell, y) = (k, \alpha, \vec{x}, \ell, y)`
:::

:::readable Fir.Memory.Memory.addrOf (fingerprint := "1378434035811052063")
*Definition: an allocation's address.* $`\mathrm{addr}_M(a)` is the
address of the block $`M[a]`, when $`M` has that block and it was given
one, and $`\bot` otherwise.
:::

:::readable Fir.Memory.Memory.fits (fingerprint := "3303481555155894563")
*Definition: an address that fits.* In a memory $`M` whose pointers are
$`P` bits wide, the address $`x` fits the allocation $`a`, with
$`M[a] = (k, \alpha, \vec{x}, \ell, y^?)`, when

$$`0 < x \;\land\; \alpha \mid x \;\land\; x + |\vec{x}| < 2^P`

and every other block of $`M` leaves room for $`|\vec{x}|` units from
$`x`. So no allocation is at 0; every address of the allocation, and the
one past its end, is an address of the memory and not 0; and no live
allocation with an address overlaps it. No address fits an allocation
that $`M` does not have. The spec allows any address that fits.
:::

:::readable Fir.Memory.Memory.expose (fingerprint := "14914568477453096129")
*Definition: exposing an allocation.* Exposing the allocation $`a` of
$`M` at $`x` gives its block the address $`x`, unless it has one:
$`M[a] := \mathrm{give}_x(M[a])`. Nothing else changes, and an id the
memory does not have changes nothing.
:::

:::readable Fir.Memory.bumpFrom Fir.Memory.Memory.bump (fingerprint := "11435310927553796152")
*Definition: the canonical addresses.* The canonical layout lays the blocks
$`b_0, b_1, \ldots` of $`M` out in the order they were made, from the
address 1. With $`c_0 = 1`, the block $`b_i`, of alignment $`\alpha_i`
and size $`n_i`, is at

$$`\mathrm{bump}_M(i) = \lceil c_i \rceil_{\alpha_i} \qquad c_{i+1} = \mathrm{bump}_M(i) + n_i + 1`

So one address is left unused after each block. Two blocks of 4 and 2
units, aligned to 4 and 8, are at 4 and 16. The address of $`b_i` depends
only on the blocks made before it.
:::

:::readable Fir.Memory.fitAfter (fingerprint := "11893542091238316513")
*Definition: an address just after a block.* For the allocation $`a`,
aligned to $`\alpha`, $`\mathrm{after}_M(a)` walks the blocks of $`M` in
order and gives $`\lceil y + n \rceil_\alpha` for the first live block, at
$`y` and of size $`n`, for which that address fits $`a`, or $`\bot` when
there is none.
:::

:::readable Fir.Memory.Memory.canonical (fingerprint := "6253861919625802359")
*Definition: the canonical layout.* The address that the canonical layout
gives the allocation $`a` of $`M`, of alignment $`\alpha`, is the first of
these that fits $`a`:

1. its canonical address, $`\mathrm{bump}_M(a)`;
2. $`\lceil 1 \rceil_\alpha`;
3. $`\mathrm{after}_M(a)`.

It is $`\bot` when none of them fits. While every exposed allocation has
its canonical address and the layout stays below $`2^P`, the first one
fits. `fir-ref` gives addresses so (#232). The
{ref "The-fir-specification--Memory--Address-laws"}[next section] proves
that it gives an address that fits whenever any address fits.
:::
