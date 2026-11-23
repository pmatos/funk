import VersoManual
import Fir.Memory.Model
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the memory model, which renders
`Fir.Memory.Model` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "The memory model: readable blocks" =>

:::moduleDocs (fingerprint := "10907334517862453530")
:::

:::readable Fir.Memory.AllocId (fingerprint := "11401156343561318334")
*Definition: an allocation id.* An allocation $`a \in \mathbb{N}` is named
by its place in the order of its memory's allocations: the first is
$`0`, the next $`1`, and so on. An id is never reused, so a pointer into a
freed allocation can never reach a later one.
:::

:::readable Fir.Memory.Pointer (fingerprint := "18056131493388657817")
*Definition: a pointer.* A pointer is a pair $`(a^?, o)`: the allocation
$`a` it has _provenance_ for, if any, and an offset $`o \in \mathbb{Z}`
into it, counted in units.

```grammar Fir.Memory.Pointer
\mathit{ptr}
prov,offset   (a^?, o)
```

The offset may be negative or past the end of the allocation: only an
access through the pointer must be in bounds. A pointer with no
provenance, $`(\epsilon, o)`, can access no allocation.
:::

:::readable Fir.Memory.MemUnit (fingerprint := "6901355222307291109")
*Definition: a unit.* A unit of a memory whose units are $`u` bits wide
holds concrete bits, poison, or a fragment of a pointer:

```grammar Fir.Memory.MemUnit
\mathit{unit}
bits     \mathsf{bits}~b
poison   \mathsf{poison}
frag     \mathsf{frag}~m~p~i
```

* $`\mathsf{bits}~b`: the $`u` bits $`b`.
* $`\mathsf{poison}`: poison. Fresh memory holds it.
* $`\mathsf{frag}~m~p~i`: the fragment $`i` of the pointer $`p` of the
  memory $`m`. A pointer stored to memory takes several units, one fragment
  each, so a pointer copied unit by unit keeps its provenance
  (ADR-2026-11-09-1542). A unit has no type, so the fragment records the
  memory its pointer belongs to, and a pointer of one memory is never read
  back as a pointer of another (ADR-2026-11-12-2125).
:::

:::readable Fir.Memory.AllocKind (fingerprint := "15187323217587274289")
*Definition: an allocation kind.* Every allocation has a kind
(ADR-2026-11-09-1542):

```grammar Fir.Memory.AllocKind
\mathit{kind}
stack,global,heap,function   \mathsf{stack} \mid \mathsf{global} \mid \mathsf{heap} \mid \mathsf{function}
```

* $`\mathsf{stack}`: it lives until the call that made it returns
  (ADR-2026-11-09-1548).
* $`\mathsf{global}`: it lives for the whole run (ADR-2026-11-09-1546).
* $`\mathsf{heap}`: it comes from an external call, such as one to
  `malloc`.
* $`\mathsf{function}`: it is the address of a function, with no units,
  made when the run starts and live for the whole run (the human's ruling
  of 2026-11-19 on #235, Q1).

Managed memory can be added as another kind.
:::

:::readable Fir.Memory.Block (fingerprint := "5919742926676485830")
*Definition: an allocation's block.* A block is a tuple
$`(k, \alpha, \vec{x}, \ell, y^?, c)`: its kind $`k`, its alignment
$`\alpha \in \mathbb{N}`, its units $`\vec{x}`, whether it is live,
$`\ell \in \{\mathsf{true}, \mathsf{false}\}`, its address
$`y^?`, a number given once it is exposed, or $`\bot`, and whether it is
constant, $`c \in \{\mathsf{true}, \mathsf{false}\}`. Its size is $`|\vec{x}|`. The alignment
counts units: it is what every address the block may be given is a
multiple of, so that an op that accesses memory can check an access
against it (#231). The ops that allocate give a power of two, as the human
ruled on 2026-11-11, and validation rejects any other. A freed block keeps
its units, but no access may reach them. A block has no address until it
is exposed, and then keeps the one it was given (#232;
{ref "The-fir-specification--Memory--Addresses"}[addresses]). A constant
block may be read and not written: a run starts with a constant global's
block so (ADR-2026-11-09-1546), and a store to it faults, so writing a
constant global is UB when the write runs (the human's ruling of
2026-11-20 on #237, Q2). No op allocates a constant block. Below, a block
whose address and constness do not matter is written $`(k, \alpha, \vec{x}, \ell)`.
:::

:::readable Fir.Memory.Block.shape (fingerprint := "15915424377461907999")
*Definition: a block's shape.* The shape of a block is everything but what
its units hold and its address:
$`\mathrm{shape}(k, \alpha, \vec{x}, \ell, y^?, c) = (k, \alpha, |\vec{x}|, \ell, c)`.
Two memories with the same shapes, block by block, have the same
allocations: an access lands or faults in the same way in both.
:::

:::readable Fir.Memory.Memory (fingerprint := "3821757417443363225")
*Definition: a memory.* A memory $`M` is the list of its blocks, in the
order they were allocated, so that the block of the allocation $`a` is
$`M[a]`. Each memory of a module is one such list, with its own
allocations and its own unit width $`u`.
:::

:::readable Fir.Memory.Fault Fir.Memory.Fault.reason (fingerprint := "18388678182929345986")
*Definition: a fault.* An access that fails is immediate UB, for one of
five reasons (ADR-2026-11-09-1542; the human's rulings of 2026-11-11 on
#231 for $`\mathsf{misaligned}` and of 2026-11-20 on #237 for
$`\mathsf{constant}`):

```grammar Fir.Memory.Fault
\mathit{fault}
noProvenance   \mathsf{noProvenance}
freed          \mathsf{freed}
outOfBounds    \mathsf{outOfBounds}
misaligned     \mathsf{misaligned}
constant       \mathsf{constant}
```

* $`\mathsf{noProvenance}`: the pointer has no provenance for an
  allocation of the memory.
* $`\mathsf{freed}`: the pointer's allocation is freed.
* $`\mathsf{outOfBounds}`: the access touches a unit outside its
  allocation.
* $`\mathsf{misaligned}`: the access is not aligned at every address its
  allocation may be given.
* $`\mathsf{constant}`: the access is a store to a constant allocation.

Each has a reason in words, which a run that faults gives for its UB.
:::

:::readable Fir.Memory.Block.read Fir.Memory.Block.write (fingerprint := "4380596442681309824")
*Definition: reading and writing a block.* Reading $`n` units of a block
from offset $`o` gives $`\vec{x}[o \,..\, o + n]`, its units from $`o` on,
at most $`n` of them. Writing the units $`\vec{y}` at offset $`o` puts
them in place of the units from $`o` on:

$$`(k, \alpha, \vec{x}, \ell)[o := \vec{y}] = (k,~ \alpha,~ \vec{x}[0 \,..\, o]~\vec{y}~\vec{x}[o + |\vec{y}| \,..\,],~ \ell)`

The kind, the alignment, the liveness, the address and the constness stay
as they were, and so does the size when
the units fit, $`o + |\vec{y}| \le |\vec{x}|`. A store writes only units
that fit, as its access checks.
:::

:::readable Fir.Memory.Block.kill (fingerprint := "15182547589668359642")
*Definition: a freed block.* $`\mathrm{kill}(k, \alpha, \vec{x}, \ell) = (k, \alpha, \vec{x}, \mathsf{false})`:
the block, no longer live, with its kind, its alignment, its units, its
address and its constness.
:::

:::readable Fir.Memory.Memory.empty (fingerprint := "4566367693092568579")
*Definition: the empty memory.* Before anything is allocated, a memory has
no blocks: $`M = \epsilon`.
:::

:::readable Fir.Memory.Memory.alloc (fingerprint := "2050193437329174558")
*Definition: allocating.* Allocating $`n` units of kind $`k`, aligned to
$`\alpha` units, in $`M` adds one live block of $`n` poisons at the end,
and gives the pointer to its first unit:

$$`\mathrm{alloc}_k(M, n, \alpha) = \big((|M|, 0),~ M~(k, \alpha, \mathsf{poison}^n, \mathsf{true}, \bot, \mathsf{false})\big)`

The new allocation's id is $`|M|`, which no allocation had before, it
has no address, $`\bot`, and it is not constant.
Provenance comes only from allocations: a pointer has provenance for an
allocation because the allocation gave it, or because it was computed from
one that did. A pointer that names an id not yet allocated has none, and
every access through it faults.
:::

:::readable Fir.Memory.Memory.free (fingerprint := "3491244456422549382")
*Definition: freeing.* Freeing the allocation $`a` kills its block,
$`M[a] := \mathrm{kill}(M[a])`, and changes nothing else. The block stays in the memory, so no id is
reused. Freeing never faults: freeing a block that is already freed, or an
id the memory does not have, changes nothing. The run frees a call's stack
allocations when it returns (ADR-2026-11-09-1548), and an external call
frees a heap allocation.
:::

:::readable Fir.Memory.Memory.locate (fingerprint := "1049162986385104119")
*Definition: where an access lands.* An access of $`n` units through the
pointer $`(a^?, o)` lands in the allocation $`a`, at offset $`o`, when all
of these hold; otherwise it faults with the first that fails:

* $`a` is given, and $`M` has a block $`M[a] = (k, \alpha, \vec{x}, \ell)`;
  otherwise $`\mathsf{noProvenance}`;
* the block is live, $`\ell = \mathsf{true}`; otherwise $`\mathsf{freed}`;
* every unit it touches is inside the block, $`0 \le o` and
  $`o + n \le |\vec{x}|`; otherwise $`\mathsf{outOfBounds}`.
:::

:::readable Fir.Memory.Memory.load (fingerprint := "2878384574588793941")
*Definition: loading.* Loading $`n` units through $`p` gives the $`n`
units of its allocation's block from its offset on, $`\vec{x}[o \,..\, o + n]`,
or the fault of its access.
:::

:::readable Fir.Memory.Memory.store (fingerprint := "16910544642550588426")
*Definition: storing.* Storing the units $`\vec{y}` through $`p` gives the
fault of its access, an access of $`|\vec{y}|` units, when it faults;
otherwise it faults with $`\mathsf{constant}` when its allocation's block
is constant, and writes the units into the block at its offset,
$`M[a] := M[a][o := \vec{y}]`, when it is not. No other unit and no other
allocation changes.
:::

:::readable Fir.Memory.Memory.aligned (fingerprint := "2489683034287928732")
*Definition: an aligned access.* An access through the pointer
$`(a^?, o)` aligned to $`\alpha` units is _aligned_ in $`M` when, if
$`M` has the block $`M[a] = (k, \alpha_b, \vec{x}, \ell)`,

$$`\alpha \mid \alpha_b \quad\text{and}\quad \alpha \mid o`

A block has no address. Every address it may be given is a multiple of
its alignment $`\alpha_b`, and the access's address is that plus $`o`. So
the access is aligned at every address its block may be given exactly
when $`\alpha` divides both, and that is what aligned means (the human's
ruling of 2026-11-14 on #388; rejected: aligned at some address, under
which no pass or backend could rely on an alignment promise). An access through a pointer that names no
block of $`M` is aligned: it faults with $`\mathsf{noProvenance}`.
So an access aligned to 4 into a block aligned to 2 is misaligned, even
at offset 0, and one aligned to 1 is always aligned.
:::

:::readable Fir.Memory.Memory.loadAligned Fir.Memory.Memory.storeAligned (fingerprint := "13237962399437252429")
*Definition: aligned loads and stores.* An op's load or store carries
an alignment, and a misaligned access is immediate UB (the human's ruling
of 2026-11-11 on #231). The aligned load of $`n` units through $`p`,
aligned to $`\alpha` units, is the plain load, which faults first; when
the plain load succeeds, it gives its units if the access is aligned, and
faults with $`\mathsf{misaligned}` if not. The aligned store of
$`\vec{y}` is the plain store, in the same way.
:::
