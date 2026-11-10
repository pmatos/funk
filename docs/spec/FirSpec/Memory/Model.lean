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

:::moduleDocs (fingerprint := "9848544354756000761")
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

:::readable Fir.Memory.MemUnit (fingerprint := "5111969052292565827")
*Definition: a unit.* A unit of a memory whose units are $`u` bits wide
holds concrete bits, poison, or a fragment of a pointer:

```grammar Fir.Memory.MemUnit
\mathit{unit}
bits     \mathsf{bits}~b
poison   \mathsf{poison}
frag     \mathsf{frag}~p~i
```

* $`\mathsf{bits}~b`: the $`u` bits $`b`.
* $`\mathsf{poison}`: poison. Fresh memory holds it.
* $`\mathsf{frag}~p~i`: the fragment $`i` of the pointer $`p`. A pointer
  stored to memory takes several units, one fragment each, so a pointer
  copied unit by unit keeps its provenance (ADR-2026-11-09-1542).
:::

:::readable Fir.Memory.AllocKind (fingerprint := "3213965169790151508")
*Definition: an allocation kind.* Every allocation has a kind
(ADR-2026-11-09-1542):

```grammar Fir.Memory.AllocKind
\mathit{kind}
stack,global,heap   \mathsf{stack} \mid \mathsf{global} \mid \mathsf{heap}
```

* $`\mathsf{stack}`: it lives until the call that made it returns
  (ADR-2026-11-09-1548).
* $`\mathsf{global}`: it lives for the whole run (ADR-2026-11-09-1546).
* $`\mathsf{heap}`: it comes from an external call, such as one to
  `malloc`.

Managed memory can be added as another kind.
:::

:::readable Fir.Memory.Block (fingerprint := "1929426076441996878")
*Definition: an allocation's block.* A block is a triple
$`(k, \vec{x}, \ell)`: its kind $`k`, its units $`\vec{x}`, and whether it
is live, $`\ell \in \{\mathsf{true}, \mathsf{false}\}`. Its size is
$`|\vec{x}|`. A freed block keeps its units, but no access may reach them.
:::

:::readable Fir.Memory.Memory (fingerprint := "3821757417443363225")
*Definition: a memory.* A memory $`M` is the list of its blocks, in the
order they were allocated, so that the block of the allocation $`a` is
$`M[a]`. Each memory of a module is one such list, with its own
allocations and its own unit width $`u`.
:::

:::readable Fir.Memory.Fault Fir.Memory.Fault.reason (fingerprint := "418687010208517563")
*Definition: a fault.* An access that fails is immediate UB, for one of
three reasons (ADR-2026-11-09-1542):

```grammar Fir.Memory.Fault
\mathit{fault}
noProvenance   \mathsf{noProvenance}
freed          \mathsf{freed}
outOfBounds    \mathsf{outOfBounds}
```

* $`\mathsf{noProvenance}`: the pointer has no provenance for an
  allocation of the memory.
* $`\mathsf{freed}`: the pointer's allocation is freed.
* $`\mathsf{outOfBounds}`: the access touches a unit outside its
  allocation.

Each has a reason in words, which a run that faults gives for its UB.
:::

:::readable Fir.Memory.Block.read Fir.Memory.Block.write (fingerprint := "11238998448373888792")
*Definition: reading and writing a block.* Reading $`n` units of a block
from offset $`o` gives $`\vec{x}[o \,..\, o + n]`, its units from $`o` on,
at most $`n` of them. Writing the units $`\vec{y}` at offset $`o` puts
them in place of the units from $`o` on:

$$`(k, \vec{x}, \ell)[o := \vec{y}] = (k,~ \vec{x}[0 \,..\, o]~\vec{y}~\vec{x}[o + |\vec{y}| \,..\,],~ \ell)`

The kind and the liveness stay as they were, and so does the size when
the units fit, $`o + |\vec{y}| \le |\vec{x}|`. A store writes only units
that fit, as its access checks.
:::

:::readable Fir.Memory.Memory.empty (fingerprint := "4566367693092568579")
*Definition: the empty memory.* Before anything is allocated, a memory has
no blocks: $`M = \epsilon`.
:::

:::readable Fir.Memory.Memory.alloc (fingerprint := "6826753237597700476")
*Definition: allocating.* Allocating $`n` units of kind $`k` in $`M` adds
one live block of $`n` poisons at the end, and gives the pointer to its
first unit:

$$`\mathrm{alloc}_k(M, n) = \big((|M|, 0),~ M~(k, \mathsf{poison}^n, \mathsf{true})\big)`

The new allocation's id is $`|M|`, which no allocation had before.
Provenance comes only from allocations: a pointer has provenance for an
allocation because the allocation gave it, or because it was computed from
one that did. A pointer that names an id not yet allocated has none, and
every access through it faults.
:::

:::readable Fir.Memory.Memory.free (fingerprint := "15821920455813180707")
*Definition: freeing.* Freeing the allocation $`a` marks its block as not
live, and changes nothing else. The block stays in the memory, so no id is
reused. Freeing never faults: freeing a block that is already freed, or an
id the memory does not have, changes nothing. The run frees a call's stack
allocations when it returns (ADR-2026-11-09-1548), and an external call
frees a heap allocation.
:::

:::readable Fir.Memory.Memory.locate (fingerprint := "7962100636980851191")
*Definition: where an access lands.* An access of $`n` units through the
pointer $`(a^?, o)` lands in the allocation $`a`, at offset $`o`, when all
of these hold; otherwise it faults with the first that fails:

* $`a` is given, and $`M` has a block $`M[a] = (k, \vec{x}, \ell)`;
  otherwise $`\mathsf{noProvenance}`;
* the block is live, $`\ell = \mathsf{true}`; otherwise $`\mathsf{freed}`;
* every unit it touches is inside the block, $`0 \le o` and
  $`o + n \le |\vec{x}|`; otherwise $`\mathsf{outOfBounds}`.
:::

:::readable Fir.Memory.Memory.load (fingerprint := "8095741583226895581")
*Definition: loading.* Loading $`n` units through $`p` gives the $`n`
units of its allocation's block from its offset on, $`\vec{x}[o \,..\, o + n]`,
or the fault of its access.
:::

:::readable Fir.Memory.Memory.store (fingerprint := "8493545234178445732")
*Definition: storing.* Storing the units $`\vec{y}` through $`p` writes
them into its allocation's block at its offset, $`M[a] := M[a][o := \vec{y}]`,
or gives the fault of its access, an access of $`|\vec{y}|` units. No other
unit and no other allocation changes.
:::
