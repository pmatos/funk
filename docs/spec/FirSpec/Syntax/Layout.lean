import VersoManual
import Fir.Syntax.Layout
import Fir.Validation.Layout
import Fir.Text.Grammar
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on data layouts, which renders
`Fir.Syntax.Layout` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Data layouts: readable blocks" =>

:::moduleDocs (fingerprint := "11879504597878469070")
:::

:::readable Fir.ByteOrder (fingerprint := "2717303684540409010")
*Definition: a byte order.* A value that spans several units of a memory
puts them in one of two orders:

```grammar Fir.ByteOrder
\mathit{order}
little \mathsf{little}
big    \mathsf{big}
```

$`\mathsf{little}` puts the least significant unit first, at the lowest
offset, and $`\mathsf{big}` the most significant. The byte order is a
parameter of how values are stored in units. M1 admits only
$`\mathsf{little}`: validation rejects a memory whose order is
$`\mathsf{big}` (the human's ruling of 2026-11-11 on #231).
:::

:::readable Fir.MemLayout (pin := Fir.MemLayout.attr) (fingerprint := "4149236188179064429")
*Definition: the entry of a memory.* The data layout gives each memory it
declares an entry:

```grammar Fir.MemLayout
\mathit{entry}
mem,unit,pointer,order,align,nonIntegral \begin{array}{l} \{\mathsf{mem}~n, \\ \enspace \mathsf{unit}~u, \\ \enspace \mathsf{pointer}~p, \\ \enspace \mathsf{order}~\mathit{order}, \\ \enspace \mathsf{align}~a^?, \\ \enspace \mathsf{nonIntegral}~b\,\} \end{array}
```

$`n` is the memory's number, the $`N` of the pointer type
$`\mathsf{ptr}\langle N\rangle`. $`u` is the width of the memory's unit of
addressing, in bits: sizes and offsets in the memory count its units. $`p`
is the width of its pointers, in bits. The order is the memory's byte
order. $`a`, when the entry gives one, is the alignment of the memory's
pointers in units; without it, they have their natural alignment, defined
below. $`b` marks a memory as non-integral, as LLVM's `ni:` marks an address
space: no pointer of such a memory becomes an integer (ADR-2026-11-12-1821).

In text the entry is written
`memory(n, unit(u), pointer(p), order)`, then `align(a)` when it gives
one and `nonintegral` when $`b` holds, as in
`memory(1, unit(16), pointer(32), little, align(4), nonintegral)`.
:::

:::readable Fir.DataLayout (fingerprint := "10594782985174102361")
*Definition: a data layout.* A data layout is a sequence of entries,
$`\mathit{entry}^*`, one for each memory it declares, in the order the text
writes them. Nothing sorts or merges them.
:::

:::readable Fir.MemLayout.limit (fingerprint := "6887097782837779550")
*Definition: the limit of a layout's numbers.* The largest number that an
entry gives, a memory, a width or an alignment, is $`2^{24} - 1`: the bound
of an integer type's width and of a pointer type's memory.
:::

:::readable Fir.MemLayout.default (fingerprint := "17191845494664329151")
*Definition: the default memory's entry.* Memory 0, the default memory, is
in every module. When the layout does not declare it, it has the entry

$$`\{\mathsf{mem}~0,\ \mathsf{unit}~8,\ \mathsf{pointer}~64,\ \mathsf{order}~\mathsf{little},\ \mathsf{align}~\epsilon,\ \mathsf{nonIntegral}~\mathsf{false}\}`

with 8-bit units, 64-bit pointers of their natural alignment, little
endian and integral. So a module whose text has no layout has memory 0
alone, with this entry.
:::

:::readable Fir.DataLayout.memory? Fir.DataLayout.Declares Fir.DataLayout.decidableDeclares (fingerprint := "6545840913398667417")
*Definition: the memories of a layout.* The entry of memory $`n` in the
layout $`L`, $`L(n)`, is the first entry of $`L` whose number is $`n`; when
there is none, it is the default entry for memory 0, and nothing for any
other memory. The layout _declares_ $`n` when $`L(n)` exists:

$$`L~\text{declares}~n \iff L(n) \neq \epsilon`

Whether a layout declares a memory can be decided.
:::

:::readable Fir.DataLayout.declares_zero Fir.DataLayout.declares_of_mem Fir.DataLayout.declares_nil (fingerprint := "6458292626815605081")
*Theorem: which memories a layout declares.* Every layout declares memory
0. A layout declares the memory of each of its entries. The empty layout,
which a module without a layout line has, declares memory 0 and no other:

$$`\epsilon~\text{declares}~n \iff n = 0`
:::

:::readable Fir.DataLayout.entry Fir.DataLayout.entry_of_memory (fingerprint := "1906880335619431194")
*Definition: the entry a run gives a memory.* A run of a module with the
layout $`L` gives each memory $`n` the entry $`\ell_L(n)`: $`L(n)` when
$`L` declares $`n`, and the default entry otherwise. So
$`\ell_L(n) = L(n)` whenever $`L(n)` exists. Validation rejects every type
that names a memory that $`L` does not declare, so a valid module never
reaches the default for any memory but 0; a run does not validate what it
runs, so an invalid one may.

The semantics with memory gives each op the entries of the memories it
names, so a load or a store reads its memory's unit width, byte order and
pointer width from $`\ell_L` (`docs/decisions/semantics-effects.md#soundness`).
:::

:::readable Fir.MemLayout.pointerUnits Fir.MemLayout.naturalAlign Fir.MemLayout.alignment (fingerprint := "509354576672953658")
*Definition: the units and the alignment of a pointer.* A pointer of the
memory of the entry $`e` takes $`\lceil p / u \rceil` units, its width over
the unit's, rounded up. Its natural alignment is the least power of two
that is at least that number of units, and its alignment is the entry's
own $`a` when the entry gives one, and the natural one otherwise. So the
default memory's pointers take 8 units and are aligned to 8.
:::
