import VersoManual
import Fir.Validation.Layout
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the data layout's rules, which
renders `Fir.Validation.Layout` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The data layout's rules: readable blocks" =>

:::moduleDocs (fingerprint := "13587330066394704076")
:::

:::readable Fir.isPowerOfTwo (fingerprint := "18023849196204137947")
*Definition: a power of two.* A natural number $`a` is a power of two, $`1`,
$`2`, $`4` and so on, when it is not 0 and has no bit in common with
$`a - 1`.
:::

:::readable Fir.MemLayout.ValidAlign (pin := Fir.isPowerOfTwo) (pin := Fir.MemLayout.limit) (fingerprint := "14994022144014384239")
*Definition: a valid alignment.* An alignment $`a` is valid when it is a
power of two no larger than the limit, $`2^{24} - 1`, so the largest is
$`2^{23}`. It is the one rule of the alignment that an entry writes for its
pointers and of the alignment that an $`\mathsf{alloca}`, a
$`\mathsf{load}` or a $`\mathsf{store}` writes
({ref "The-fir-specification--Validation--Core-rules"}[the
core's rules]). A natural alignment, which an entry or an
$`\mathsf{alloca}` that writes none takes, is not bound by it: in a memory
with 1-bit units it can be $`2^{24}`. For an $`\mathsf{alloca}` the human
ruled so on 2026-11-14 (#385), as an entry's pointers already were. The
rejected alternative, rejecting an $`\mathsf{alloca}` whose natural
alignment is above the limit, would need the data layout in the op's rule
and would change the proofs over op validity.
:::

:::readable Fir.MemLayout.Valid (pin := Fir.MemLayout.ValidAlign) (fingerprint := "7806627350590008117")
*Definition: a valid entry.* The entry $`e` of a data layout is valid when
its memory's number is at most the limit, $`2^{24} - 1`; its unit and its
pointers each have from 1 to $`2^{24} - 1` bits; its byte order is
$`\mathsf{little}`; and the alignment it gives, if any, is valid, a power
of two no larger than the limit:

$$`\dfrac{n \le 2^{24}-1 \qquad 1 \le u, p \le 2^{24}-1 \qquad \forall a' \in a^?.\ a'~\text{a valid alignment}}{\vdash \{\mathsf{mem}~n, \mathsf{unit}~u, \mathsf{pointer}~p, \mathsf{order}~\mathsf{little}, \mathsf{align}~a^?, \mathsf{nonIntegral}~b\}~\text{valid}}`

An entry whose order is $`\mathsf{big}` decodes, and is never valid in M1:
no backend or harness yet uses a big-endian memory (the human's ruling of
2026-11-11 on #231). A non-integral entry is valid; the ops that turn a
pointer into an integer and back are rejected on such a memory
(ADR-2026-11-12-1821).
:::

:::readable Fir.DataLayout.Valid (fingerprint := "8730855190514664523")
*Definition: a valid data layout.* A data layout is valid when each of its
entries is, and it declares each memory once: the numbers of its entries
are distinct.
:::

:::readable Fir.DataLayout.pointer_pos (fingerprint := "15452446704807025419")
*Theorem: pointers have bits.* Each memory of a valid layout, the
default memory included, has pointers of at least one bit.
:::

:::readable Fir.DataLayout.HasMemoryOf Fir.DataLayout.decidableHasMemoryOf (fingerprint := "14715638795206739839")
*Definition: the layout has a type's memory.* A dialect says which memory
each of its pointer types points into, by its number,
$`\mathrm{memory}(t)`, and names none for another type
({ref "The-fir-specification--Validation--Scope-and-symbols"}[the dialect's
rules]). The layout $`L` _has the memory of_ the type $`t` when it declares
$`\mathrm{memory}(t)`, or when $`t` names no memory. Whether it does can be
decided.
:::

:::readable Fir.Func.attrTypes Fir.SymbolTable.MemoriesIn Fir.Module.MemoriesDeclared (fingerprint := "12736814380526601669")
*Definition: the memories that a module's types name.* The memories of the
symbol table $`T` are in the layout $`L` when $`L` has the memory of each
type that each function of $`T` states, its results, its parameters and
the values its blocks define, of each type that an op of each function of
$`T` carries in its attributes, $`\mathrm{optypes}`, op by op, and of each
type that each item of a dialect's kind of $`T` states. The layout of the module $`M` declares the
memories of $`M` when the memories of each of its symbol tables, its own and
each nested module's at any depth, are in it. A nested module has no layout
of its own, so its types name the memories of the module that holds it.

So a function that takes a $`\mathsf{ptr}\langle 1\rangle` is valid only in
a module whose layout declares memory 1, while one that takes a
$`\mathsf{ptr}`, which is $`\mathsf{ptr}\langle 0\rangle`, is valid in every
module; and so is an $`\mathsf{alloca}` of $`\mathsf{ptr}\langle 1\rangle`
values.
:::

:::readable Fir.roundUp Fir.Field.extent Fir.Field.shape Fir.Field.units (pin := Fir.DataLayout.entry) (fingerprint := "13486431922279883060")
*Definition: the units that a field takes.* $`\mathrm{roundup}(u, a)` is
$`u` rounded up to a multiple of $`a`: $`\lceil u / a \rceil \cdot a`. Let
$`\ell` be the data layout of a module and $`n` a memory. The shape of a
field $`F` of type $`t` in memory $`n`, $`\mathrm{shape}_{\ell,n}(F)`, is
$`\mathrm{shape}_d(\mathrm{entry}_\ell, n, t)`: the units $`u` that one
value of $`t` takes there and its alignment $`a`, as the dialect of $`t`
says, or none when $`t` may not be a field. A field of one value takes
$`u` units, and a repeated field of $`c` elements takes

$$`\mathrm{extent}(F, u, a) = c \cdot \mathrm{roundup}(u, a)`

units: each element is rounded up to its alignment (the human's ruling of
2026-11-16 on #236). So four `i24` in memory 0, each 3 units aligned to 4,
take 16 units. $`\mathrm{units}_{\ell,n}(F)` is the extent of $`F` at its
shape, and 0 when its type may not be a field.
:::

:::readable Fir.Field.Placed Fir.Field.decidablePlaced Fir.Field.Apart Fir.Field.decidableApart (fingerprint := "7370576294404612289")
*Definition: a placed field, and two fields apart.* A field $`F` at the
offset $`o` is placed in a layout of memory $`n` with the size $`z` and
the alignment $`A` when its type may be a field, with the shape $`(u, a)`,
and

$$`a \mid o \qquad a \le A \qquad o + \mathrm{extent}(F, u, a) \le z`

that is, its offset is a multiple of its type's alignment, that alignment
is no larger than the layout's, and the field ends within the size. Two
fields $`F` and $`G` are apart when one ends before the other starts, or
one of them takes no units:

$$`o_F + \mathrm{units}(F) \le o_G \;\lor\; o_G + \mathrm{units}(G) \le o_F \;\lor\; \mathrm{units}(F) = 0 \;\lor\; \mathrm{units}(G) = 0`

So a repeated field of no elements, which a C flexible array member is,
is apart from every field. Both can be decided.
:::

:::readable Fir.Aggregate.Valid Fir.Module.AggregatesValid (pin := Fir.MemLayout.ValidAlign) (fingerprint := "3141668117769171098")
*Definition: a valid aggregate's layout.* An aggregate's layout $`A` of
memory $`n` is valid in a module whose data layout is $`\ell` when

$$`\dfrac{\begin{array}{c} A \text{ is within its limits} \qquad \ell \text{ declares } n \qquad \mathrm{align}(A) \text{ is a valid alignment} \\ \vdash_d t~\text{valid and } \ell \text{ declares the memory of } t \text{ for each } t \in \mathrm{types}(A) \\ F \text{ is placed for each field } F \text{ of } A \qquad \text{the fields of } A \text{ are pairwise apart} \end{array}}{\ell \vdash A~\text{valid}}`

(ADR-2026-11-16-1546). Its numbers are within the limit so that the text
can write it, and its alignment is valid as an entry's is: a power of two
no larger than $`2^{24} - 1`. A module's aggregates' layouts are valid when
each layout of each of its symbol tables, its own and each nested
module's, is valid in the module's one data layout.
:::
