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

:::moduleDocs (fingerprint := "10127504593038420527")
:::

:::readable Fir.isPowerOfTwo (fingerprint := "18023849196204137947")
*Definition: a power of two.* A natural number $`a` is a power of two, $`1`,
$`2`, $`4` and so on, when it is not 0 and has no bit in common with
$`a - 1`.
:::

:::readable Fir.MemLayout.Valid (fingerprint := "18387061454187400433")
*Definition: a valid entry.* The entry $`e` of a data layout is valid when
its memory's number is at most the limit, $`2^{24} - 1`; its unit and its
pointers each have from 1 to $`2^{24} - 1` bits; its byte order is
$`\mathsf{little}`; and the alignment it gives, if any, is a power of two
no larger than the limit:

$$`\dfrac{n \le 2^{24}-1 \qquad 1 \le u, p \le 2^{24}-1 \qquad \forall a' \in a^?.\ a'~\text{a power of two} \le 2^{24}-1}{\vdash \{\mathsf{mem}~n, \mathsf{unit}~u, \mathsf{pointer}~p, \mathsf{order}~\mathsf{little}, \mathsf{align}~a^?, \mathsf{nonIntegral}~b\}~\text{valid}}`

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

:::readable Fir.SymbolTable.MemoriesIn Fir.Module.MemoriesDeclared (fingerprint := "17413471415812578625")
*Definition: the memories that a module's types name.* The memories of the
symbol table $`T` are in the layout $`L` when $`L` has the memory of each
type that each function of $`T` states, its results, its parameters and
the values its blocks define, and of each type that each item of a
dialect's kind of $`T` states. The layout of the module $`M` declares the
memories of $`M` when the memories of each of its symbol tables, its own and
each nested module's at any depth, are in it. A nested module has no layout
of its own, so its types name the memories of the module that holds it.

So a function that takes a $`\mathsf{ptr}\langle 1\rangle` is valid only in
a module whose layout declares memory 1, while one that takes a
$`\mathsf{ptr}`, which is $`\mathsf{ptr}\langle 0\rangle`, is valid in every
module.
:::
