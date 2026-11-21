import VersoManual
import Fir.Validation.CheckLayout
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on checking the data layout, which
renders `Fir.Validation.CheckLayout` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Checking the data layout: readable blocks" =>

:::moduleDocs (fingerprint := "1017014516784800239")
:::

:::readable Fir.need Fir.need_eq_nil (fingerprint := "7722159485140472772")
*Definition: one problem unless a condition holds.* $`\mathrm{need}(c, P)`
is no problem when the condition $`c` holds, and the problem $`P`
otherwise. It gives no problem exactly when $`c` holds.
:::

:::readable Fir.MemLayout.problems Fir.MemLayout.problems_eq_nil (pin := Fir.MemLayout.ValidAlign) (fingerprint := "7448233536726733923")
*Definition: the check of an entry.* The check of the entry $`e` of memory
$`n` gives, in this order, a problem for each rule of a valid entry that
$`e` breaks: a number above the limit; a unit or pointers of no bits or of
more than the limit; the byte order $`\mathsf{big}`, which M1 does not
admit; and an alignment that is not a power of two within the limit. Each
problem starts "data layout: memory $`n`". The check gives no problem
exactly when $`e` is valid.
:::

:::readable Fir.DataLayout.problems Fir.DataLayout.problems_eq_nil Fir.DataLayout.decidableValid (fingerprint := "10579221279708594081")
*Definition: the check of a data layout.* The check of the layout $`L`
gives the problems of each entry, in order, then one problem for each
memory that $`L` declares again after its first entry. It gives no problem
exactly when $`L` is valid, so the validity of a layout can be decided.
:::

:::readable Fir.DataLayout.missing Fir.DataLayout.missing_eq_nil (fingerprint := "15047233252531822272")
*Definition: the memories that a layout misses.* The memories that the
layout $`L` misses among the types $`t^*` are the memories, in order, that
the types name and $`L` does not declare. There are none exactly when $`L`
has the memory of each type.
:::

:::readable Fir.memoryProblem Fir.memoryProblem_eq_none Fir.unitsProblem Fir.unitsProblem_eq_none Fir.addrsProblem Fir.addrsProblem_eq_none Fir.SymbolTable.memoryProblems Fir.SymbolTable.memoryProblems_eq_nil (fingerprint := "9592405104375268863")
*Definition: the check of a table's memories.* The check of the memories of
the symbol table $`T` in the layout $`L` gives one problem for each function
of $`T`, and then for each item of a dialect's kind, whose types name a
memory that $`L` misses. A function's types are those it states, then
those its ops carry in their attributes. The problem names the item's symbol and the first
memory it misses: "a type names memory $`n`, which the data layout does not
declare". Then it gives one problem for each function of $`T` whose ops
ask units of $`V` bits of a memory $`N` whose entry in $`L` has units of
$`U \ne V` bits; the problem names the function and the first such pair:
"an op writes values of $`V` bits into memory $`N`, whose units have $`U`
bits". Last it gives one problem for each function of $`T` whose ops ask
pointers of $`W` bits of a memory $`N` whose entry in $`L` is non-integral,
"an op turns pointers of memory $`N` into integers or back, but the memory
is non-integral", or has pointers of $`P \ne W` bits, "an op turns pointers
of memory $`N` into integers of $`W` bits or back, but its pointers have
$`P` bits". The check gives no problem exactly when the memories of $`T`
are in $`L`.
:::

:::readable Fir.Aggregate.decidableInLimits Fir.Aggregate.problem Fir.Field.problems Fir.Field.problems_eq_nil (fingerprint := "5817582713345187724")
*Definition: the check of a field.* Whether a layout is within its limits
can be decided. A problem about the layout $`A` names its symbol. The
problems of a field $`F` at the offset $`o` of $`A` are one, "the field at
offset $`o` has a type that may not be a field: an integer, a float or a pointer",
when its type has no shape; and otherwise, in order, "the field at offset
$`o` is not a multiple of its type's alignment, $`a`", "the field at offset
$`o` has a type aligned to $`a` units, more than the layout's $`A`" and
"the field at offset $`o` ends past the layout's size, $`z`", each when $`F`
breaks that rule. A field has no problem exactly when it is placed.
:::

:::readable Fir.Aggregate.problems Fir.Aggregate.problems_eq_nil Fir.Aggregate.decidableValid (fingerprint := "18075158507381701911")
*Definition: the check of an aggregate's layout.* The problems of a layout
$`A` in a module whose data layout is $`\ell` are, in order: one when a
number of $`A` is above $`2^{64} - 1`; one when $`\ell` does not declare
its memory; one when its alignment is not valid; one when a type of $`A` is
not valid; one, as for a function, when a type of $`A` names a memory that
$`\ell` does not declare; the problems of each field, in order; and "two
fields of the layout share a unit" when two fields are not apart. A layout
has no problem exactly when it is valid, so validity can be decided.
:::
