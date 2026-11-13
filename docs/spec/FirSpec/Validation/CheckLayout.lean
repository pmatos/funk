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

:::moduleDocs (fingerprint := "968208954335950470")
:::

:::readable Fir.need Fir.need_eq_nil (fingerprint := "7722159485140472772")
*Definition: one problem unless a condition holds.* $`\mathrm{need}(c, P)`
is no problem when the condition $`c` holds, and the problem $`P`
otherwise. It gives no problem exactly when $`c` holds.
:::

:::readable Fir.MemLayout.problems Fir.MemLayout.problems_eq_nil (fingerprint := "9524884543563344005")
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

:::readable Fir.memoryProblem Fir.memoryProblem_eq_none Fir.SymbolTable.memoryProblems Fir.SymbolTable.memoryProblems_eq_nil (fingerprint := "11196811998435207586")
*Definition: the check of a table's memories.* The check of the memories of
the symbol table $`T` in the layout $`L` gives one problem for each function
of $`T`, and then for each item of a dialect's kind, whose types name a
memory that $`L` misses. The problem names the item's symbol and the first
memory it misses: "a type names memory $`n`, which the data layout does not
declare". The check gives no problem exactly when the memories of $`T` are
in $`L`.
:::
