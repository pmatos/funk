import VersoManual
import Fir.Validation.Nest
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the module of a nested symbol table,
which renders `Fir.Validation.Nest` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "The module of a nested table: readable blocks" =>

:::moduleDocs (fingerprint := "9633832136249785136")
:::

:::readable Fir.Module.nest Fir.Module.nest_table Fir.Module.nest_funcs Fir.Module.nest_layout (fingerprint := "14539827474870878551")
*Definition: the module of a table.* For a module $`M` and one of its
symbol tables $`t`, $`M.\mathrm{nest}(t)` is the module whose dialect set
and items are $`t`'s, and whose data layout and location table are $`M`'s.
A function of $`t` runs in it: a call names a function of $`t`, and a
pointer type names a memory of $`M`'s layout. A module's own table gives
the module back, and the functions and the layout of $`M.\mathrm{nest}(t)`
are $`t`'s functions and $`M`'s layout.
:::

:::readable Fir.Item.tables_closed Fir.Item.tablesIn_closed Fir.Module.tables_nest (fingerprint := "1434188233690602781")
*Theorems: the tables of a table are tables of the module.* A table nested
in an item, or in a list of items, holds the tables nested in it among that
item's, or that list's, at any depth. So every table of
$`M.\mathrm{nest}(t)`, for a table $`t` of $`M`, is a table of $`M`.
:::

:::readable Fir.Module.Valid.nest (fingerprint := "5427870368383046134")
*Theorem: the module of each table of a valid module is valid.* If $`M` is
valid and $`t` is one of its tables, its own or that of a module nested in
it at any depth, then $`M.\mathrm{nest}(t)` is valid: its tables are tables
of $`M`, each valid, and it has $`M`'s location table and layout, which
declares every memory that its types name. So every theorem about the
functions of a valid module holds of the functions of each of its tables, a
device module's kernels included.
:::
