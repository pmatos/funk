import VersoManual
import Fir.Execution.ObserveEndLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the laws of the end of a return,
which renders `Fir.Execution.ObserveEndLaws` (ADR-2026-11-05-2012). Each
block explains declarations of that module and pins their fingerprint; the
build fails when the Lean changes under it.
-/

#doc (Manual) "Laws of the end of a return: readable blocks" =>

:::moduleDocs (fingerprint := "5277642195407649636")
:::

:::readable Fir.Renaming.ptr_id Fir.Renaming.id_covers (fingerprint := "8261197138660584134")
*Theorem: the identity renaming.* Under the identity, a pointer is seen as
itself, or as poison when it is dangling, and the identity covers every
pointer.
:::

:::readable Fir.Memory.Block.OptSeenIn.freed_eq Fir.Renaming.ptr_comp Fir.Renaming.Covers.comp Fir.HasPtrs.map_comp_le (fingerprint := "5509245789772729598")
*Theorem: two renamings in turn.* Two allocations seen in each other are
both freed or neither is. So when $`R_1` renames only allocations whose
images in $`M` are freed just when they are in $`S`, and covers $`p`:

$$`(R_1;R_2)^{S}_n(p) = \mathsf{poison} \quad\text{or}\quad (R_1;R_2)^{S}_n(p) = R_2^{M}_n(R_1^{S}_n(p))`

and $`R_1;R_2` covers $`p` when $`R_2` covers its image. Replacing the
pointers of a value that $`R_1` covers by $`(R_1;R_2)^S` refines less than
replacing them by $`R_1^S`, then $`R_2^M`.
:::

:::readable Fir.Memory.Block.OptSeenIn.some_left Fir.Memory.Block.OptSeenIn.trans (fingerprint := "5522943077167086512")
*Theorem: seeing allocations is transitive.* An allocation that is a block
is seen in a block. An allocation seen in a second, which is seen in a
third, is seen in the third, when replacing its units' pointers by $`f_3`
refines less than replacing them by $`f_1`, then $`f_2`.
:::

:::readable Fir.End.isRefinedBy_refl Fir.End.isRefinedBy_trans (fingerprint := "2434149458349433759")
*Theorem: refinement of the ends of returns is a preorder.* The identity
shows an end in itself. When $`R_1` shows $`s` in $`m` and $`R_2` shows
$`m` in $`t`, $`R_1;R_2` shows $`s` in $`t`, when refinement of the
returned values is transitive.
:::

:::readable Fir.End.isRefinedBy_iff_vals (fingerprint := "4462620303117133407")
*Theorem: with no pointer and nothing escaped, the values decide.* When the
source returns no pointer and nothing escaped:

$$`\langle \vec{v}, S, []\rangle \sqsubseteq \langle \vec{v}', S', E'\rangle \iff \vec{v} \sqsubseteq \vec{v}' \land E' = []`

So M0's runs, which return no pointer and show no event, keep their
refinement.
:::
