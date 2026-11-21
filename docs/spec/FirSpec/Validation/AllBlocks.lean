import VersoManual
import Fir.Validation.AllBlocks
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on where a block sits, which renders
`Fir.Validation.AllBlocks` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Where a block sits: readable blocks" =>

:::moduleDocs (fingerprint := "3939647015306293821")
:::

:::readable Fir.Block.InRegionOf Fir.Block.InRegionOf.mono Fir.Block.mem_allBlocks Fir.Region.mem_allBlocks_cases Fir.Block.mem_allBlocks_cases Fir.Operation.mem_regionBlocks_cases Fir.Func.mem_allBlocks_cases (pin := Fir.Func.allBlocks) (fingerprint := "12115075447680226974")
*Theorems: where a block of a function sits.* A block $`b` is _in a region
of_ a list of blocks $`L` when some op of some block of $`L` owns a region
that holds $`b`. Every block of a list is among its blocks at any depth.
And every block of $`\mathrm{allblocks}(f)` is a block of the body of $`f`,
or a block in a region of $`\mathrm{allblocks}(f)`. So every op of a
function at any depth is an op of its body, or an op inside a region of an
op of the function, and the general rules cover each op once.
:::
