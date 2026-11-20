import VersoManual
import Fir
import FirSpecSite.ReadableElab
import FirSpec.ReadableDocs

open Verso.Genre Manual
open FirSpecSite

set_option pp.rawOnError true

/-!
The chapter on the GPU dialect of the fir specification, which
`FirSpec.lean` includes after the chapter on sums of dialects. It is a
document of its own so that `FirSpec.lean` keeps within the file-size
budget (ADR-2026-10-28-0724). Each section renders one module of
`lean/Fir`.
-/

#doc (Manual) "The GPU dialect" =>

The second dialect in tree, `gpu`, is shaped like a GPU kernel language
(ADR-2026-11-09-1545). A host module holds a device module, a module nested
in it whose dialect set names `gpu`, and the kernels are the device
module's functions. The device module has no data layout of its own: its
pointer types name the memories of its host's layout (ADR-2026-11-12-1821).
Work-group memory is one of them, any memory that the layout declares:
`gpu` owns no memory, and its op `gpu.work_group_alloca` gives a declared
memory its meaning by allocating there for the whole run of the kernel (the
human's ruling of 2026-11-16 on #212). `gpu` is terminal: it has no lowering to the core and no native backend
(ADR-2026-11-09-1544). In M1 a kernel runs one work-item at a time, with
its ids given as inputs, and no op of `gpu` needs another work-item. This
chapter gives its abstract syntax, text, rules and effects, the laws of its
text, the rules by which a work-item runs, how it allocates in work-group
memory, the guarantees of the sum of the core and `gpu`, for the functions of every table of a valid module, a device
module's kernels included, and the modes that `fir-ref run` walks.

{includeReadable "." Fir.Gpu.Ops "Abstract syntax" FirSpec.Gpu.Ops (level := 1)}

{includeReadable "." Fir.Gpu.Text "Text" FirSpec.Gpu.Text (level := 1)}

{includeReadable "." Fir.Gpu.Validation "Validation" FirSpec.Gpu.Validation (level := 1)}

{includeReadable "." Fir.Gpu.Effects "Effects" FirSpec.Gpu.Effects (level := 1)}

{includeReadable "." Fir.Gpu.TextLaws "The text is lawful" FirSpec.Gpu.TextLaws (level := 1)}

{includeReadable "." Fir.Gpu.Semantics "Execution" FirSpec.Gpu.Semantics (level := 1)}

{includeReadable "." Fir.Gpu.WorkGroup "Work-group allocation" FirSpec.Gpu.WorkGroup (level := 1)}

{includeReadable "." Fir.Gpu.Runs "Runs of the core and gpu" FirSpec.Gpu.Runs (level := 1)}

{includeReadable "." Fir.Gpu.Modes "Modes of the core and gpu" FirSpec.Gpu.Modes (level := 1)}

{includeReadable "." Fir.Gpu.Trace "Traced runs of the core and gpu" FirSpec.Gpu.Trace (level := 1)}

{includeReadable "." Fir.Gpu.EndModes "Modes of the core and gpu that see the end of a return" FirSpec.Gpu.EndModes (level := 1)}
