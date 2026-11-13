import VersoManual
import Fir
import FirSpecSite.ReadableElab
import FirSpec.ReadableDocs

open Verso.Genre Manual
open FirSpecSite

set_option pp.rawOnError true

/-!
The chapter on memory of the fir specification, which `FirSpec.lean`
includes as its fourth chapter. It is a document of its own so that
`FirSpec.lean` keeps within the file-size budget (ADR-2026-10-28-0724).
Each section renders one module of `lean/Fir`.
-/

#doc (Manual) "Memory" =>

Memory is logical blocks in typed memories (ADR-2026-11-09-1542). This
chapter gives one memory of that model, written once for a unit of any
width, so that every memory of every dialect is an instance of it. It then
makes memory an effect of a run: the memories of a run, the effect that
ops ask for, the layer that adds the memories to a way of computing, the
runs of a function with memory and how they end, their fuel monotonicity,
the obligations that an op's declaration of its effects on memory puts on
its semantics, progress with memory, which asks each op to be total from
any memories, and refinement with memory, which refines memories unit by
unit and asks each op to be monotone from memories that refine others.
Between the model and the effect, it says how a value of an integer or a
pointer type becomes units of a memory, and units a value again, at every
byte order.

{includeReadable "." Fir.Memory.Model "The memory model" FirSpec.Memory.Model (level := 1)}

{includeReadable "." Fir.Memory.Laws "Memory laws" FirSpec.Memory.Laws (level := 1)}

{includeReadable "." Fir.Memory.Frames "The memories of a run" FirSpec.Memory.Frames (level := 1)}

{includeReadable "." Fir.Memory.FrameLaws "Frame laws" FirSpec.Memory.FrameLaws (level := 1)}

{includeReadable "." Fir.Memory.Refine "Refining memories" FirSpec.Memory.Refine (level := 1)}

{includeReadable "." Fir.Memory.Encode "Values in units" FirSpec.Memory.Encode (level := 1)}

{includeReadable "." Fir.Memory.EncodeLaws "Laws of values in units" FirSpec.Memory.EncodeLaws (level := 1)}

{includeReadable "." Fir.Core.Encode "The core's values in memory" FirSpec.Core.Encode (level := 1)}

{includeReadable "." Fir.Execution.MemoryEffect "The memory effect" FirSpec.Execution.MemoryEffect (level := 1)}

{includeReadable "." Fir.Execution.MemoryState "The state layer" FirSpec.Execution.MemoryState (level := 1)}

{includeReadable "." Fir.Execution.MemoryRuns "Runs with memory" FirSpec.Execution.MemoryRuns (level := 1)}

{includeReadable "." Fir.Execution.StatePaths "How a run with memory ends" FirSpec.Execution.StatePaths (level := 1)}

{includeReadable "." Fir.Execution.MemoryMonotone "Runs with memory at every budget" FirSpec.Execution.MemoryMonotone (level := 1)}

{includeReadable "." Fir.Execution.MemoryObligations "Memory obligations" FirSpec.Execution.MemoryObligations (level := 1)}

{includeReadable "." Fir.Execution.MemoryObligationLaws "Meeting the memory obligations" FirSpec.Execution.MemoryObligationLaws (level := 1)}

{includeReadable "." Fir.Execution.MemoryTotal "Totality with memory" FirSpec.Execution.MemoryTotal (level := 1)}

{includeReadable "." Fir.Execution.MemoryCallSteps "The steps of a call, with memory" FirSpec.Execution.MemoryCallSteps (level := 1)}

{includeReadable "." Fir.Execution.MemoryProgress "Progress and no stuck path, with memory" FirSpec.Execution.MemoryProgress (level := 1)}

{includeReadable "." Fir.Execution.MemoryOpRefine "Monotonicity with memory" FirSpec.Execution.MemoryOpRefine (level := 1)}

{includeReadable "." Fir.Execution.MemoryPoison "Poison obligations with memory" FirSpec.Execution.MemoryPoison (level := 1)}

{includeReadable "." Fir.Execution.MemoryStepPaths "The ways a step with memory goes on" FirSpec.Execution.MemoryStepPaths (level := 1)}

{includeReadable "." Fir.Execution.MemoryCalls "Runs from given memories" FirSpec.Execution.MemoryCalls (level := 1)}

{includeReadable "." Fir.Execution.MemoryBlackBox "Calls as black boxes, with memory" FirSpec.Execution.MemoryBlackBox (level := 1)}

{includeReadable "." Fir.Execution.MemoryRefineUp "Returns and UB with memory, followed back" FirSpec.Execution.MemoryRefineUp (level := 1)}

{includeReadable "." Fir.Execution.MemoryRefineDown "Running out of fuel with memory, followed back" FirSpec.Execution.MemoryRefineDown (level := 1)}

{includeReadable "." Fir.Execution.MemoryRefineRuns "Refined arguments and memories" FirSpec.Execution.MemoryRefineRuns (level := 1)}

{includeReadable "." Fir.Execution.MemoryReplace "Replacing a callee, with memory" FirSpec.Execution.MemoryReplace (level := 1)}

{includeReadable "." Fir.Execution.MemoryModes "Modes with memory" FirSpec.Execution.MemoryModes (level := 1)}

{includeReadable "." Fir.Core.MemRules "The core's rules with memory" FirSpec.Core.MemRules (level := 1)}

{includeReadable "." Fir.Core.TreeRules "The core dialect in the tree of choices" FirSpec.Core.TreeRules (level := 1)}

{includeReadable "." Fir.Core.Modes "The core dialect's modes" FirSpec.Core.Modes (level := 1)}

{includeReadable "." Fir.Core.MemoryRuns "Core functions with memory" FirSpec.Core.MemoryRuns (level := 1)}
