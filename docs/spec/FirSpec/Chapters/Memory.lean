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
Between the model and the effect, it says which addresses an exposed
allocation may be given and which one `fir-ref` gives, how a run's address
policy picks one, and how a value of
an integer, a float or a pointer type becomes units of a memory, and units
a value again, at every byte order. It ends with traces: the events that a
run shows to the world outside it, the layer in which a run shows them, and
refinement of the traced runs of functions for every world
(ADR-2026-11-09-1540), and the core's traced runs, on which refined
arguments and congruence in the callee hold while the core shows no
event.

{includeReadable "." Fir.Memory.Model "The memory model" FirSpec.Memory.Model (level := 1)}

{includeReadable "." Fir.Memory.Laws "Memory laws" FirSpec.Memory.Laws (level := 1)}

{includeReadable "." Fir.Memory.AlignLaws "Aligned access laws" FirSpec.Memory.AlignLaws (level := 1)}

{includeReadable "." Fir.Memory.Ordering "The ordering of an access" FirSpec.Memory.Ordering (level := 1)}

{includeReadable "." Fir.Memory.Frames "The memories of a run" FirSpec.Memory.Frames (level := 1)}

{includeReadable "." Fir.Memory.FrameLaws "Frame laws" FirSpec.Memory.FrameLaws (level := 1)}

{includeReadable "." Fir.Memory.Refine "Refining memories" FirSpec.Memory.Refine (level := 1)}

{includeReadable "." Fir.Memory.Address "Addresses" FirSpec.Memory.Address (level := 1)}

{includeReadable "." Fir.Memory.AddressLaws "Address laws" FirSpec.Memory.AddressLaws (level := 1)}

{includeReadable "." Fir.Memory.CanonicalLaws "Canonical layout laws" FirSpec.Memory.CanonicalLaws (level := 1)}

{includeReadable "." Fir.Memory.ExposeLaws "Exposure laws" FirSpec.Memory.ExposeLaws (level := 1)}

{includeReadable "." Fir.Memory.Policy "Address policies" FirSpec.Memory.Policy (level := 1)}

{includeReadable "." Fir.Memory.PolicyLaws "Address policy laws" FirSpec.Memory.PolicyLaws (level := 1)}

{includeReadable "." Fir.Memory.Encode "Values in units" FirSpec.Memory.Encode (level := 1)}

{includeReadable "." Fir.Memory.EncodeLaws "Laws of values in units" FirSpec.Memory.EncodeLaws (level := 1)}

{includeReadable "." Fir.Core.Encode "The core's values in memory" FirSpec.Core.Encode (level := 1)}

{includeReadable "." Fir.Execution.MemoryEffect "The memory effect" FirSpec.Execution.MemoryEffect (level := 1)}

{includeReadable "." Fir.Execution.MemoryState "The state layer" FirSpec.Execution.MemoryState (level := 1)}

{includeReadable "." Fir.Execution.MemoryRuns "Runs with memory" FirSpec.Execution.MemoryRuns (level := 1)}

{includeReadable "." Fir.Execution.StatePaths "How a run with memory ends" FirSpec.Execution.StatePaths (level := 1)}

{includeReadable "." Fir.Execution.MemoryMonotone "Runs with memory at every budget" FirSpec.Execution.MemoryMonotone (level := 1)}

{includeReadable "." Fir.Execution.RunItems "The items a run gives each op" FirSpec.Execution.RunItems (level := 1)}

{includeReadable "." Fir.Execution.MemoryObligations "Memory obligations" FirSpec.Execution.MemoryObligations (level := 1)}

{includeReadable "." Fir.Execution.MemoryObligationLaws "Meeting the memory obligations" FirSpec.Execution.MemoryObligationLaws (level := 1)}

{includeReadable "." Fir.Execution.MemoryTotal "Totality with memory" FirSpec.Execution.MemoryTotal (level := 1)}

{includeReadable "." Fir.Execution.MemoryCallSteps "The steps of a call, with memory" FirSpec.Execution.MemoryCallSteps (level := 1)}

{includeReadable "." Fir.Execution.MemoryProgress "Progress and no stuck path, with memory" FirSpec.Execution.MemoryProgress (level := 1)}

{includeReadable "." Fir.Execution.MemoryLocal "Progress and no stuck path with memory, without calls" FirSpec.Execution.MemoryLocal (level := 1)}

{includeReadable "." Fir.Execution.MemoryOpRefine "Monotonicity with memory" FirSpec.Execution.MemoryOpRefine (level := 1)}

{includeReadable "." Fir.Execution.MemoryPoison "Poison obligations with memory" FirSpec.Execution.MemoryPoison (level := 1)}

{includeReadable "." Fir.Execution.MemoryStepPaths "The ways a step with memory goes on" FirSpec.Execution.MemoryStepPaths (level := 1)}

{includeReadable "." Fir.Execution.MemoryCalls "Runs from given memories" FirSpec.Execution.MemoryCalls (level := 1)}

{includeReadable "." Fir.Execution.MemoryBlackBox "Calls as black boxes, with memory" FirSpec.Execution.MemoryBlackBox (level := 1)}

{includeReadable "." Fir.Execution.MemoryRefineUp "Returns and UB with memory, followed back" FirSpec.Execution.MemoryRefineUp (level := 1)}

{includeReadable "." Fir.Execution.MemoryRefineDown "Running out of fuel with memory, followed back" FirSpec.Execution.MemoryRefineDown (level := 1)}

{includeReadable "." Fir.Execution.MemoryRefineRuns "Refined arguments and memories" FirSpec.Execution.MemoryRefineRuns (level := 1)}

{includeReadable "." Fir.Execution.MemoryReplace "Replacing a callee, with memory" FirSpec.Execution.MemoryReplace (level := 1)}

{includeReadable "." Fir.Execution.MemoryFinite "Ops of finitely many outcomes" FirSpec.Execution.MemoryFinite (level := 1)}

{includeReadable "." Fir.Execution.MemoryFiniteDown "Divergence with ops of finitely many outcomes" FirSpec.Execution.MemoryFiniteDown (level := 1)}

{includeReadable "." Fir.Execution.MemoryFiniteReplace "Congruence in the callee with ops of finitely many outcomes" FirSpec.Execution.MemoryFiniteReplace (level := 1)}

{includeReadable "." Fir.Execution.MemoryFree "Touching no memory" FirSpec.Execution.MemoryFree (level := 1)}

{includeReadable "." Fir.Execution.MemoryFreeRuns "Runs that touch no memory" FirSpec.Execution.MemoryFreeRuns (level := 1)}

{includeReadable "." Fir.Execution.MemoryFreeReplace "Congruence in a callee that touches no memory" FirSpec.Execution.MemoryFreeReplace (level := 1)}

{includeReadable "." Fir.Execution.MemoryModes "Modes with memory" FirSpec.Execution.MemoryModes (level := 1)}

{includeReadable "." Fir.Execution.NaNModes "Exhaustive runs that try a few NaNs" FirSpec.Execution.NaNModes (level := 1)}

{includeReadable "." Fir.Execution.MemoryAllocLaws "Allocation in the state layer" FirSpec.Execution.MemoryAllocLaws (level := 1)}

{includeReadable "." Fir.Execution.MemoryLoadLaws "Loads in the state layer" FirSpec.Execution.MemoryLoadLaws (level := 1)}

{includeReadable "." Fir.Execution.MemoryStoreLaws "Stores in the state layer" FirSpec.Execution.MemoryStoreLaws (level := 1)}

{includeReadable "." Fir.Execution.MemoryBindLaws "Sequences in the state layer" FirSpec.Execution.MemoryBindLaws (level := 1)}

{includeReadable "." Fir.Execution.MemoryCopyLaws "Copies of units in the state layer" FirSpec.Execution.MemoryCopyLaws (level := 1)}

{includeReadable "." Fir.Execution.MemoryExposeLaws "Exposing in the state layer" FirSpec.Execution.MemoryExposeLaws (level := 1)}

{includeReadable "." Fir.Execution.MemoryPolicyRuns "Runs under every address policy" FirSpec.Execution.MemoryPolicyRuns (level := 1)}

{includeReadable "." Fir.Execution.MemoryChoiceLaws "Choices in the state layer" FirSpec.Execution.MemoryChoiceLaws (level := 1)}

{includeReadable "." Fir.Core.Alloca "Stack allocation rules" FirSpec.Core.Alloca (level := 1)}

{includeReadable "." Fir.Core.Load "Load rules" FirSpec.Core.Load (level := 1)}

{includeReadable "." Fir.Core.Store "Store rules" FirSpec.Core.Store (level := 1)}

{includeReadable "." Fir.Core.PtrAccess "Pointer load and store rules" FirSpec.Core.PtrAccess (level := 1)}

{includeReadable "." Fir.Core.FloatAccess "Float load and store rules" FirSpec.Core.FloatAccess (level := 1)}

{includeReadable "." Fir.Core.MemCopy "Copy and move rules" FirSpec.Core.MemCopy (level := 1)}

{includeReadable "." Fir.Core.MemSet "Fill rules" FirSpec.Core.MemSet (level := 1)}

{includeReadable "." Fir.Core.FieldAddr "Field address rules" FirSpec.Core.FieldAddr (level := 1)}

{includeReadable "." Fir.Core.MemRules "The core's rules with memory" FirSpec.Core.MemRules (level := 1)}

{includeReadable "." Fir.Core.AllocaLaws "Stack allocation obligations" FirSpec.Core.AllocaLaws (level := 1)}

{includeReadable "." Fir.Core.LoadLaws "Load obligations" FirSpec.Core.LoadLaws (level := 1)}

{includeReadable "." Fir.Core.LoadReads "A load declared without a read" FirSpec.Core.LoadReads (level := 1)}

{includeReadable "." Fir.Core.StoreLaws "Store obligations" FirSpec.Core.StoreLaws (level := 1)}

{includeReadable "." Fir.Core.StoreWrites "A store declared without a write" FirSpec.Core.StoreWrites (level := 1)}

{includeReadable "." Fir.Core.LoadPtrLaws "Pointer load obligations" FirSpec.Core.LoadPtrLaws (level := 1)}

{includeReadable "." Fir.Core.StorePtrLaws "Pointer store obligations" FirSpec.Core.StorePtrLaws (level := 1)}

{includeReadable "." Fir.Core.LoadFloatLaws "Float load obligations" FirSpec.Core.LoadFloatLaws (level := 1)}

{includeReadable "." Fir.Core.StoreFloatLaws "Float store obligations" FirSpec.Core.StoreFloatLaws (level := 1)}

{includeReadable "." Fir.Core.MemCopyLaws "Copy and move obligations" FirSpec.Core.MemCopyLaws (level := 1)}

{includeReadable "." Fir.Core.MemCopyPoison "Copy and move poison obligations" FirSpec.Core.MemCopyPoison (level := 1)}

{includeReadable "." Fir.Core.MemSetLaws "Fill obligations" FirSpec.Core.MemSetLaws (level := 1)}

{includeReadable "." Fir.Core.MemSetPoison "Fill poison obligations" FirSpec.Core.MemSetPoison (level := 1)}

{includeReadable "." Fir.Core.FieldAddrLaws "Field address obligations" FirSpec.Core.FieldAddrLaws (level := 1)}

{includeReadable "." Fir.Core.TreeRules "The core dialect in the tree of choices" FirSpec.Core.TreeRules (level := 1)}

{includeReadable "." Fir.Core.Modes "The core dialect's modes" FirSpec.Core.Modes (level := 1)}

{includeReadable "." Fir.Core.MemoryRuns "Core functions with memory" FirSpec.Core.MemoryRuns (level := 1)}

{includeReadable "." Fir.Core.MemoryCallRefine "Congruence in a core callee" FirSpec.Core.MemoryCallRefine (level := 1)}

{includeReadable "." Fir.Execution.Trace "Traces of events" FirSpec.Execution.Trace (level := 1)}

{includeReadable "." Fir.Execution.TraceMonad "The traced layer" FirSpec.Execution.TraceMonad (level := 1)}

{includeReadable "." Fir.Execution.TraceRuns "Traced runs" FirSpec.Execution.TraceRuns (level := 1)}

{includeReadable "." Fir.Execution.TraceWorld "The world and escaped memory" FirSpec.Execution.TraceWorld (level := 1)}

{includeReadable "." Fir.Execution.Observe "Pointers under a renaming" FirSpec.Execution.Observe (level := 1)}

{includeReadable "." Fir.Core.Observe "The pointers of the core's values" FirSpec.Core.Observe (level := 1)}

{includeReadable "." Fir.Execution.ObserveEnd "The end of a return" FirSpec.Execution.ObserveEnd (level := 1)}

{includeReadable "." Fir.Execution.ObserveEndLaws "Laws of the end of a return" FirSpec.Execution.ObserveEndLaws (level := 1)}

{includeReadable "." Fir.Execution.TraceDialect "A dialect's traced runs" FirSpec.Execution.TraceDialect (level := 1)}

{includeReadable "." Fir.Execution.TraceLift "Traced runs of a dialect with no event" FirSpec.Execution.TraceLift (level := 1)}

{includeReadable "." Fir.Execution.TraceRefine "Refinement over the traced runs of a dialect with no event" FirSpec.Execution.TraceRefine (level := 1)}

{includeReadable "." Fir.Execution.TraceObligations "Monotonicity in the traced layer" FirSpec.Execution.TraceObligations (level := 1)}

{includeReadable "." Fir.Execution.TraceObligationLaws "Ops monotone in the traced layer" FirSpec.Execution.TraceObligationLaws (level := 1)}

{includeReadable "." Fir.Execution.TracePaths "Paths of the interpreter in the traced layer" FirSpec.Execution.TracePaths (level := 1)}

{includeReadable "." Fir.Execution.TraceStepPaths "A traced run of ops, one step at a time" FirSpec.Execution.TraceStepPaths (level := 1)}

{includeReadable "." Fir.Execution.TraceOpsRefine "A traced run of ops on refined environments and states" FirSpec.Execution.TraceOpsRefine (level := 1)}

{includeReadable "." Fir.Execution.TraceArgs "Refined arguments over traced runs: returns, UB and each budget" FirSpec.Execution.TraceArgs (level := 1)}

{includeReadable "." Fir.Core.Trace "The core's traced runs" FirSpec.Core.Trace (level := 1)}
