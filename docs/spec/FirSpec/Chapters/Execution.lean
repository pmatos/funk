import VersoManual
import Fir
import FirSpecSite.ReadableElab
import FirSpec.ReadableDocs

open Verso.Genre Manual
open FirSpecSite

set_option pp.rawOnError true

/-!
The chapter on execution of the fir specification, which `FirSpec.lean`
includes as its third chapter. It is a document of its own so that
`FirSpec.lean` keeps within the file-size budget (ADR-2026-10-28-0724).
Each section renders one module of `lean/Fir`.
-/

#doc (Manual) "Execution" =>

{includeReadable "." Fir.Execution.Values "Values and refinement" FirSpec.Execution.Values (level := 1)}

{includeLiterate "." Fir.Execution.PoisonUB "Poison and immediate UB" (level := 1)}

{includeReadable "." Fir.Execution.Effects "Effects and op semantics" FirSpec.Execution.Effects (level := 1)}

{includeReadable "." Fir.Execution.Behaviour "Outcomes and behaviours" FirSpec.Execution.Behaviour (level := 1)}

{includeReadable "." Fir.Execution.Frame "The frame effect" FirSpec.Execution.Frame (level := 1)}

{includeReadable "." Fir.Execution.Fuel "Fuel and progress" FirSpec.Execution.Fuel (level := 1)}

{includeReadable "." Fir.Execution.Refinement "Refinement" FirSpec.Execution.Refinement (level := 1)}

{includeReadable "." Fir.Execution.OpEffects "Effect sets" FirSpec.Execution.OpEffects (level := 1)}

{includeReadable "." Fir.Execution.Propagation "Poison classes" FirSpec.Execution.Propagation (level := 1)}

{includeReadable "." Fir.Execution.EffectLaws "Effect obligations" FirSpec.Execution.EffectLaws (level := 1)}

{includeReadable "." Fir.Core.Values "Core values" FirSpec.Core.Values (level := 1)}

{includeReadable "." Fir.Core.OpEffects "Core effects" FirSpec.Core.OpEffects (level := 1)}

{includeReadable "." Fir.Core.Poison "Core poison classes" FirSpec.Core.Poison (level := 1)}

{includeReadable "." Fir.Core.Unlawful "Semantics the obligations reject" FirSpec.Core.Unlawful (level := 1)}

{includeReadable "." Fir.Execution.Interpreter "The interpreter" FirSpec.Execution.Interpreter (level := 1)}

{includeReadable "." Fir.Core.Arith "Arithmetic rules" FirSpec.Core.Arith (level := 1)}

{includeReadable "." Fir.Core.Wrap "Wrap flag rules" FirSpec.Core.Wrap (level := 1)}

{includeReadable "." Fir.Core.Freeze "The freeze rule" FirSpec.Core.Freeze (level := 1)}

{includeReadable "." Fir.Core.Bitwise "Bitwise and shift rules" FirSpec.Core.Bitwise (level := 1)}

{includeReadable "." Fir.Core.Width "Width change rules" FirSpec.Core.Width (level := 1)}

{includeReadable "." Fir.Core.Div "Division rules" FirSpec.Core.Div (level := 1)}

{includeReadable "." Fir.Core.Compare "Comparison and selection rules" FirSpec.Core.Compare (level := 1)}

{includeReadable "." Fir.Core.FloatCompare "Float comparison rules" FirSpec.Core.FloatCompare (level := 1)}

{includeReadable "." Fir.Core.Control "Control-flow rules" FirSpec.Core.Control (level := 1)}

{includeReadable "." Fir.Core.Branch "Branch rules" FirSpec.Core.Branch (level := 1)}

{includeReadable "." Fir.Core.Call "Call rules" FirSpec.Core.Call (level := 1)}

{includeReadable "." Fir.Core.Semantics "Core op semantics" FirSpec.Core.Semantics (level := 1)}

{includeReadable "." Fir.Core.ArithLaws "Constant obligations" FirSpec.Core.ArithLaws (level := 1)}

{includeReadable "." Fir.Core.WrapLaws "Arithmetic obligations" FirSpec.Core.WrapLaws (level := 1)}

{includeReadable "." Fir.Core.FreezeLaws "Freeze obligations" FirSpec.Core.FreezeLaws (level := 1)}

{includeReadable "." Fir.Core.BitwiseLaws "Bitwise and shift obligations" FirSpec.Core.BitwiseLaws (level := 1)}

{includeReadable "." Fir.Core.WidthLaws "Width change obligations" FirSpec.Core.WidthLaws (level := 1)}

{includeReadable "." Fir.Core.DivLaws "Division obligations" FirSpec.Core.DivLaws (level := 1)}

{includeReadable "." Fir.Core.CompareLaws "Comparison and selection obligations" FirSpec.Core.CompareLaws (level := 1)}

{includeReadable "." Fir.Core.FloatCompareLaws "Float comparison obligations" FirSpec.Core.FloatCompareLaws (level := 1)}

{includeReadable "." Fir.Core.ControlLaws "Control-flow obligations" FirSpec.Core.ControlLaws (level := 1)}

{includeReadable "." Fir.Core.BranchLaws "Branch obligations" FirSpec.Core.BranchLaws (level := 1)}

{includeReadable "." Fir.Execution.Morphism "Monad morphisms" FirSpec.Execution.Morphism (level := 1)}

{includeReadable "." Fir.Execution.ChoiceTree "Choice trees" FirSpec.Execution.ChoiceTree (level := 1)}

{includeReadable "." Fir.Execution.Modes "Exhaustive, scripted and sampled modes" FirSpec.Execution.Modes (level := 1)}

{includeReadable "." Fir.Execution.SetRuns "Reading a run path by path" FirSpec.Execution.SetRuns (level := 1)}

{includeReadable "." Fir.Execution.Monotone "The runs of a function, and fuel monotonicity" FirSpec.Execution.Monotone (level := 1)}

{includeReadable "." Fir.Execution.Environment "The environment of a run" FirSpec.Execution.Environment (level := 1)}

{includeReadable "." Fir.Execution.Progress "Progress and no stuck path" FirSpec.Execution.Progress (level := 1)}

{includeReadable "." Fir.Execution.Scoped "Scope along a run" FirSpec.Execution.Scoped (level := 1)}

{includeReadable "." Fir.Execution.Jumps "Progress with jumps and loops" FirSpec.Execution.Jumps (level := 1)}

{includeReadable "." Fir.Execution.CallSteps "What a call step needs" FirSpec.Execution.CallSteps (level := 1)}

{includeReadable "." Fir.Execution.Calls "Progress with calls" FirSpec.Execution.Calls (level := 1)}

{includeReadable "." Fir.Core.Runs "The runs of core functions" FirSpec.Core.Runs (level := 1)}

{includeReadable "." Fir.Core.CallFree "Core functions without calls" FirSpec.Core.CallFree (level := 1)}

{includeReadable "." Fir.Core.ValidRuns "Core functions with calls" FirSpec.Core.ValidRuns (level := 1)}

{includeReadable "." Fir.Execution.RunPaths "The ways a step goes on" FirSpec.Execution.RunPaths (level := 1)}

{includeReadable "." Fir.Execution.EnvRefine "Refined environments" FirSpec.Execution.EnvRefine (level := 1)}

{includeReadable "." Fir.Execution.BlackBox "Calls as black boxes" FirSpec.Execution.BlackBox (level := 1)}

{includeReadable "." Fir.Execution.RefineUp "Returns and UB, followed back" FirSpec.Execution.RefineUp (level := 1)}

{includeReadable "." Fir.Execution.RefineDown "Running out of fuel, followed back" FirSpec.Execution.RefineDown (level := 1)}

{includeReadable "." Fir.Execution.RefineRuns "Refined arguments" FirSpec.Execution.RefineRuns (level := 1)}

{includeReadable "." Fir.Execution.Replace "Replacing a callee" FirSpec.Execution.Replace (level := 1)}

{includeReadable "." Fir.Core.CallRefine "Refinement through core calls" FirSpec.Core.CallRefine (level := 1)}

{includeReadable "." Fir.Execution.Lawful "What the lawful class gives" FirSpec.Execution.Lawful (level := 1)}

{includeReadable "." Fir.Core.Lawful "The core dialect's poison obligations" FirSpec.Core.Lawful (level := 1)}

{includeReadable "." Fir.Core.EffectLaws "The core dialect's effect obligations" FirSpec.Core.EffectLaws (level := 1)}

{includeReadable "." Fir.Execution.Summary "Function summaries" FirSpec.Execution.Summary (level := 1)}

{includeReadable "." Fir.Execution.SummaryLaws "Joins and the walk" FirSpec.Execution.SummaryLaws (level := 1)}

{includeReadable "." Fir.Execution.SummaryFixpoint "The summary is the least fixpoint" FirSpec.Execution.SummaryFixpoint (level := 1)}

{includeReadable "." Fir.Execution.SummarySound "Function summaries are sound" FirSpec.Execution.SummarySound (level := 1)}
