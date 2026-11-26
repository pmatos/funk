import VersoManual
import Fir
import FirSpecSite.ReadableElab
import FirSpec.ReadableDocs

open Verso.Genre Manual
open FirSpecSite

set_option pp.rawOnError true

/-!
The chapter on traces of the fir specification, which `FirSpec.lean`
includes after the chapter on memory. It is a document of its own so that
the chapter on memory keeps within the file-size budget
(ADR-2026-10-28-0724). Each section renders one module of `lean/Fir`.
-/

#doc (Manual) "Traces" =>

The events that a run shows to the world outside it, the layer in which a
run shows them, and refinement of the traced runs of functions for every
world (ADR-2026-11-09-1540), what the world sees, the core's events, what
an external call lets escape and the core's rule for one, and the core's
traced runs, on which refined arguments and congruence in the callee hold.

{includeReadable "." Fir.Execution.Trace "Traces of events" FirSpec.Execution.Trace (level := 1)}

{includeReadable "." Fir.Execution.TraceMonad "The traced layer" FirSpec.Execution.TraceMonad (level := 1)}

{includeReadable "." Fir.Execution.TraceRuns "Traced runs" FirSpec.Execution.TraceRuns (level := 1)}

{includeReadable "." Fir.Execution.TraceWorld "The world and escaped memory" FirSpec.Execution.TraceWorld (level := 1)}

{includeReadable "." Fir.Execution.TraceScript "Scripted worlds" FirSpec.Execution.TraceScript (level := 1)}

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

{includeReadable "." Fir.Execution.TraceStepWays "The ways a traced step goes on" FirSpec.Execution.TraceStepWays (level := 1)}

{includeReadable "." Fir.Execution.TraceStepPaths "A traced run of ops, one step at a time" FirSpec.Execution.TraceStepPaths (level := 1)}

{includeReadable "." Fir.Execution.TraceCallSource "A traced call of the target, followed back" FirSpec.Execution.TraceCallSource (level := 1)}

{includeReadable "." Fir.Execution.TraceOpsRefine "A traced run of ops on refined environments and states" FirSpec.Execution.TraceOpsRefine (level := 1)}

{includeReadable "." Fir.Execution.TraceArgs "Refined arguments over traced runs: returns, UB and each budget" FirSpec.Execution.TraceArgs (level := 1)}

{includeReadable "." Fir.Execution.TraceSteps "The first steps of a marked trace" FirSpec.Execution.TraceSteps (level := 1)}

{includeReadable "." Fir.Execution.TraceFinite "Ops of finitely many outcomes, given the world's answers" FirSpec.Execution.TraceFinite (level := 1)}

{includeReadable "." Fir.Execution.TraceKonig "Divergence of a traced run, by König's lemma" FirSpec.Execution.TraceKonig (level := 1)}

{includeReadable "." Fir.Execution.TraceChain "Calls between two steps" FirSpec.Execution.TraceChain (level := 1)}

{includeReadable "." Fir.Execution.TracePace "The fuel of a return" FirSpec.Execution.TracePace (level := 1)}

{includeReadable "." Fir.Execution.TraceCut "Truncated paths and cuts" FirSpec.Execution.TraceCut (level := 1)}

{includeReadable "." Fir.Execution.TraceTruncate "Truncating a traced run" FirSpec.Execution.TraceTruncate (level := 1)}

{includeReadable "." Fir.Execution.TraceFiniteRuns "Finitely many traces at one budget" FirSpec.Execution.TraceFiniteRuns (level := 1)}

{includeReadable "." Fir.Execution.TraceDiverge "Refined arguments over traced runs, divergence included" FirSpec.Execution.TraceDiverge (level := 1)}

{includeReadable "." Fir.Execution.TraceAhead "More fuel, in the traced layer" FirSpec.Execution.TraceAhead (level := 1)}

{includeReadable "." Fir.Execution.TraceBlackBox "Two modules in the traced layer, compared call by call" FirSpec.Execution.TraceBlackBox (level := 1)}

{includeReadable "." Fir.Execution.TraceBranch "Streams of acts and branches of moves" FirSpec.Execution.TraceBranch (level := 1)}

{includeReadable "." Fir.Execution.TraceCallPace "A callee's return, paced" FirSpec.Execution.TraceCallPace (level := 1)}

{includeReadable "." Fir.Execution.TraceMoves "Configurations and their moves" FirSpec.Execution.TraceMoves (level := 1)}

{includeReadable "." Fir.Execution.TraceGuard "Guards: the source path that a proof of refinement picks" FirSpec.Execution.TraceGuard (level := 1)}

{includeReadable "." Fir.Execution.TraceCallsAllowed "Every return and UB of the target, allowed, call by call" FirSpec.Execution.TraceCallsAllowed (level := 1)}

{includeReadable "." Fir.Execution.TraceArgsFrom "Refined arguments over traced runs from a given traced state" FirSpec.Execution.TraceArgsFrom (level := 1)}

{includeReadable "." Fir.Execution.TraceReplace "Congruence in the callee over traced runs: returns and UB" FirSpec.Execution.TraceReplace (level := 1)}

{includeReadable "." Fir.Execution.TraceMoveCases "How a run goes on by moves" FirSpec.Execution.TraceMoveCases (level := 1)}

{includeReadable "." Fir.Execution.TraceMoveFinite "Finitely many moves" FirSpec.Execution.TraceMoveFinite (level := 1)}

{includeReadable "." Fir.Execution.TraceGood "A stream at unboundedly many budgets" FirSpec.Execution.TraceGood (level := 1)}

{includeReadable "." Fir.Execution.TraceMoveSel "The pigeonhole step" FirSpec.Execution.TraceMoveSel (level := 1)}

{includeReadable "." Fir.Execution.TraceTargetBranch "The target's branch" FirSpec.Execution.TraceTargetBranch (level := 1)}

{includeReadable "." Fir.Execution.TraceShowsObs "Streams and outcomes that diverge" FirSpec.Execution.TraceShowsObs (level := 1)}

{includeReadable "." Fir.Execution.TraceFollow "The source follows the target" FirSpec.Execution.TraceFollow (level := 1)}

{includeReadable "." Fir.Execution.TraceFollowStep "One move of the source" FirSpec.Execution.TraceFollowStep (level := 1)}

{includeReadable "." Fir.Execution.TraceCalleeDiverge "Divergence across black boxes" FirSpec.Execution.TraceCalleeDiverge (level := 1)}

{includeReadable "." Fir.Execution.TraceReplaceDiverge "Congruence in the callee over traced runs, divergence included" FirSpec.Execution.TraceReplaceDiverge (level := 1)}

{includeReadable "." Fir.Execution.TraceLiftFrom "Traced runs from a traced state, for a dialect that lifts its semantics with memory" FirSpec.Execution.TraceLiftFrom (level := 1)}

{includeReadable "." Fir.Execution.TraceSeen "What the world sees" FirSpec.Execution.TraceSeen (level := 1)}

{includeReadable "." Fir.Core.Event "The core's events" FirSpec.Core.Event (level := 1)}

{includeReadable "." Fir.Execution.TraceEscape "What an external call lets escape" FirSpec.Execution.TraceEscape (level := 1)}

{includeReadable "." Fir.Execution.TraceEscapeLaws "What an external call lets escape is the closure" FirSpec.Execution.TraceEscapeLaws (level := 1)}

{includeReadable "." Fir.Execution.TraceWorldRefine "What the world gives, on refined traced states" FirSpec.Execution.TraceWorldRefine (level := 1)}

{includeReadable "." Fir.Core.ExtCallRule "The core's traced external-call rule" FirSpec.Core.ExtCallRule (level := 1)}

{includeReadable "." Fir.Core.Trace "The core's traced runs" FirSpec.Core.Trace (level := 1)}

{includeReadable "." Fir.Execution.MemoryEndModes "Modes that see the end of a return" FirSpec.Execution.MemoryEndModes (level := 1)}
