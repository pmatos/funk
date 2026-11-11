import Fir
import FirRef
import FirRef.Main
import FirTest.Axioms
import FirTest.Parse
import FirTest.Print
import FirTest.PrintInt
import FirTest.Run
import FirTest.Interpreter
import FirTest.Modes
import FirTest.Sample
import FirTest.RunSteps
import FirTest.Lookup
import FirTest.Bitwise
import FirTest.Width
import FirTest.PoisonOp
import FirTest.Div
import FirTest.Compare
import FirTest.FloatCompare
import FirTest.Branch
import FirTest.Unreachable
import FirTest.Loops
import FirTest.Lex
import FirTest.Decode
import FirTest.Read
import FirTest.ReadDeep
import FirTest.ValidateOps
import FirTest.Validate
import FirTest.ValidateNested
import FirTest.LocTable
import FirTest.Dominance
import FirTest.OverCore
import FirTest.Toy
import FirTest.UseOnce
import FirTest.RegionKinds
import FirTest.RegionKindCases
import FirTest.Mixed
import FirTest.SumTypes
import FirTest.Bit
import FirTest.DialectSet
import FirTest.ItemKinds
import FirTest.Deps
import FirTest.Runs
import FirTest.ValidSum
import FirTest.RunsLoops
import FirTest.Calls
import FirTest.RunsCalls
import FirTest.RefineCalls
import FirTest.Lawful
import FirTest.LawfulRefine
import FirTest.Effects
import FirTest.EffectCases
import FirTest.SummaryCases
import FirTest.Memory
import FirTest.MemoryRuns
import FirTest.MemoryObligations
import FirTest.MemoryStoreReads
import FirTest.PrintParse
import FirTest.ParseWellFormed
import FirTest.G0
import FirTest.G0Effects
import FirTest.FloatModel
import FirTest.FloatModelFma
import FirTest.FloatModelF16
import FirTest.FloatModelBf16
import FirTest.FloatModelF128

/-!
The Lean tests. Building this library runs their checks. This root module
imports every module of `lean/`, and its last command checks that each of
their declarations, and each of its own, is trusted (ADR-2026-10-30-1452).
Nothing may follow that command, since the check would not see it.
-/

#check_axioms Fir FirRef FirTest
