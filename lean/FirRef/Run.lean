import Std.Data.HashSet
import Fir
import FirRef.Utf8
import FirRef.Report
import FirRef.Sample
import FirRef.MachineModes
import FirRef.HVectorSum
import FirRef.RunNaN
import FirRef.RunText

/-!
What `fir-ref run` does with a file: it parses it with the dialects in tree,
the core and `gpu`, runs one of its functions, or a kernel of one of its
nested modules, as one work-item (`Gpu.WorkItem`) with the spec's
interpreter, `Func.run`, and reports the result as one JSON object on one
line (`docs/decisions/fir-ref-command-line.md#fir-ref-run`).

`freeze` of poison makes a choice, so a run may end in many ways.
`fir-ref` runs the interpreter in the state layer over the spec's tree of
choices, from the memories that hold the globals of the function's table,
with the rules of the core and `gpu`, and
walks the tree in one of the modes below, the spec's `Gpu.scripted`,
`Gpu.exhaustive`, `Gpu.exhaustiveNaN` and `Gpu.sampled`, which Lean proves
sound for the runs with memory (`Gpu.scripted_memOutcomes`,
`Gpu.exhaustive_memOutcomes`, `Gpu.exhaustiveNaN_memOutcomes` and
`Gpu.sampled_memOutcomes`):

* scripted mode, the default, follows the one path that a choice sequence
  names, given with `--choices`, and reports its one outcome. With no
  `--choices`, the sequence is empty, so a run that makes no choice
  reports its one outcome, with a count of `0` choices, and one that makes
  a choice is an error;
* exhaustive mode, `--exhaustive`, reports every outcome of the run, when
  no path chooses more bits in all than its budget, `--choice-bits`;
* with `--nans`, exhaustive mode tries, at each NaN choice of a float op,
  only the positive quiet NaN and the NaNs it is given, the spec's
  `Gpu.exhaustiveNaN`: each outcome it reports is one of the run's
  (`Gpu.exhaustiveNaN_memOutcomes`), and all of them when no path made a NaN
  choice (`Gpu.exhaustiveNaN_exact`);
* sampled mode, `--seed`, follows the path on which a generator seeded
  with its number draws each choice, the spec's `Gpu.sampled`, and
  reports its one outcome and the values it drew, a sequence that
  `--choices` takes (`Gpu.sampled_fits`).

Each says how many choices a path made. An op without rules has no outcome in
the spec, so a path that reaches one is reported as an error, not as a result
(`docs/decisions/fir-ref.md#an-op-without-rules`), and so is a choice sequence
that does not fit the run.

Arguments, choices and values are spelled as constants are in text: `true`
and `false` at `i1`, signed decimal at every other width, and the one
float literal of a float's bits at a float type (ADR-2026-11-11-1438), read
with the spec's lexer and checked with `Core.Op.decode` (`FirRef.readArg`,
in `FirRef.RunArgs`). `fir-ref` runs the spec's lexer as `argAttrP`, which lexes at most two tokens over the text's
positions, with no stack per character (`argAttr_eq_argAttrP`). A value or
an argument may also be `poison`, at any `iN` or float type, so that a run may start from
poison, as the runs of `Core.FuncRuns` do (#123). A choice may not:
`freeze` chooses a value of its type.
-/

namespace FirRef

open Fir

/-! # Fills

The spec's `memset` rule builds its `len` units before the store looks at
the allocation; `memTreeFast` first finds where the store lands and is UB
at once where it would fault, so a fill out of bounds builds no units
(`docs/decisions/fir-ref-fast-paths.md#fills`). The `@[csimp]` swap comes
before the modes below, so their calls of `Core.memTreeDenote` reach it.
-/

section Fills

open Fir.Core Fir.Memory

variable {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : Core.Mem → N)

local notation "TM" => StateT (Memories N (unitsOf lay)) (ChoiceTree Core.Op)

/-- `setLenRule` in the layer over the tree of choices, which first finds
where the store of a length other than 0 lands, and is UB at once where it
would fault. -/
def setLenFast (v n len : Nat) (p : PoisonOr Pointer) (x : PoisonOr (BitVec v)) :
    TM (HVector toType ([] : List Ty)) :=
  match p with
  | .value q => fun S =>
    if len = 0 then setLenRule (m := TM) lay ρ v n len p x S else
      match (S.mem (ρ n)).locate q len with
      | .error f => MonadUB.ub f.reason
      | .ok _ => setLenRule (m := TM) lay ρ v n len p x S
  | .poison => setLenRule lay ρ v n len p x

theorem setLenFast_eq (v n len : Nat) (p : PoisonOr Pointer) (x : PoisonOr (BitVec v)) :
    setLenFast lay ρ v n len p x = setLenRule (m := TM) lay ρ v n len p x := by
  cases p with
  | poison => rfl
  | value q =>
    funext S
    simp only [setLenFast]
    split
    · rfl
    · rename_i hlen
      split
      · rename_i f hf
        have hs : S.store (ρ n) q (setUnits (lay (ρ n)) len x) 1 = .error f := by
          simp only [Memories.store, Memory.storeAligned]
          rw [Memory.store_of_locate_error (by simpa [setUnits] using hf)]
          rfl
        simp only [setLenRule, hlen, ↓reduceIte]
        show _ = StateT.map _ (MonadMemory.store (m := TM) (ρ n) q (setUnits (lay (ρ n)) len x) 1) S
        simp only [StateT.map, MonadMemory.store, hs]
        rfl
      · rfl

/-- `memSetRule` in the layer over the tree of choices, by `setLenFast`. -/
def memSetFast (v w n : Nat) (p : PoisonOr Pointer) (x : PoisonOr (BitVec v)) :
    PoisonOr (BitVec w) → TM (HVector toType ([] : List Ty))
  | .value l => setLenFast lay ρ v n l.toNat p x
  | .poison => MonadChoice.choose w >>= fun l => setLenFast lay ρ v n l.toNat p x

theorem memSetFast_eq (v w n : Nat) (p : PoisonOr Pointer) (x : PoisonOr (BitVec v))
    (l : PoisonOr (BitVec w)) :
    memSetFast lay ρ v w n p x l = memSetRule (m := TM) lay ρ v w n p x l := by
  cases l <;> simp only [memSetFast, memSetRule, setLenFast_eq]

/-- `Op.memDenote?` in the layer over the tree of choices, with `memSet`'s
rule by `memSetFast`. -/
def memDenoteFast? (L : RunItems) (op : Core.Op) :
    Option (HVector toType (Fir.sig (d := CoreDialect) op) →
      TM (HVector toType (Fir.returnTypes (d := CoreDialect) op))) :=
  match op with
  | .memSet _ v w n => some fun
    | .cons p (.cons x (.cons l .nil)) => memSetFast lay ρ v w n p x l
  | op => op.memDenote? lay ρ L

/-- `Core.memTreeDenote`, with `memSet`'s rule by `memSetFast`. -/
@[instance_reducible] def memTreeFast (L : RunItems) : DialectDenote CoreDialect TM :=
  denoteWith (memDenoteFast? lay ρ L) (fun op => op.memExit? lay ρ)
    fun op _ => ChoiceTree.noOutcome op

@[csimp] theorem memTreeDenote_eq_memTreeFast : @Core.memTreeDenote = @memTreeFast := by
  funext N _ lay ρ L
  unfold Core.memTreeDenote memDenoteIn memTreeFast
  congr 1
  funext op
  cases op with
  | memSet o v w n =>
    show some _ = some _
    congr 1
    funext args
    match args with
    | .cons p (.cons x (.cons l .nil)) => exact (memSetFast_eq lay ρ v w n p x l).symm
  | _ => rfl

end Fills

/-! # The modes, by the machine

`runBytes` below calls the spec's `Gpu.scripted`, `Gpu.exhaustive`,
`Gpu.exhaustiveNaN` and `Gpu.sampled`, the modes of the sum of the core and
`gpu` at a work-item;
the core's own modes, `Core.scripted`, `Core.exhaustive` and
`Core.sampled`, are what it called before #212. The theorems here make Lean
compile calls of either as calls of
`FirRef.Machine`'s walks of the run
(`docs/decisions/fir-ref-fast-paths.md#running`), which take no stack per step,
per level of calls or per choice. They name the dialects in tree, so they
live in `fir-ref`'s command line, not in `FirRef.RunModes` (G0,
ADR-2026-11-03-0600).
-/

/-- The memories that a run of a function of `M`'s own table starts with,
each memory with its entry in `M`'s data layout, named by its number: the
core's, and the core's and `gpu`'s. -/
abbrev coreStart (M : Module CoreDialect) := RunItems.start CoreDialect M.layout.entry id M.runItems
abbrev gpuStart (M : Module CoreGpu) := RunItems.start CoreGpu M.layout.entry Gpu.memName M.runItems

/-- `Core.scripted`, by the machine, with the core's semantics in the layer
over the tree that the modes run: each memory with its entry in `M`'s data
layout, named by its number. -/
def runScripted {σ : Type} (read : (w : Nat) → σ → Option (BitVec w)) (M : Module CoreDialect)
    (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2))) (fuel : Nat)
    (cs : List σ) : Except (ChoiceTree.Misfit σ) (RunLeaf × Nat) :=
  letI := Core.memTreeDenote M.layout.entry id M.runItems
  Machine.scripted (unit := unitsOf M.layout.entry) M (coreStart M) read f args fuel cs

@[csimp] theorem scripted_eq_runScripted : @Core.scripted = @runScripted := by
  funext σ read M f args fuel cs
  letI := Core.memTreeDenote M.layout.entry id M.runItems
  exact (Machine.scripted_eq M _ read f args fuel cs).symm

/-- `Core.exhaustive`, by the machine. -/
def runExhaustive (M : Module CoreDialect) (f : Func CoreDialect)
    (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat) :
    Option (List (RunLeaf × Nat)) :=
  letI := Core.memTreeDenote M.layout.entry id M.runItems
  Machine.exhaustive (unit := unitsOf M.layout.entry) M (coreStart M) f args fuel budget

@[csimp] theorem exhaustive_eq_runExhaustive : @Core.exhaustive = @runExhaustive := by
  funext M f args fuel budget
  letI := Core.memTreeDenote M.layout.entry id M.runItems
  exact (Machine.exhaustive_eq M _ f args fuel budget).symm

/-- `Core.sampled`, by the machine. -/
def runSampled {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ) (M : Module CoreDialect)
    (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (g : γ) :
    RunLeaf × List ChoiceTree.Chosen :=
  letI := Core.memTreeDenote M.layout.entry id M.runItems
  Machine.sampled (unit := unitsOf M.layout.entry) M (coreStart M) draw f args fuel g

@[csimp] theorem sampled_eq_runSampled : @Core.sampled = @runSampled := by
  funext γ draw M f args fuel g
  letI := Core.memTreeDenote M.layout.entry id M.runItems
  exact (Machine.sampled_eq M _ draw f args fuel g).symm

/-- `Gpu.memTreeDenote`, with the sum's rules from `sumDenote`, whose moves of
vectors take no stack per value (#405). -/
@[instance_reducible] def gpuTreeDenote [Gpu.WorkItem] {N : Type} [DecidableEq N]
    (lay : N → MemLayout) (ρ : DialectEffects.Mem CoreGpu → N) (L : RunItems) :
    DialectDenote CoreGpu (StateT (Memory.Memories N (unitsOf lay)) (ChoiceTree Core.Op)) :=
  letI := Core.memTreeDenote lay (ρ ∘ DialectMemOver.ofBase (base := CoreDialect) (e := GpuExt)) L
  letI := Gpu.treeDenote lay ρ
  sumDenote

theorem gpuTreeDenote_eq [Gpu.WorkItem] {N : Type} [DecidableEq N] (lay : N → MemLayout)
    (ρ : DialectEffects.Mem CoreGpu → N) (L : RunItems) :
    gpuTreeDenote lay ρ L = Gpu.memTreeDenote lay ρ L := rfl

/-- `Gpu.scripted`, by the machine, with
the semantics of the core and `gpu` at the work-item in the layer over the
tree: each memory with its entry in `M`'s data layout, named by its
number. -/
def runGpuScripted [Gpu.WorkItem] {σ : Type} (read : (w : Nat) → σ → Option (BitVec w))
    (M : Module CoreGpu) (f : Func CoreGpu) (args : HVector toType (f.params.map (·.2)))
    (fuel : Nat) (cs : List σ) : Except (ChoiceTree.Misfit σ) (Gpu.Leaf × Nat) :=
  letI := gpuTreeDenote M.layout.entry Gpu.memName M.runItems
  Machine.scripted (unit := unitsOf M.layout.entry) M (gpuStart M) read f args fuel cs

@[csimp] theorem gpuScripted_eq_runGpuScripted : @Gpu.scripted = @runGpuScripted := by
  funext w σ read M f args fuel cs
  letI := Gpu.memTreeDenote M.layout.entry Gpu.memName M.runItems
  exact (Machine.scripted_eq M _ read f args fuel cs).symm

/-- `Gpu.exhaustive`, by the machine. -/
def runGpuExhaustive [Gpu.WorkItem] (M : Module CoreGpu) (f : Func CoreGpu)
    (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat) :
    Option (List (Gpu.Leaf × Nat)) :=
  letI := gpuTreeDenote M.layout.entry Gpu.memName M.runItems
  Machine.exhaustive (unit := unitsOf M.layout.entry) M (gpuStart M) f args fuel budget

@[csimp] theorem gpuExhaustive_eq_runGpuExhaustive : @Gpu.exhaustive = @runGpuExhaustive := by
  funext w M f args fuel budget
  letI := Gpu.memTreeDenote M.layout.entry Gpu.memName M.runItems
  exact (Machine.exhaustive_eq M _ f args fuel budget).symm

/-- `Gpu.sampled`, by the machine. -/
def runGpuSampled [Gpu.WorkItem] {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ)
    (M : Module CoreGpu) (f : Func CoreGpu) (args : HVector toType (f.params.map (·.2)))
    (fuel : Nat) (g : γ) : Gpu.Leaf × List ChoiceTree.Chosen :=
  letI := gpuTreeDenote M.layout.entry Gpu.memName M.runItems
  Machine.sampled (unit := unitsOf M.layout.entry) M (gpuStart M) draw f args fuel g

@[csimp] theorem gpuSampled_eq_runGpuSampled : @Gpu.sampled = @runGpuSampled := by
  funext w γ draw M f args fuel g
  letI := Gpu.memTreeDenote M.layout.entry Gpu.memName M.runItems
  exact (Machine.sampled_eq M _ draw f args fuel g).symm

/-- `Gpu.exhaustiveNaN`, by the machine. -/
def runGpuExhaustiveNaN [Gpu.WorkItem] (M : Module CoreGpu) (f : Func CoreGpu)
    (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat) (nans : List Nat) :
    Option (List (Gpu.Leaf × Nat × Nat)) :=
  letI := gpuTreeDenote M.layout.entry Gpu.memName M.runItems
  Machine.exhaustiveNaN (unit := unitsOf M.layout.entry) M (gpuStart M) f args fuel budget nans

@[csimp] theorem gpuExhaustiveNaN_eq_runGpuExhaustiveNaN :
    @Gpu.exhaustiveNaN = @runGpuExhaustiveNaN := by
  funext w M f args fuel budget nans
  letI := Gpu.memTreeDenote M.layout.entry Gpu.memName M.runItems
  exact (Machine.exhaustiveNaN_eq M _ f args fuel budget nans).symm

/-- How `fir-ref run` walks a run: scripted mode, with a choice sequence,
exhaustive mode, with a choice budget in bits, and, when it tries a few
NaNs, the NaNs it is given as bit patterns, or sampled mode, with the seed
of its generator. -/
inductive Mode where
  | scripted (choices : List String)
  | exhaustive (budget : Nat)
  | exhaustiveNaN (budget : Nat) (nans : List Nat)
  | sampled (seed : Nat)
  deriving DecidableEq, Repr

/-! # The modes that see the end of a return, by the machine

`fir-ref run --world` calls the spec's `Gpu.scriptedEnd`, `Gpu.exhaustiveEnd`,
`Gpu.exhaustiveNaNEnd` and `Gpu.sampledEnd`
(`docs/decisions/fir-ref-run-end.md`). The machine sees a return of the
values `vs` with the memories `S` at the end of its path as the end
`⟨vs, S, []⟩`: nothing escapes, since neither the core nor `gpu` shows an
event. The theorems below make Lean compile calls of those modes as calls of
the machine's walks, as the ones above do for the modes that see a return
as its values.
-/

/-- How the machine sees a return of a function of the module `M`: at its
end, the returned values `vs` with the memories `S` and nothing escaped. -/
def endOfRet [Gpu.WorkItem] (M : Module CoreGpu) (vs : List (DVal CoreGpu))
    (S : Memory.Memories Nat (unitsOf M.layout.entry)) : Gpu.RunEnd M :=
  ⟨vs, S, []⟩

/-- The spec's tree that sees each return at its end is the machine's, with
returns seen by `endOfRet`. -/
theorem endTree_eq [Gpu.WorkItem] (M : Module CoreGpu) (f : Func CoreGpu)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) :
    Gpu.endTree M f args fuel =
      letI := gpuTreeDenote M.layout.entry Gpu.memName M.runItems
      Machine.endTree (ε := Core.Op) (unit := unitsOf M.layout.entry) M (gpuStart M) (endOfRet M) f args fuel := by
  show _ <$> _ = Machine.endWith _ <$> _
  congr 1
  funext p
  rcases p with ⟨_ | _ | _, _⟩ <;> rfl

/-- `Gpu.scriptedEnd`, by the machine. -/
def runGpuScriptedEnd [Gpu.WorkItem] {σ : Type} (read : (w : Nat) → σ → Option (BitVec w)) (M : Module CoreGpu)
    (f : Func CoreGpu) (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (cs : List σ) :
    Except (ChoiceTree.Misfit σ) (Gpu.EndLeaf M × Nat) :=
  letI := gpuTreeDenote M.layout.entry Gpu.memName M.runItems
  Machine.scriptedWith (unit := unitsOf M.layout.entry) M (gpuStart M) (endOfRet M) read f args fuel cs

@[csimp] theorem gpuScriptedEnd_eq : @Gpu.scriptedEnd = @runGpuScriptedEnd := by
  funext w σ read M f args fuel cs
  letI := gpuTreeDenote M.layout.entry Gpu.memName M.runItems
  show (Gpu.endTree M f args fuel).script read cs 0 = _
  rw [endTree_eq]
  exact (Machine.scriptedWith_eq M _ _ read f args fuel cs).symm

/-- `Gpu.exhaustiveEnd`, by the machine. -/
def runGpuExhaustiveEnd [Gpu.WorkItem] (M : Module CoreGpu) (f : Func CoreGpu)
    (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat) :
    Option (List (Gpu.EndLeaf M × Nat)) :=
  letI := gpuTreeDenote M.layout.entry Gpu.memName M.runItems
  Machine.exhaustiveWith (unit := unitsOf M.layout.entry) M (gpuStart M) (endOfRet M) f args fuel budget

@[csimp] theorem gpuExhaustiveEnd_eq : @Gpu.exhaustiveEnd = @runGpuExhaustiveEnd := by
  funext w M f args fuel budget
  letI := gpuTreeDenote M.layout.entry Gpu.memName M.runItems
  show (Gpu.endTree M f args fuel).explore budget = _
  rw [endTree_eq]
  exact (Machine.exhaustiveWith_eq M _ _ f args fuel budget).symm

/-- `Gpu.exhaustiveNaNEnd`, by the machine. -/
def runGpuExhaustiveNaNEnd [Gpu.WorkItem] (M : Module CoreGpu) (f : Func CoreGpu)
    (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat) (nans : List Nat) :
    Option (List (Gpu.EndLeaf M × Nat × Nat)) :=
  letI := gpuTreeDenote M.layout.entry Gpu.memName M.runItems
  Machine.exhaustiveNaNWith (unit := unitsOf M.layout.entry) M (gpuStart M) (endOfRet M) f args fuel budget nans

@[csimp] theorem gpuExhaustiveNaNEnd_eq : @Gpu.exhaustiveNaNEnd = @runGpuExhaustiveNaNEnd := by
  funext w M f args fuel budget nans
  letI := gpuTreeDenote M.layout.entry Gpu.memName M.runItems
  show (Gpu.endTree M f args fuel).exploreNaN nans budget = _
  rw [endTree_eq]
  exact (Machine.exhaustiveNaNWith_eq M _ _ f args fuel budget nans).symm

/-- `Gpu.sampledEnd`, by the machine. -/
def runGpuSampledEnd [Gpu.WorkItem] {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ) (M : Module CoreGpu)
    (f : Func CoreGpu) (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (g : γ) :
    Gpu.EndLeaf M × List ChoiceTree.Chosen :=
  letI := gpuTreeDenote M.layout.entry Gpu.memName M.runItems
  Machine.sampledWith (unit := unitsOf M.layout.entry) M (gpuStart M) (endOfRet M) draw f args fuel g

@[csimp] theorem gpuSampledEnd_eq : @Gpu.sampledEnd = @runGpuSampledEnd := by
  funext w γ draw M f args fuel g
  letI := gpuTreeDenote M.layout.entry Gpu.memName M.runItems
  show (Gpu.endTree M f args fuel).sample draw g = _
  rw [endTree_eq]
  exact (Machine.sampledWith_eq M _ _ draw f args fuel g).symm

end FirRef
