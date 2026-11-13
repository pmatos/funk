import Fir.Core.EffectLaws
import Fir.Execution.MemoryModes

/-!
# The core dialect's exhaustive, scripted and sampled runs

`fir-ref run` runs the core dialect's rules in the tree of choices. Each op
runs its rule, the same rule that the set monad's semantics runs; an op without
rules ends its path with no outcome, for that op, as the set monad gives it
none (`docs/decisions/fir-ref.md#an-op-without-rules`). `fir-ref` reports such
a path as an error.

Each op's semantics in the tree has the set monad's as its set: the rules
are written once for any monad, and the set of a tree keeps the steps of
a computation, the choice effect and UB.

The modes run the core dialect with memory (the section on modes with
memory): its rules in the tree, lifted into the state layer over the tree,
from the empty memories, where each memory's units are as wide as the run
says. No core op touches memory, so each op keeps the memories, as it does
in the core's semantics with memory, and the morphism through the layer
maps the one to the other at every naming of the core's memories. So the
theorems of exhaustive and scripted modes hold of the runs with memory of
every core function, on every argument vector, at every fuel budget; and
since the core's runs with memory are its runs, they hold of its runs in
the set monad too. `fir-ref` computes the exhaustive, scripted and sampled
modes defined below, and nothing else, to report a run. The values that
sampled mode chose fit the run, so it inherits scripted mode's theorems.

The theorems hold on every argument vector of the function's parameter types,
poison included, and `fir-ref run` takes `poison` as an argument of any `iN`. A
run on a poison argument is refined by the run with any value in its place,
calls and recursion included, as the section on refinement through core calls
proves. So the differential test harness, which checks compiled code against
`fir-ref`, runs native code, which holds no poison, on poison stand-ins in
place of each poison argument, and judges each result against the outcomes that
`fir-ref` lists for the run on the poison
(`docs/decisions/fir-ref.md#poison-arguments`).
-/

namespace Fir.Core

open Memory

/-- The core dialect's rules in the tree of choices. An op without rules
ends its path with no outcome, and names itself. -/
instance : DialectDenote CoreDialect (ChoiceTree Op) where
  denote op args := match op.denote? (m := ChoiceTree Op) with
    | some rule => rule args
    | none => .noOutcome op
  exit op args := match op.exit? (m := ChoiceTree Op) with
    | some rule => rule args
    | none => .noOutcome op

/-- `freeze`'s rule in the tree of choices denotes its rule in the set
monad. -/
theorem freezeValue_toSet {ε : Type} {w : Nat} (a : PoisonOr (BitVec w)) :
    (freezeValue (m := ChoiceTree ε) a).toSet = freezeValue a := by
  cases a with
  | value _ => rfl
  | poison => exact ChoiceTree.toSet_bind _ _

/-- A rule made by `ruleOfEv`, such as a division's, denotes in the tree of
choices what it denotes in the set monad. -/
theorem ruleOfEv_toSet {ε : Type} {w : Nat}
    (g : PoisonOr (BitVec w) → PoisonOr (BitVec w) → Ev (PoisonOr (BitVec w)))
    (args : HVector toType [i w, i w]) :
    (ruleOfEv (m := ChoiceTree ε) g args).toSet = ruleOfEv g args := by
  match args with
  | .cons a (.cons b .nil) =>
    simp only [ruleOfEv]
    cases g a b <;> rfl

/-- A terminator's rule made by `exitOfEv`, such as `cond_br`'s, denotes in
the tree of choices what it denotes in the set monad. -/
theorem exitOfEv_toSet {ε : Type} (e : Ev Exit) :
    (exitOfEv (m := ChoiceTree ε) e).toSet = exitOfEv e := by
  cases e <;> rfl

/-- The tree's semantics of each core op denotes the set monad's. -/
theorem mapsDenote : (ChoiceTree.toSetMorphism (ε := Op)).MapsDenote (d := CoreDialect) where
  denote
    | .add _ _, .cons _ (.cons _ .nil) | .sub _ _, .cons _ (.cons _ .nil)
    | .mul _ _, .cons _ (.cons _ .nil) | .and _, .cons _ (.cons _ .nil)
    | .or _, .cons _ (.cons _ .nil) | .xor _, .cons _ (.cons _ .nil)
    | .shl _, .cons _ (.cons _ .nil) | .lshr _, .cons _ (.cons _ .nil)
    | .ashr _, .cons _ (.cons _ .nil) | .zext .., .cons _ .nil | .sext .., .cons _ .nil
    | .trunc .., .cons _ .nil | .toBits .., .cons _ .nil | .ofBits .., .cons _ .nil
    | .icmp .., .cons _ (.cons _ .nil)
    | .fcmp .., .cons _ (.cons _ .nil) | .select _, .cons _ (.cons _ (.cons _ .nil))
    | .ptradd .., .cons _ (.cons _ .nil) => rfl
    | .freeze w, .cons a .nil => by
      show (ChoiceTree.bind (freezeValue a) _).toSet = _
      rw [ChoiceTree.toSet_bind]
      exact congrArg (fun s => s >>= fun v => (pure (.cons v .nil) : SetM (HVector toType [i w])))
        (freezeValue_toSet (ε := Op) (w := w) a)
    | .fbin o e m, .cons a (.cons b .nil) => by
      show (ChoiceTree.bind (fbinValues o a b) _).toSet = _
      rw [ChoiceTree.toSet_bind]
      exact congrArg (fun s => s >>= fun v => (pure (.cons v .nil) : SetM (HVector toType [Ty.float e m])))
        (fbinValues_toSet (ε := Op) o a b)
    | .funary o e m, .cons a .nil => by
      show (ChoiceTree.bind (funaryValue o a) _).toSet = _
      rw [ChoiceTree.toSet_bind]
      exact congrArg (fun s => s >>= fun v => (pure (.cons v .nil) : SetM (HVector toType [Ty.float e m])))
        (funaryValue_toSet (ε := Op) o a)
    | .fma e m, .cons a (.cons b (.cons c .nil)) => by
      show (ChoiceTree.bind (fmaValues a b c) _).toSet = _
      rw [ChoiceTree.toSet_bind]
      exact congrArg (fun s => s >>= fun v => (pure (.cons v .nil) : SetM (HVector toType [Ty.float e m])))
        (fmaValues_toSet (ε := Op) a b c)
    | .sitofp _ e m, .cons a .nil => by
      show (ChoiceTree.bind (intToFloat e m true a) _).toSet = _
      rw [ChoiceTree.toSet_bind]
      exact congrArg (fun s => s >>= fun v => (pure (.cons v .nil) : SetM (HVector toType [Ty.float e m])))
        (intToFloat_toSet (ε := Op) e m true a)
    | .uitofp _ e m, .cons a .nil => by
      show (ChoiceTree.bind (intToFloat e m false a) _).toSet = _
      rw [ChoiceTree.toSet_bind]
      exact congrArg (fun s => s >>= fun v => (pure (.cons v .nil) : SetM (HVector toType [Ty.float e m])))
        (intToFloat_toSet (ε := Op) e m false a)
    | .fpext e m e' m', .cons a .nil | .fptrunc e m e' m', .cons a .nil => by
      show (ChoiceTree.bind (convertFloat e m e' m' a) _).toSet = _
      rw [ChoiceTree.toSet_bind]
      exact congrArg (fun s => s >>= fun v => (pure (.cons v .nil) : SetM (HVector toType [Ty.float e' m'])))
        (convertFloat_toSet (ε := Op) e m e' m' a)
    | .sdiv _ x, args => ruleOfEv_toSet (sdivWith x) args
    | .udiv _ x, args => ruleOfEv_toSet (udivWith x) args
    | .srem _, args => ruleOfEv_toSet sremValues args
    | .urem _, args => ruleOfEv_toSet uremValues args
    | .const .., _ | .fconst .., _ | .poison _, _ | .br, _ | .condBr, _ | .ret _, _
    | .unreachable, _ | .call .., _ => rfl
  exit
    | .condBr, .cons c .nil => exitOfEv_toSet (condBrExit c)
    | .unreachable, _ => exitOfEv_toSet (ε := Op) unreachableExit
    | .const .., _ | .add .., _ | .sub .., _ | .mul .., _ | .sdiv .., _ | .udiv .., _
    | .srem _, _ | .urem _, _ | .and _, _ | .or _, _ | .xor _, _ | .shl _, _ | .lshr _, _
    | .ashr _, _ | .icmp .., _ | .select _, _ | .zext .., _ | .sext .., _ | .trunc .., _
    | .freeze _, _ | .poison _, _ | .br, _ | .ret _, _ | .call .., _ | .fconst .., _
    | .fcmp .., _ | .fbin .., _ | .funary .., _ | .fma .., _ | .toBits .., _ | .ofBits .., _
    | .sitofp .., _ | .uitofp .., _ | .fpext .., _ | .fptrunc .., _
    | .ptradd .., _ => rfl

/-- The core dialect's rules in the state layer over the tree of choices:
each op runs by its rule in the tree and keeps the memories, as it runs with
memory by its rule in the set monad (the section on the core's effects). -/
instance {N : Type} {unit : N → Nat} :
    DialectDenote CoreDialect (StateT (Memories N unit) (ChoiceTree Op)) :=
  DialectDenote.liftState _

variable {N : Type} [DecidableEq N] (unit : N → Nat)

/-- The core's semantics in the layer over the tree of choices denotes its
semantics with memory, wherever a run names the core's memories. -/
theorem memMapsDenote (ρ : DialectEffects.Mem CoreDialect → N) :
    MemMapsDenote (d := CoreDialect) unit (ε := Op) ρ :=
  ChoiceTree.toSetMorphism.state_mapsDenote_liftState _ mapsDenote

/-- Exhaustive mode on the core function `f` of the module `M`: every path
of its run with memory on `args` with `fuel` steps, from the empty memories
whose units are `unit x` bits wide for the memory `x`, when no path chooses
more than `budget` bits in all. -/
def exhaustive (M : Module CoreDialect) (f : Func CoreDialect)
    (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat) :
    Option (List (ChoiceTree.Leaf Op (Except Stuck (Result Obs)) × Nat)) :=
  (f.memTree unit M args fuel).explore budget

/-- Scripted mode on the core function `f` of the module `M`: the path of
its run with memory on `args` with `fuel` steps, from the empty memories,
that the choice sequence `cs` names, each value read by `read`, or why `cs`
does not fit the run. -/
def scripted {σ : Type} (read : (w : Nat) → σ → Option (BitVec w)) (M : Module CoreDialect)
    (f : Func CoreDialect)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (cs : List σ) :
    Except (ChoiceTree.Misfit σ) (ChoiceTree.Leaf Op (Except Stuck (Result Obs)) × Nat) :=
  (f.memTree unit M args fuel).script read cs 0

/-- Sampled mode on the core function `f` of the module `M`: the path of
its run with memory on `args` with `fuel` steps, from the empty memories, on
which `draw` gives each choice, from the generator `g`, and the values
chosen on it. -/
def sampled {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ) (M : Module CoreDialect)
    (f : Func CoreDialect)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (g : γ) :
    ChoiceTree.Leaf Op (Except Stuck (Result Obs)) × List ChoiceTree.Chosen :=
  (f.memTree unit M args fuel).sample draw g

/-! # Outcomes of the runs with memory -/

variable (ρ : DialectEffects.Mem CoreDialect → N)

/-- Exhaustive mode, within its choice budget, gives exactly the outcomes
of the run with memory at the fuel budget it runs with, wherever a run
names the core's memories. -/
theorem exhaustive_memOutcomes (M : Module CoreDialect) (f : Func CoreDialect)
    (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat)
    {ls : List (ChoiceTree.Leaf Op (Except Stuck (Result Obs)) × Nat)}
    (hx : exhaustive unit M f args fuel budget = some ls) (o : Outcome Obs) :
    Run.outcomes (f.memRuns unit ρ M args fuel) o ↔ ∃ p ∈ ls, p.1.pathEnd = .outcome o :=
  Func.memExplore_outcomes unit ρ (memMapsDenote unit ρ) M f args fuel budget hx o

/-- Exhaustive mode, within its choice budget, lists a stuck path exactly
when the run with memory has one. -/
theorem exhaustive_memStuck (M : Module CoreDialect) (f : Func CoreDialect)
    (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat)
    {ls : List (ChoiceTree.Leaf Op (Except Stuck (Result Obs)) × Nat)}
    (hx : exhaustive unit M f args fuel budget = some ls) :
    Run.IsStuck (f.memRuns unit ρ M args fuel) ↔ ∃ p ∈ ls, ∃ st, p.1.pathEnd = .stuck st :=
  Func.memExplore_stuck unit ρ (memMapsDenote unit ρ) M f args fuel budget hx

/-- Scripted mode, on a choice sequence that fits, gives an outcome of the
run with memory at the fuel budget it runs with. -/
theorem scripted_memOutcomes {σ : Type} (read : (w : Nat) → σ → Option (BitVec w))
    (M : Module CoreDialect) (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2)))
    (fuel : Nat) (cs : List σ) {l : ChoiceTree.Leaf Op (Except Stuck (Result Obs))} {c : Nat}
    (hs : scripted unit read M f args fuel cs = .ok (l, c)) {o : Outcome Obs}
    (ho : l.pathEnd = .outcome o) : Run.outcomes (f.memRuns unit ρ M args fuel) o :=
  Func.memScript_outcomes unit ρ (memMapsDenote unit ρ) read M f args fuel cs hs ho

/-- Scripted mode, on a choice sequence that fits, reports a stuck path
only when the run with memory has one. -/
theorem scripted_memStuck {σ : Type} (read : (w : Nat) → σ → Option (BitVec w))
    (M : Module CoreDialect) (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2)))
    (fuel : Nat) (cs : List σ) {l : ChoiceTree.Leaf Op (Except Stuck (Result Obs))} {c : Nat}
    (hs : scripted unit read M f args fuel cs = .ok (l, c)) {st : Stuck}
    (hst : l.pathEnd = .stuck st) : Run.IsStuck (f.memRuns unit ρ M args fuel) :=
  Func.memScript_stuck unit ρ (memMapsDenote unit ρ) read M f args fuel cs hs hst

/-- The values that sampled mode chose are a choice sequence that fits the
run: scripted mode on them reports the same path, with as many choices. -/
theorem sampled_fits {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ) (M : Module CoreDialect)
    (f : Func CoreDialect)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (g : γ) :
    scripted unit ChoiceTree.readChosen M f args fuel (sampled unit draw M f args fuel g).2 =
      .ok ((sampled unit draw M f args fuel g).1,
        (sampled unit draw M f args fuel g).2.length) := by
  have h := ChoiceTree.sample_script (draw := draw) (f.memTree unit (ε := Op) M args fuel) g 0
  rw [Nat.zero_add] at h
  exact h

/-- Sampled mode gives an outcome of the run with memory at the fuel budget
it runs with, whatever the generator. -/
theorem sampled_memOutcomes {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ)
    (M : Module CoreDialect) (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2)))
    (fuel : Nat) (g : γ) {o : Outcome Obs}
    (ho : (sampled unit draw M f args fuel g).1.pathEnd = .outcome o) :
    Run.outcomes (f.memRuns unit ρ M args fuel) o :=
  scripted_memOutcomes unit ρ _ M f args fuel _ (sampled_fits unit draw M f args fuel g) ho

/-- Sampled mode reports a stuck path only when the run with memory has
one. -/
theorem sampled_memStuck {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ)
    (M : Module CoreDialect) (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2)))
    (fuel : Nat) (g : γ) {st : Stuck}
    (hst : (sampled unit draw M f args fuel g).1.pathEnd = .stuck st) :
    Run.IsStuck (f.memRuns unit ρ M args fuel) :=
  scripted_memStuck unit ρ _ M f args fuel _ (sampled_fits unit draw M f args fuel g) hst

/-! # Outcomes of the runs

The core's ops touch no memory, so the tree of a core run with memory is the
tree of its run with no memory: the modes report what they reported before
memory, path for path, and each mode's theorems speak of the run in the set
monad too. -/

/-- The tree of a core run with memory is the tree of its run: each core op
keeps the memories, so the paths, their choices and how each ends are the
same, and only the memories that the tree drops at each leaf differ. -/
theorem memTree_eq (M : Module CoreDialect) (f : Func CoreDialect)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) :
    f.memTree unit (ε := Op) M args fuel = (f.run M (m := ChoiceTree Op) args fuel).run := by
  have h := Func.run_map (DialectDenote.liftState_mapsDenote (m := ChoiceTree Op)
    (d := CoreDialect) (Memories N unit))
    (MonadMorphism.liftState_mapsFrame (Mem := N) (unit := unit) (fun _ => rfl)) M f args fuel
  unfold Func.memTree
  rw [← h]
  show (ChoiceTree.bind _ fun a => .pure (a, Memories.empty)).bind (fun p => .pure p.1) = _
  rw [ChoiceTree.bind_assoc]
  exact ChoiceTree.bind_pure _

/-- Exhaustive mode, within its choice budget, gives exactly the outcomes
of the run at the fuel budget it runs with. -/
theorem exhaustive_outcomes (M : Module CoreDialect) (f : Func CoreDialect)
    (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat)
    {ls : List (ChoiceTree.Leaf Op (Except Stuck (Result Obs)) × Nat)}
    (hx : exhaustive unit M f args fuel budget = some ls) (o : Outcome Obs) :
    Run.outcomes (f.run M (m := SetM) args fuel) o ↔ ∃ p ∈ ls, p.1.pathEnd = .outcome o := by
  rw [exhaustive, memTree_eq] at hx
  exact Func.explore_outcomes mapsDenote M f args fuel budget hx o

/-- Exhaustive mode, within its choice budget, lists a stuck path exactly
when the run has one. -/
theorem exhaustive_stuck (M : Module CoreDialect) (f : Func CoreDialect)
    (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat)
    {ls : List (ChoiceTree.Leaf Op (Except Stuck (Result Obs)) × Nat)}
    (hx : exhaustive unit M f args fuel budget = some ls) :
    Run.IsStuck (f.run M (m := SetM) args fuel) ↔ ∃ p ∈ ls, ∃ st, p.1.pathEnd = .stuck st := by
  rw [exhaustive, memTree_eq] at hx
  exact Func.explore_stuck mapsDenote M f args fuel budget hx

/-- Scripted mode, on a choice sequence that fits, gives an outcome of the
run at the fuel budget it runs with. -/
theorem scripted_outcomes {σ : Type} (read : (w : Nat) → σ → Option (BitVec w))
    (M : Module CoreDialect) (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2)))
    (fuel : Nat) (cs : List σ) {l : ChoiceTree.Leaf Op (Except Stuck (Result Obs))} {c : Nat}
    (hs : scripted unit read M f args fuel cs = .ok (l, c)) {o : Outcome Obs}
    (ho : l.pathEnd = .outcome o) : Run.outcomes (f.run M (m := SetM) args fuel) o := by
  rw [scripted, memTree_eq] at hs
  exact Func.script_outcomes mapsDenote read M f args fuel cs hs ho

/-- Scripted mode, on a choice sequence that fits, reports a stuck path
only when the run has one. -/
theorem scripted_stuck {σ : Type} (read : (w : Nat) → σ → Option (BitVec w))
    (M : Module CoreDialect) (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2)))
    (fuel : Nat) (cs : List σ) {l : ChoiceTree.Leaf Op (Except Stuck (Result Obs))} {c : Nat}
    (hs : scripted unit read M f args fuel cs = .ok (l, c)) {st : Stuck}
    (hst : l.pathEnd = .stuck st) : Run.IsStuck (f.run M (m := SetM) args fuel) := by
  rw [scripted, memTree_eq] at hs
  exact Func.script_stuck mapsDenote read M f args fuel cs hs hst

/-- Sampled mode gives an outcome of the run at the fuel budget it runs
with, whatever the generator. -/
theorem sampled_outcomes {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ)
    (M : Module CoreDialect) (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2)))
    (fuel : Nat) (g : γ) {o : Outcome Obs}
    (ho : (sampled unit draw M f args fuel g).1.pathEnd = .outcome o) :
    Run.outcomes (f.run M (m := SetM) args fuel) o :=
  scripted_outcomes unit _ M f args fuel _ (sampled_fits unit draw M f args fuel g) ho

/-- Sampled mode reports a stuck path only when the run has one. -/
theorem sampled_stuck {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ)
    (M : Module CoreDialect) (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2)))
    (fuel : Nat) (g : γ) {st : Stuck}
    (hst : (sampled unit draw M f args fuel g).1.pathEnd = .stuck st) :
    Run.IsStuck (f.run M (m := SetM) args fuel) :=
  scripted_stuck unit _ M f args fuel _ (sampled_fits unit draw M f args fuel g) hst

end Fir.Core
