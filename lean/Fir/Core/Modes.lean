import Fir.Core.Semantics
import Fir.Execution.Modes

/-!
# The core dialect's exhaustive, scripted and sampled runs

`fir-ref run` runs the core dialect's rules in the tree of choices. Each op
runs its rule, the same rule that the set monad's semantics runs; an op
without rules ends its path with no outcome, for that op, as the set monad
gives it none (ADR-2026-10-30-1855). `fir-ref` reports such a path as an
error.

Each op's semantics in the tree has the set monad's as its set: the rules
are written once for any monad, and the set of a tree keeps the steps of
a computation, the choice effect and UB. So the theorems of exhaustive and
scripted modes hold for every core function, on every argument vector, at
every fuel budget. `fir-ref` computes the exhaustive, scripted and sampled
modes defined below, and nothing else, to report a run. The values that
sampled mode chose fit the run, so it inherits scripted mode's theorems.

The theorems hold on every argument vector of the function's parameter
types, poison included, and `fir-ref run` takes `poison` as an argument of
any `iN`. A run on a poison argument is refined by the run with any value
in its place, calls and recursion included, as the section on refinement
through core calls proves. So the differential test harness, which
checks compiled code against `fir-ref`, runs native code, which holds no
poison, on poison stand-ins in place of each poison argument, and judges
each result against the outcomes that `fir-ref` lists for the run on the
poison (ADR-2026-11-03-1847).
-/

namespace Fir.Core

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
    | .trunc .., .cons _ .nil | .icmp .., .cons _ (.cons _ .nil)
    | .select _, .cons _ (.cons _ (.cons _ .nil)) => rfl
    | .freeze w, .cons a .nil => by
      show (ChoiceTree.bind (freezeValue a) _).toSet = _
      rw [ChoiceTree.toSet_bind]
      exact congrArg (fun s => s >>= fun v => (pure (.cons v .nil) : SetM (HVector toType [i w])))
        (freezeValue_toSet (ε := Op) (w := w) a)
    | .sdiv _ x, args => ruleOfEv_toSet (sdivWith x) args
    | .udiv _ x, args => ruleOfEv_toSet (udivWith x) args
    | .srem _, args => ruleOfEv_toSet sremValues args
    | .urem _, args => ruleOfEv_toSet uremValues args
    | .const .., _ | .poison _, _ | .br, _ | .condBr, _ | .ret _, _ | .unreachable, _
    | .call .., _ => rfl
  exit
    | .condBr, .cons c .nil => exitOfEv_toSet (condBrExit c)
    | .unreachable, _ => exitOfEv_toSet (ε := Op) unreachableExit
    | .const .., _ | .add .., _ | .sub .., _ | .mul .., _ | .sdiv .., _ | .udiv .., _
    | .srem _, _ | .urem _, _ | .and _, _ | .or _, _ | .xor _, _ | .shl _, _ | .lshr _, _
    | .ashr _, _ | .icmp .., _ | .select _, _ | .zext .., _ | .sext .., _ | .trunc .., _
    | .freeze _, _ | .poison _, _ | .br, _ | .ret _, _ | .call .., _ => rfl

/-- Exhaustive mode on the core function `f` of the module `M`: every path
of its run on `args` with `fuel` steps, when no path chooses more than
`budget` bits in all. -/
def exhaustive (M : Module CoreDialect) (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2)))
    (fuel budget : Nat) : Option (List (ChoiceTree.Leaf Op (Except Stuck (Result Obs)) × Nat)) :=
  (f.run M (m := ChoiceTree Op) args fuel).run.explore budget

/-- Scripted mode on the core function `f` of the module `M`: the path of
its run on `args` with `fuel` steps that the choice sequence `cs` names,
each value read by `read`, or why `cs` does not fit the run. -/
def scripted {σ : Type} (read : (w : Nat) → σ → Option (BitVec w)) (M : Module CoreDialect)
    (f : Func CoreDialect)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (cs : List σ) :
    Except (ChoiceTree.Misfit σ) (ChoiceTree.Leaf Op (Except Stuck (Result Obs)) × Nat) :=
  (f.run M (m := ChoiceTree Op) args fuel).run.script read cs 0

/-- Exhaustive mode, within its choice budget, gives exactly the outcomes
of the run at the fuel budget it runs with. -/
theorem exhaustive_outcomes (M : Module CoreDialect) (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2)))
    (fuel budget : Nat) {ls : List (ChoiceTree.Leaf Op (Except Stuck (Result Obs)) × Nat)}
    (hx : exhaustive M f args fuel budget = some ls) (o : Outcome Obs) :
    Run.outcomes (f.run M (m := SetM) args fuel) o ↔ ∃ p ∈ ls, p.1.pathEnd = .outcome o :=
  Func.explore_outcomes mapsDenote M f args fuel budget hx o

/-- Exhaustive mode, within its choice budget, lists a stuck path exactly
when the run has one. -/
theorem exhaustive_stuck (M : Module CoreDialect) (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2)))
    (fuel budget : Nat) {ls : List (ChoiceTree.Leaf Op (Except Stuck (Result Obs)) × Nat)}
    (hx : exhaustive M f args fuel budget = some ls) :
    Run.IsStuck (f.run M (m := SetM) args fuel) ↔ ∃ p ∈ ls, ∃ st, p.1.pathEnd = .stuck st :=
  Func.explore_stuck mapsDenote M f args fuel budget hx

/-- Scripted mode, on a choice sequence that fits, gives an outcome of the
run at the fuel budget it runs with. -/
theorem scripted_outcomes {σ : Type} (read : (w : Nat) → σ → Option (BitVec w))
    (M : Module CoreDialect) (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2))) (fuel : Nat)
    (cs : List σ) {l : ChoiceTree.Leaf Op (Except Stuck (Result Obs))} {c : Nat}
    (hs : scripted read M f args fuel cs = .ok (l, c)) {o : Outcome Obs}
    (ho : l.pathEnd = .outcome o) : Run.outcomes (f.run M (m := SetM) args fuel) o :=
  Func.script_outcomes mapsDenote read M f args fuel cs hs ho

/-- Scripted mode, on a choice sequence that fits, reports a stuck path
only when the run has one. -/
theorem scripted_stuck {σ : Type} (read : (w : Nat) → σ → Option (BitVec w))
    (M : Module CoreDialect) (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2))) (fuel : Nat)
    (cs : List σ) {l : ChoiceTree.Leaf Op (Except Stuck (Result Obs))} {c : Nat}
    (hs : scripted read M f args fuel cs = .ok (l, c)) {st : Stuck}
    (hst : l.pathEnd = .stuck st) : Run.IsStuck (f.run M (m := SetM) args fuel) :=
  Func.script_stuck mapsDenote read M f args fuel cs hs hst

/-- Sampled mode on the core function `f` of the module `M`: the path of
its run on `args` with `fuel` steps on which `draw` gives each choice, from
the generator `g`, and the values chosen on it. -/
def sampled {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ) (M : Module CoreDialect)
    (f : Func CoreDialect)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (g : γ) :
    ChoiceTree.Leaf Op (Except Stuck (Result Obs)) × List ChoiceTree.Chosen :=
  (f.run M (m := ChoiceTree Op) args fuel).run.sample draw g

/-- The values that sampled mode chose are a choice sequence that fits the
run: scripted mode on them reports the same path, with as many choices. -/
theorem sampled_fits {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ) (M : Module CoreDialect)
    (f : Func CoreDialect)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (g : γ) :
    scripted ChoiceTree.readChosen M f args fuel (sampled draw M f args fuel g).2 =
      .ok ((sampled draw M f args fuel g).1, (sampled draw M f args fuel g).2.length) := by
  have h := ChoiceTree.sample_script (draw := draw) (f.run M (m := ChoiceTree Op) args fuel).run g 0
  rw [Nat.zero_add] at h
  exact h

/-- Sampled mode gives an outcome of the run at the fuel budget it runs
with, whatever the generator. -/
theorem sampled_outcomes {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ)
    (M : Module CoreDialect) (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (g : γ)
    {o : Outcome Obs} (ho : (sampled draw M f args fuel g).1.pathEnd = .outcome o) :
    Run.outcomes (f.run M (m := SetM) args fuel) o :=
  scripted_outcomes _ M f args fuel _ (sampled_fits draw M f args fuel g) ho

/-- Sampled mode reports a stuck path only when the run has one. -/
theorem sampled_stuck {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ)
    (M : Module CoreDialect) (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (g : γ)
    {st : Stuck} (hst : (sampled draw M f args fuel g).1.pathEnd = .stuck st) :
    Run.IsStuck (f.run M (m := SetM) args fuel) :=
  scripted_stuck _ M f args fuel _ (sampled_fits draw M f args fuel g) hst

end Fir.Core
