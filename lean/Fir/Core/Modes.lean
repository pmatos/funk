import Fir.Core.Semantics
import Fir.Execution.Modes

/-!
# The core dialect's exhaustive and scripted runs

`fir-ref run` runs the core dialect's rules in the tree of choices. Each op
runs its rule, `Core.Op.denote?` or `Core.Op.exit?`, the same rule that the
set monad's instance runs; an op without rules ends its path with no
outcome, for that op, as the set monad gives it none (ADR-2026-10-30-1855).
`fir-ref` reports such a path as an error.

The tree's semantics of each op denotes the set monad's, `mapsDenote`: the
rules are written once for any monad, and `toSet` keeps `pure`, `bind` and
the choice effect. So the soundness theorems of exhaustive and scripted
runs hold for every core function, on every argument vector, at every fuel
budget: `exhaustive_outcomes` and `scripted_outcomes`. `fir-ref` computes
`exhaustive`, `scripted` and `sampled` below, and nothing else, to report a
run. Sampled mode's values fit the run (`sampled_fits`), so it inherits
scripted mode's theorem: `sampled_outcomes`.
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

/-- The tree's semantics of each core op denotes the set monad's. -/
theorem mapsDenote : (ChoiceTree.toSetMorphism (ε := Op)).MapsDenote (d := CoreDialect) where
  denote
    | .add _ _, .cons _ (.cons _ .nil) | .sub _ _, .cons _ (.cons _ .nil)
    | .mul _ _, .cons _ (.cons _ .nil) | .and _, .cons _ (.cons _ .nil)
    | .or _, .cons _ (.cons _ .nil) | .xor _, .cons _ (.cons _ .nil)
    | .shl _, .cons _ (.cons _ .nil) | .lshr _, .cons _ (.cons _ .nil)
    | .ashr _, .cons _ (.cons _ .nil) => rfl
    | .freeze w, .cons a .nil => by
      show (ChoiceTree.bind (freezeValue a) _).toSet = _
      rw [ChoiceTree.toSet_bind]
      exact congrArg (fun s => s >>= fun v => (pure (.cons v .nil) : SetM (HVector toType [i w])))
        (freezeValue_toSet (ε := Op) (w := w) a)
    | .const .., _ | .sdiv .., _ | .udiv .., _ | .srem _, _ | .urem _, _ | .icmp .., _
    | .select _, _ | .zext .., _ | .sext .., _ | .trunc .., _ | .br, _ | .condBr, _
    | .ret _, _ | .call .., _ => rfl
  exit op _ := by cases op <;> rfl

/-- Exhaustive mode on the core function `f`: every path of its run on
`args` with `fuel` steps, when no path chooses more than `budget` bits in
all. -/
def exhaustive (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2)))
    (fuel budget : Nat) : Option (List (ChoiceTree.Leaf Op (Except Stuck (Result Obs)) × Nat)) :=
  (f.run (m := ChoiceTree Op) args fuel).run.explore budget

/-- Scripted mode on the core function `f`: the path of its run on `args`
with `fuel` steps that the choice sequence `cs` names, each value read by
`read`, or why `cs` does not fit the run. -/
def scripted {σ : Type} (read : (w : Nat) → σ → Option (BitVec w)) (f : Func CoreDialect)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (cs : List σ) :
    Except (ChoiceTree.Misfit σ) (ChoiceTree.Leaf Op (Except Stuck (Result Obs)) × Nat) :=
  (f.run (m := ChoiceTree Op) args fuel).run.script read cs 0

/-- Exhaustive mode, within its choice budget, gives exactly the outcomes
of the run at the fuel budget it runs with. -/
theorem exhaustive_outcomes (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2)))
    (fuel budget : Nat) {ls : List (ChoiceTree.Leaf Op (Except Stuck (Result Obs)) × Nat)}
    (hx : exhaustive f args fuel budget = some ls) (o : Outcome Obs) :
    Run.outcomes (f.run (m := SetM) args fuel) o ↔ ∃ p ∈ ls, p.1.pathEnd = .outcome o :=
  Func.explore_outcomes mapsDenote f args fuel budget hx o

/-- Exhaustive mode, within its choice budget, lists a stuck path exactly
when the run has one. -/
theorem exhaustive_stuck (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2)))
    (fuel budget : Nat) {ls : List (ChoiceTree.Leaf Op (Except Stuck (Result Obs)) × Nat)}
    (hx : exhaustive f args fuel budget = some ls) :
    Run.IsStuck (f.run (m := SetM) args fuel) ↔ ∃ p ∈ ls, ∃ st, p.1.pathEnd = .stuck st :=
  Func.explore_stuck mapsDenote f args fuel budget hx

/-- Scripted mode, on a choice sequence that fits, gives an outcome of the
run at the fuel budget it runs with. -/
theorem scripted_outcomes {σ : Type} (read : (w : Nat) → σ → Option (BitVec w))
    (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2))) (fuel : Nat)
    (cs : List σ) {l : ChoiceTree.Leaf Op (Except Stuck (Result Obs))} {c : Nat}
    (hs : scripted read f args fuel cs = .ok (l, c)) {o : Outcome Obs}
    (ho : l.pathEnd = .outcome o) : Run.outcomes (f.run (m := SetM) args fuel) o :=
  Func.script_outcomes mapsDenote read f args fuel cs hs ho

/-- Scripted mode, on a choice sequence that fits, reports a stuck path
only when the run has one. -/
theorem scripted_stuck {σ : Type} (read : (w : Nat) → σ → Option (BitVec w))
    (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2))) (fuel : Nat)
    (cs : List σ) {l : ChoiceTree.Leaf Op (Except Stuck (Result Obs))} {c : Nat}
    (hs : scripted read f args fuel cs = .ok (l, c)) {st : Stuck}
    (hst : l.pathEnd = .stuck st) : Run.IsStuck (f.run (m := SetM) args fuel) :=
  Func.script_stuck mapsDenote read f args fuel cs hs hst

/-- Sampled mode on the core function `f`: the path of its run on `args`
with `fuel` steps on which `draw` gives each choice, from the generator
`g`, and the values chosen on it. -/
def sampled {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ) (f : Func CoreDialect)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (g : γ) :
    ChoiceTree.Leaf Op (Except Stuck (Result Obs)) × List ChoiceTree.Chosen :=
  (f.run (m := ChoiceTree Op) args fuel).run.sample draw g

/-- The values that sampled mode chose are a choice sequence that fits the
run: scripted mode on them reports the same path, with as many choices. -/
theorem sampled_fits {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ) (f : Func CoreDialect)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (g : γ) :
    scripted ChoiceTree.readChosen f args fuel (sampled draw f args fuel g).2 =
      .ok ((sampled draw f args fuel g).1, (sampled draw f args fuel g).2.length) := by
  have h := ChoiceTree.sample_script (draw := draw) (f.run (m := ChoiceTree Op) args fuel).run g 0
  rw [Nat.zero_add] at h
  exact h

/-- Sampled mode gives an outcome of the run at the fuel budget it runs
with, whatever the generator. -/
theorem sampled_outcomes {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ)
    (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (g : γ)
    {o : Outcome Obs} (ho : (sampled draw f args fuel g).1.pathEnd = .outcome o) :
    Run.outcomes (f.run (m := SetM) args fuel) o :=
  scripted_outcomes _ f args fuel _ (sampled_fits draw f args fuel g) ho

/-- Sampled mode reports a stuck path only when the run has one. -/
theorem sampled_stuck {γ : Type} (draw : (w : Nat) → γ → BitVec w × γ)
    (f : Func CoreDialect) (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (g : γ)
    {st : Stuck} (hst : (sampled draw f args fuel g).1.pathEnd = .stuck st) :
    Run.IsStuck (f.run (m := SetM) args fuel) :=
  scripted_stuck _ f args fuel _ (sampled_fits draw f args fuel g) hst

end Fir.Core
