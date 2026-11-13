import Fir.Core.EffectLaws
import Fir.Execution.MemoryModes

/-!
# The core dialect in the tree of choices

`fir-ref run` runs the core dialect's rules in the tree of choices. Each op
runs its rule, the same rule that the set monad's semantics runs; an op without
rules ends its path with no outcome, for that op, as the set monad gives it
none (`docs/decisions/fir-ref.md#an-op-without-rules`). `fir-ref` reports such
a path as an error.

Each op's semantics in the tree has the set monad's as its set: the rules
are written once for any monad, and the set of a tree keeps the steps of
a computation, the choice effect and UB.

With memory, the core runs in the state layer over the tree of choices,
where the run's memories have their layout entries and the run names the
core's memories. No core op touches memory, so each op runs by its rule in
the tree and keeps the memories, as it does in the core's semantics with
memory, and the morphism through the layer maps the one to the other at
every layout and naming of the core's memories. The modes of the next
section walk the run in that layer.
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
    | .fptosi .., .cons _ .nil | .fptoui .., .cons _ .nil
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
    | .ptradd .., _ | .fptosi .., _ | .fptoui .., _ => rfl

/-- The core dialect's semantics in the state layer over the tree of
choices, where a run's memories have the layout entries `lay` and the run
names the core's memory `x` as `ρ x`: each op runs by its rule in the tree
and keeps the memories, as it runs with memory by its rule in the set monad
(the section on the core's effects). -/
@[instance_reducible] def memTreeDenote {N : Type} (lay : N → MemLayout) (_ : Mem → N) :
    DialectDenote CoreDialect (StateT (Memories N (unitsOf lay)) (ChoiceTree Op)) :=
  DialectDenote.liftState _

variable {N : Type} [DecidableEq N] (lay : N → MemLayout)

/-- The core's semantics in the layer over the tree of choices denotes its
semantics with memory, wherever a run names the core's memories, whatever
their entries. -/
theorem memMapsDenote (ρ : DialectEffects.Mem CoreDialect → N) :
    letI := memTreeDenote lay ρ
    MemMapsDenote (d := CoreDialect) lay (ε := Op) ρ :=
  ChoiceTree.toSetMorphism.state_mapsDenote_liftState _ mapsDenote

end Fir.Core
