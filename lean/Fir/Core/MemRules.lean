import Fir.Core.FloatArithLaws
import Fir.Core.FloatOfIntLaws
import Fir.Core.FloatConvertLaws
import Fir.Core.Lawful
import Fir.Execution.MemoryRuns

/-!
# The core's rules with memory

The core's rules are written once, for any monad with the effects they ask
for (the section on the core dialect's semantics). A monad morphism that
keeps choice and UB maps each rule in one monad to the same rule in the
other: `freeze`'s choice to a choice, a division's UB to UB, a result to
the same result. So the core's semantics in one monad maps to its
semantics in the other, op by op, wherever the two give an op with no rule
the same image.

With memory, the core's rules are written for a monad that also has the
memory effect, over the memories of a run, whose layout entries are `lay`,
where the run names the core's memory `x` as `ρ x`. An op that touches
memory reads the entry `lay (ρ x)` of the memory it accesses
(ADR-2026-11-13-0906). No core op touches memory yet, so each op's rule
with memory is its rule. The core's semantics with memory runs those rules
in the state layer over the set monad, op by op; an op with no rule, as
`call`, has no outcome there, as in the set monad.

Lifting a computation of the set monad into the state layer keeps choice
and UB, so it maps each core op's rule in the set monad to its rule with
memory. So each core op is tied: it runs with memory by its rule in the set
monad and keeps the memories. Each obligation with memory of an op follows
from that op's own tie and its obligation in the set monad, and the core
dialect lifts the set monad, as a theorem (`Core.liftsSetM`, in the section
on core functions with memory). An op that touches memory will have no tie,
and will meet each obligation with memory by its own proof.
-/

namespace Fir.Core

/-! # The rules in another monad -/

section

variable {m n : Type → Type} [Monad m] [Monad n] (φ : MonadMorphism m n)

/-- A morphism maps a computation that ends with a function of the result
of another as it maps the other. -/
theorem map_bind_pure {α β : Type} {x : m α} {y : n α} (h : φ.map x = y) (g : α → β) :
    φ.map (x >>= fun a => pure (g a)) = y >>= fun a => pure (g a) := by
  rw [φ.map_bind, h]
  simp only [φ.map_pure]

variable [MonadChoice m] [MonadChoice n] [MonadUB m] [MonadUB n] (hk : φ.KeepsChoiceUB)
include hk

/-- A morphism that keeps choice and UB maps `freeze`'s rule in `m` to its
rule in `n`. -/
theorem freezeValue_map {w : Nat} (a : PoisonOr (BitVec w)) :
    φ.map (freezeValue (m := m) a) = freezeValue a := by
  cases a with
  | value _ => exact φ.map_pure _
  | poison => exact map_bind_pure φ (hk.choose w) _

/-- Such a morphism maps a rule made by `ruleOfEv`, such as a division's, in
`m` to the same rule in `n`. -/
theorem ruleOfEv_map {w : Nat}
    (g : PoisonOr (BitVec w) → PoisonOr (BitVec w) → Ev (PoisonOr (BitVec w)))
    (args : HVector toType [i w, i w]) : φ.map (ruleOfEv (m := m) g args) = ruleOfEv g args := by
  match args with
  | .cons a (.cons b .nil) =>
    simp only [ruleOfEv]
    cases g a b
    · exact φ.map_pure _
    · exact hk.ub _

/-- Such a morphism maps a terminator's rule made by `exitOfEv`, such as
`cond_br`'s, in `m` to the same rule in `n`. -/
theorem exitOfEv_map (e : Ev Exit) : φ.map (exitOfEv (m := m) e) = exitOfEv e := by
  cases e
  · exact φ.map_pure _
  · exact hk.ub _

/-- A morphism that keeps choice and UB maps the core's semantics in `m` to
its semantics in `n`, op by op, when it maps what an op with no rule does
in `m` to what it does in `n`. -/
theorem denoteIn_mapsDenote (zm : {α : Type} → Op → m α) (zn : {α : Type} → Op → n α)
    (hz : ∀ {α : Type} (op : Op), φ.map (zm op : m α) = zn op) :
    letI := denoteIn @zm
    letI := denoteIn @zn
    φ.MapsDenote (d := CoreDialect) :=
  letI := denoteIn @zm
  letI := denoteIn @zn
  { denote := fun
      | .add _ _, .cons _ (.cons _ .nil) | .sub _ _, .cons _ (.cons _ .nil)
      | .mul _ _, .cons _ (.cons _ .nil) | .and _, .cons _ (.cons _ .nil)
      | .or _, .cons _ (.cons _ .nil) | .xor _, .cons _ (.cons _ .nil)
      | .shl _, .cons _ (.cons _ .nil) | .lshr _, .cons _ (.cons _ .nil)
      | .ashr _, .cons _ (.cons _ .nil) | .zext .., .cons _ .nil | .sext .., .cons _ .nil
      | .trunc .., .cons _ .nil | .toBits .., .cons _ .nil | .ofBits .., .cons _ .nil
      | .fptosi .., .cons _ .nil | .fptoui .., .cons _ .nil
      | .icmp .., .cons _ (.cons _ .nil)
      | .fcmp .., .cons _ (.cons _ .nil) | .select _, .cons _ (.cons _ (.cons _ .nil))
      | .ptradd .., .cons _ (.cons _ .nil) | .const .., _ | .fconst .., _ | .poison _, _ =>
        φ.map_pure _
      | .freeze _, .cons a .nil => map_bind_pure φ (freezeValue_map φ hk a) _
      | .fbin o _ _, .cons a (.cons b .nil) => map_bind_pure φ (fbinValues_map φ hk o a b) _
      | .funary o _ _, .cons a .nil => map_bind_pure φ (funaryValue_map φ hk o a) _
      | .fma _ _, .cons a (.cons b (.cons c .nil)) => map_bind_pure φ (fmaValues_map φ hk a b c) _
      | .sitofp _ e m, .cons a .nil => map_bind_pure φ (intToFloat_map φ hk e m true a) _
      | .uitofp _ e m, .cons a .nil => map_bind_pure φ (intToFloat_map φ hk e m false a) _
      | .fpext e m e' m', .cons a .nil | .fptrunc e m e' m', .cons a .nil =>
        map_bind_pure φ (convertFloat_map φ hk e m e' m' a) _
      | .sdiv _ x, args => ruleOfEv_map φ hk (sdivWith x) args
      | .udiv _ x, args => ruleOfEv_map φ hk (udivWith x) args
      | .srem _, args => ruleOfEv_map φ hk sremValues args
      | .urem _, args => ruleOfEv_map φ hk uremValues args
      | .br, _ | .condBr, _ | .ret _, _ | .unreachable, _ | .call .., _ => hz _
    exit := fun
      | .br, _ | .ret _, _ => φ.map_pure _
      | .condBr, .cons c .nil => exitOfEv_map φ hk (condBrExit c)
      | .unreachable, _ => exitOfEv_map φ hk unreachableExit
      | .const .., _ | .add .., _ | .sub .., _ | .mul .., _ | .sdiv .., _ | .udiv .., _
      | .srem _, _ | .urem _, _ | .and _, _ | .or _, _ | .xor _, _ | .shl _, _ | .lshr _, _
      | .ashr _, _ | .icmp .., _ | .select _, _ | .zext .., _ | .sext .., _ | .trunc .., _
      | .freeze _, _ | .poison _, _ | .call .., _ | .fconst .., _
      | .fcmp .., _ | .fbin .., _ | .funary .., _ | .fma .., _ | .toBits .., _ | .ofBits .., _
      | .sitofp .., _ | .uitofp .., _ | .fpext .., _ | .fptrunc .., _
      | .ptradd .., _ | .fptosi .., _ | .fptoui .., _ => hz _ }

end

/-! # The rules with memory -/

section

variable {N : Type} {m : Type → Type} [Monad m] [MonadChoice m] [MonadUB m]

/-- The rule of each core op that is not a terminator, with memory: in any
monad with choice, UB and the memory effect on the memories of a run whose
layout entries are `lay`, where the run names the core's memory `x` as
`ρ x`. No core op touches memory yet, so each op's rule is its rule in
`Op.denote?`. -/
def Op.memDenote? (lay : N → MemLayout) (_ : Mem → N) [MonadMemory N (unitsOf lay) m] (op : Op) :
    Option (HVector toType (Fir.sig (d := CoreDialect) op) →
      m (HVector toType (Fir.returnTypes (d := CoreDialect) op))) :=
  op.denote? (m := m)

/-- The rule of each core terminator, with memory: its rule in `Op.exit?`,
since no terminator touches memory. -/
def Op.memExit? (lay : N → MemLayout) (_ : Mem → N) [MonadMemory N (unitsOf lay) m] (op : Op) :
    Option (HVector toType (Fir.sig (d := CoreDialect) op) → m Exit) :=
  op.exit? (m := m)

/-- The core's semantics in a monad with memory, where a run's memories have
the entries `lay` and the run names the core's memories by `ρ`: each op's
rule with memory, and `z p` for an op `p` that has none. -/
@[reducible] def memDenoteIn (lay : N → MemLayout) (ρ : Mem → N) [MonadMemory N (unitsOf lay) m]
    (z : {α : Type} → Op → m α) : DialectDenote CoreDialect m :=
  denoteWith (fun op => op.memDenote? lay ρ) (fun op => op.memExit? lay ρ) z

/-- The core's semantics with memory: in the state layer over the set monad,
each op runs by its rule with memory, and an op with no rule has no
outcome, as in the set monad. -/
@[instance_reducible] def memDenoteAt [DecidableEq N] (lay : N → MemLayout) (ρ : Mem → N) :
    DialectDenote CoreDialect (StateT (Memory.Memories N (unitsOf lay)) SetM) :=
  memDenoteIn lay ρ fun _ _ _ => False

end

end Fir.Core

namespace Fir

/-- The core dialect's semantics with memory, at each layout and naming of
its memories. -/
instance Core.instDialectMemDenote : DialectMemDenote CoreDialect :=
  ⟨Core.memDenoteAt⟩

namespace Core

/-- No core op touches memory: each runs with memory by its rule in the set
monad and keeps the memories, at every layout and naming. Lifting into the
layer keeps choice and UB, and maps an op with no rule to one with no
outcome. -/
theorem Op.liftsSetM (op : Op) : OpLiftsSetM (d := CoreDialect) op := by
  intro N _ lay ρ args
  have h := denoteIn_mapsDenote (MonadMorphism.liftState SetM (Memory.Memories N (unitsOf lay)))
    (MonadMorphism.liftState_keeps _ fun r f => SetM.ub_bind r f) (fun _ _ => False)
    (fun _ _ _ => False) fun _ => by
      funext S e
      exact propext ⟨fun h => by rcases h with ⟨_, h, _⟩ | ⟨_, h, _⟩ <;> exact h, False.elim⟩
  obtain ⟨hd, he⟩ := h
  exact ⟨(hd op args).symm, (he op args).symm⟩

end Core

end Fir
