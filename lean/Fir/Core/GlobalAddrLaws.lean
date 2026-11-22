import Fir.Core.MemRules
import Fir.Execution.MemoryPoison
import Fir.Execution.MemoryFinite
import Fir.Execution.MemoryFree

/-!
# Global address obligations

`globalAddr` reads where its global starts in the items that the run gives
each op, so it has no rule in the set monad and no tie to it: it meets each
obligation with memory by its own rule, wherever a run names the core's
memories, whatever their layout entries, and for every record of items,
one that gives no such global included. Its rule gives one result at once
and keeps the memories: it is a computation of the set monad, a result,
run in the state layer, at every record. So:

* _Effects._ It never ends in UB, and its result, a pointer, is never
  poison. It writes, reads and allocates in no memory: it is pure, as it
  declares.
* _Totality._ It has an outcome from any memories.
* _Monotonicity._ It takes no operands, so it gives the same pointer on
  every operand vector, and keeps memories that refine others.
* _Poison with memory._ It has no operand that could be poison, it is
  never UB, and it gives a result from memories inside a call.
* _Finitely many outcomes._ It has one, from any memories.
* _It ignores the memories._ It ends with the memories it started with,
  and the same result from any others.

None of this looks at the record or the global, so the proofs hold for
every record and every symbol, valid or not.
-/

namespace Fir.Core

open Memory

variable (s : String) (n : Nat)

section

variable {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : Mem → N) (L : RunItems)

/-- `globalAddr` runs with memory by its rule: its result, from where the
run starts its global, with the memories unchanged, a computation of the
set monad run in the state layer. -/
theorem globalAddr_denote (args : HVector toType (Fir.sig (d := CoreDialect) (Op.globalAddr s n))) :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ L
    @Eq (StateT (Memories N (unitsOf lay)) SetM (HVector toType [Ty.ptr n]))
      (DialectDenote.denote (d := CoreDialect) (m := StateT (Memories N (unitsOf lay)) SetM)
        (Op.globalAddr s n) args)
      (StateT.lift (pure (globalAddrResult (L.global? s)))) := by
  funext S
  exact (SetM.pure_bind (globalAddrResult (n := n) (L.global? s)) fun a => pure (a, S)).symm

/-- What `globalAddr` runs by its own rule has every property that each
computation of the set monad, run in the state layer, has. -/
theorem globalAddr_ownRuleHas {P : {α : Type} → StateT (Memories N (unitsOf lay)) SetM α → Prop}
    (hP : ∀ {α : Type} (c : SetM α), P (StateT.lift c)) :
    OwnRuleHas lay ρ L P (d := CoreDialect) (.globalAddr s n) := fun args =>
  ⟨fun _ => by rw [globalAddr_denote]; exact hP _, fun h => nomatch h⟩

/-- `globalAddr` writes no unit of any memory. -/
theorem globalAddr_writesNot (x : N) :
    OwnRuleHas lay ρ L (WritesNot x) (d := CoreDialect) (.globalAddr s n) :=
  globalAddr_ownRuleHas s n lay ρ L fun c => writesNot_lift x c

/-- `globalAddr` reads no memory. -/
theorem globalAddr_readsNot (x : N) :
    OwnRuleHas lay ρ L (ReadsNot x) (d := CoreDialect) (.globalAddr s n) :=
  globalAddr_ownRuleHas s n lay ρ L fun c => readsNot_lift x c

/-- `globalAddr` allocates in no memory. -/
theorem globalAddr_allocatesNot (x : N) :
    OwnRuleHas lay ρ L (AllocatesNot x) (d := CoreDialect) (.globalAddr s n) :=
  globalAddr_ownRuleHas s n lay ρ L fun c => allocatesNot_lift x c

/-- `globalAddr` ignores the memories. -/
theorem globalAddr_ignoresMemory :
    OwnRuleHas lay ρ L IgnoresMemory (d := CoreDialect) (.globalAddr s n) :=
  globalAddr_ownRuleHas s n lay ρ L fun c => IgnoresMemory.lift c

/-- `globalAddr` has one outcome from any memories. -/
theorem globalAddr_finitelyMany
    (args : HVector toType (Fir.sig (d := CoreDialect) (Op.globalAddr s n))) :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ L
    FinitelyMany (DialectDenote.denote (d := CoreDialect)
      (m := StateT (Memories N (unitsOf lay)) SetM) (Op.globalAddr s n) args) := by
  rw [globalAddr_denote]
  exact FinitelyMany.lift ⟨[globalAddrResult (L.global? s)], fun a h => by
    cases h
    exact List.mem_singleton_self _⟩

end

/-- The result of `globalAddr` is a pointer, never poison. -/
theorem globalAddrResult_defined (n : Nat) (g : Option (Nat × AllocId)) :
    ¬ (globalAddrResult (n := n) g).Any TyPoison.IsPoison := by
  rintro (h | h) <;> cases h

/-- `globalAddr` never ends in UB. -/
theorem globalAddr_neverUB : NeverUB (d := CoreDialect) (.globalAddr s n) := fun lay ρ L args =>
  ⟨fun _ => by rw [globalAddr_denote]; exact noUB_lift fun _ h => (by cases h),
    fun h => nomatch h⟩

/-- `globalAddr` gives a pointer, never poison. -/
theorem globalAddr_makesNoPoison : MakesNoPoison (d := CoreDialect) (.globalAddr s n) := by
  intro _ N _ lay ρ L args _ S rs S' h
  rw [globalAddr_denote] at h
  rcases (SetM.lift_apply _ S _).1 h with ⟨a, ha, he⟩ | ⟨_, -, he⟩
  · cases he
    cases ha
    exact globalAddrResult_defined n _
  · cases he

/-- `globalAddr` has an outcome from any memories. -/
theorem globalAddr_memTotal : MemTotal (d := CoreDialect) (.globalAddr s n) := fun lay ρ L args =>
  ⟨fun _ => (by rw [globalAddr_denote]; exact hasOutcome_lift ⟨_, rfl⟩), fun h => nomatch h⟩

/-- From memories that refine others, `globalAddr` gives the same pointer
and keeps the memories. -/
theorem globalAddr_memMonotone : MemMonotone (d := CoreDialect) (.globalAddr s n) :=
  fun lay ρ L args args' _ => by
    refine ⟨fun _ => ?_, fun h => nomatch h⟩
    rw [globalAddr_denote, globalAddr_denote]
    refine StateRefinedBy.lift fun e he => ?_
    cases he
    exact ⟨_, rfl, rfl, trivial⟩

/-- `globalAddr` has no operand, so none is poison, and it is never UB, so
it propagates poison with memory. -/
theorem globalAddr_memPropagates : MemPropagatesPoison (d := CoreDialect) (.globalAddr s n) where
  poisonOut lay ρ L args hany := by
    match args, hany with
    | .nil, h => exact h.elim
  ubByOwnRules lay ρ L args S r _ h := by
    rw [globalAddr_denote] at h
    rcases (SetM.lift_apply _ S _).1 h with ⟨_, -, he⟩ | ⟨_, hr, -⟩
    · cases he
    · cases hr

/-- The operands of `globalAddr`: none. -/
def globalAddrNoArgs : HVector toType (Fir.sig (d := CoreDialect) (Op.globalAddr s n)) := .nil

/-- `globalAddr` gives a result on its empty operand vector, from memories
inside a call. -/
theorem globalAddr_memReturnsOnDefined :
    MemReturnsOnDefined (d := CoreDialect) (.globalAddr s n) := by
  intro _ _ lay ρ L
  refine ⟨globalAddrNoArgs s n, ?_, Memories.empty.enter, globalAddrResult (L.global? s),
    Memories.empty.enter,
    List.cons_ne_nil _ _, ?_⟩
  · exact fun h => h.elim
  · rw [globalAddr_denote]
    exact (SetM.lift_apply _ _ _).2 (.inl ⟨_, rfl, rfl⟩)

end Fir.Core
