import Fir.Core.MemRules
import Fir.Execution.MemoryPoison
import Fir.Execution.MemoryFinite
import Fir.Execution.MemoryFree

/-!
# Function address obligations

`funcAddr` reads where its function starts in the items that the run gives
each op, so it has no rule in the set monad and no tie to it: it meets each
obligation with memory by its own rule, wherever a run names the core's
memories, whatever their layout entries, and for every record of items,
one that gives no such function included. Its rule gives one result at once
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

None of this looks at the record or the function, so the proofs hold for
every record and every symbol, valid or not.
-/

namespace Fir.Core

open Memory

variable (s : String) (n : Nat)

section

variable {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : Mem → N) (L : RunItems)

/-- `funcAddr` runs with memory by its rule: its result, from where the
run starts its function, with the memories unchanged, a computation of the
set monad run in the state layer. -/
theorem funcAddr_denote (args : HVector toType (Fir.sig (d := CoreDialect) (Op.funcAddr s n))) :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ L
    @Eq (StateT (Memories N (unitsOf lay)) SetM (HVector toType [Ty.ptr n]))
      (DialectDenote.denote (d := CoreDialect) (m := StateT (Memories N (unitsOf lay)) SetM)
        (Op.funcAddr s n) args)
      (StateT.lift (pure (funcAddrResult (L.func? s)))) := by
  funext S
  exact (SetM.pure_bind (funcAddrResult (n := n) (L.func? s)) fun a => pure (a, S)).symm

/-- What `funcAddr` runs by its own rule has every property that each
computation of the set monad, run in the state layer, has. -/
theorem funcAddr_ownRuleHas {P : {α : Type} → StateT (Memories N (unitsOf lay)) SetM α → Prop}
    (hP : ∀ {α : Type} (c : SetM α), P (StateT.lift c)) :
    OwnRuleHas lay ρ L P (d := CoreDialect) (.funcAddr s n) := fun args =>
  ⟨fun _ => by rw [funcAddr_denote]; exact hP _, fun h => nomatch h⟩

/-- `funcAddr` writes no unit of any memory. -/
theorem funcAddr_writesNot (x : N) :
    OwnRuleHas lay ρ L (WritesNot x) (d := CoreDialect) (.funcAddr s n) :=
  funcAddr_ownRuleHas s n lay ρ L fun c => writesNot_lift x c

/-- `funcAddr` reads no memory. -/
theorem funcAddr_readsNot (x : N) :
    OwnRuleHas lay ρ L (ReadsNot x) (d := CoreDialect) (.funcAddr s n) :=
  funcAddr_ownRuleHas s n lay ρ L fun c => readsNot_lift x c

/-- `funcAddr` allocates in no memory. -/
theorem funcAddr_allocatesNot (x : N) :
    OwnRuleHas lay ρ L (AllocatesNot x) (d := CoreDialect) (.funcAddr s n) :=
  funcAddr_ownRuleHas s n lay ρ L fun c => allocatesNot_lift x c

/-- `funcAddr` ignores the memories. -/
theorem funcAddr_ignoresMemory :
    OwnRuleHas lay ρ L IgnoresMemory (d := CoreDialect) (.funcAddr s n) :=
  funcAddr_ownRuleHas s n lay ρ L fun c => IgnoresMemory.lift c

/-- `funcAddr` has one outcome from any memories. -/
theorem funcAddr_finitelyMany
    (args : HVector toType (Fir.sig (d := CoreDialect) (Op.funcAddr s n))) :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ L
    FinitelyMany (DialectDenote.denote (d := CoreDialect)
      (m := StateT (Memories N (unitsOf lay)) SetM) (Op.funcAddr s n) args) := by
  rw [funcAddr_denote]
  exact FinitelyMany.lift ⟨[funcAddrResult (L.func? s)], fun a h => by
    cases h
    exact List.mem_singleton_self _⟩

end

/-- The result of `funcAddr` is a pointer, never poison. -/
theorem funcAddrResult_defined (n : Nat) (g : Option AllocId) :
    ¬ (funcAddrResult (n := n) g).Any TyPoison.IsPoison := by
  rintro (h | h) <;> cases h

/-- `funcAddr` never ends in UB. -/
theorem funcAddr_neverUB : NeverUB (d := CoreDialect) (.funcAddr s n) := fun lay ρ L args =>
  ⟨fun _ => by rw [funcAddr_denote]; exact noUB_lift fun _ h => (by cases h),
    fun h => nomatch h⟩

/-- `funcAddr` gives a pointer, never poison. -/
theorem funcAddr_makesNoPoison : MakesNoPoison (d := CoreDialect) (.funcAddr s n) := by
  intro _ N _ lay ρ L args _ S rs S' h
  rw [funcAddr_denote] at h
  rcases (SetM.lift_apply _ S _).1 h with ⟨a, ha, he⟩ | ⟨_, -, he⟩
  · cases he
    cases ha
    exact funcAddrResult_defined n _
  · cases he

/-- `funcAddr` has an outcome from any memories. -/
theorem funcAddr_memTotal : MemTotal (d := CoreDialect) (.funcAddr s n) := fun lay ρ L args =>
  ⟨fun _ => (by rw [funcAddr_denote]; exact hasOutcome_lift ⟨_, rfl⟩), fun h => nomatch h⟩

/-- From memories that refine others, `funcAddr` gives the same pointer
and keeps the memories. -/
theorem funcAddr_memMonotone : MemMonotone (d := CoreDialect) (.funcAddr s n) :=
  fun lay ρ L args args' _ => by
    refine ⟨fun _ => ?_, fun h => nomatch h⟩
    rw [funcAddr_denote, funcAddr_denote]
    refine StateRefinedBy.lift fun e he => ?_
    cases he
    exact ⟨_, rfl, rfl, trivial⟩

/-- `funcAddr` has no operand, so none is poison, and it is never UB, so
it propagates poison with memory. -/
theorem funcAddr_memPropagates : MemPropagatesPoison (d := CoreDialect) (.funcAddr s n) where
  poisonOut lay ρ L args hany := by
    match args, hany with
    | .nil, h => exact h.elim
  ubByOwnRules lay ρ L args S r _ h := by
    rw [funcAddr_denote] at h
    rcases (SetM.lift_apply _ S _).1 h with ⟨_, -, he⟩ | ⟨_, hr, -⟩
    · cases he
    · cases hr

/-- The operands of `funcAddr`: none. -/
def funcAddrNoArgs : HVector toType (Fir.sig (d := CoreDialect) (Op.funcAddr s n)) := .nil

/-- `funcAddr` gives a result on its empty operand vector, from memories
inside a call. -/
theorem funcAddr_memReturnsOnDefined :
    MemReturnsOnDefined (d := CoreDialect) (.funcAddr s n) := by
  intro _ _ lay ρ L
  refine ⟨funcAddrNoArgs s n, ?_, Memories.empty.enter, funcAddrResult (L.func? s),
    Memories.empty.enter,
    List.cons_ne_nil _ _, ?_⟩
  · exact fun h => h.elim
  · rw [funcAddr_denote]
    exact (SetM.lift_apply _ _ _).2 (.inl ⟨_, rfl, rfl⟩)

end Fir.Core
