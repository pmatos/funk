import Fir.Core.MemRules
import Fir.Execution.MemoryPoison
import Fir.Execution.MemoryFinite
import Fir.Execution.MemoryFree

/-!
# Field address obligations

`fieldAddr` reads the layout it names in the items that the run gives each
op, so it has no rule in the set monad and no tie to it: it meets each
obligation with memory by its own rule, wherever a run names the core's
memories, whatever their layout entries, and for every record of items,
one that gives no such layout or field included. Its rule gives one result
at once and keeps the memories: it is a computation of the set monad, a
result, run in the state layer, at every record. So:

* _Effects._ It never ends in UB, and on a defined pointer and index its
  result, a pointer, is never poison. It writes, reads and allocates in no
  memory: it is pure, as it declares.
* _Totality._ It has an outcome from any memories.
* _Monotonicity._ On operands that refine others, it gives a pointer that
  refines the other's, and keeps memories that refine the others': a
  poison operand gives poison, which every pointer refines, and a pointer
  or an integer is refined only by itself.
* _Poison with memory._ A poison operand gives a poison pointer, it is
  never UB, and it gives a result on a defined pointer from memories inside
  a call.
* _Finitely many outcomes._ It has one, from any memories.
* _It ignores the memories._ It ends with the memories it started with,
  and the same result from any others.

None of this looks at the record, the layout or the field, so the proofs
hold for every record, every symbol and every field, valid or not.
-/

namespace Fir.Core

open Memory

variable (s : String) (j n : Nat) (w : Option Nat)

section

variable {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : Mem → N) (L : RunItems)

/-- `fieldAddr` runs with memory by its rule: its result, from the layout
that the run gives, with the memories unchanged, a computation of the set
monad run in the state layer. -/
theorem fieldAddr_denote (args : HVector toType (Fir.sig (d := CoreDialect) (Op.fieldAddr s j n w))) :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ L
    @Eq (StateT (Memories N (unitsOf lay)) SetM (HVector toType [Ty.ptr n]))
      (DialectDenote.denote (d := CoreDialect) (m := StateT (Memories N (unitsOf lay)) SetM)
        (Op.fieldAddr s j n w) args)
      (StateT.lift (pure (fieldAddrResult (L.layout? s) j w args))) := by
  funext S
  exact (SetM.pure_bind (fieldAddrResult (L.layout? s) j w args) fun a => pure (a, S)).symm

/-- What `fieldAddr` runs by its own rule has every property that each
computation of the set monad, run in the state layer, has. -/
theorem fieldAddr_ownRuleHas {P : {α : Type} → StateT (Memories N (unitsOf lay)) SetM α → Prop}
    (hP : ∀ {α : Type} (c : SetM α), P (StateT.lift c)) :
    OwnRuleHas lay ρ L P (d := CoreDialect) (.fieldAddr s j n w) := fun args =>
  ⟨fun _ => by rw [fieldAddr_denote]; exact hP _, fun h => nomatch h⟩

/-- `fieldAddr` writes no unit of any memory. -/
theorem fieldAddr_writesNot (x : N) :
    OwnRuleHas lay ρ L (WritesNot x) (d := CoreDialect) (.fieldAddr s j n w) :=
  fieldAddr_ownRuleHas s j n w lay ρ L fun c => writesNot_lift x c

/-- `fieldAddr` reads no memory. -/
theorem fieldAddr_readsNot (x : N) :
    OwnRuleHas lay ρ L (ReadsNot x) (d := CoreDialect) (.fieldAddr s j n w) :=
  fieldAddr_ownRuleHas s j n w lay ρ L fun c => readsNot_lift x c

/-- `fieldAddr` allocates in no memory. -/
theorem fieldAddr_allocatesNot (x : N) :
    OwnRuleHas lay ρ L (AllocatesNot x) (d := CoreDialect) (.fieldAddr s j n w) :=
  fieldAddr_ownRuleHas s j n w lay ρ L fun c => allocatesNot_lift x c

/-- `fieldAddr` ignores the memories. -/
theorem fieldAddr_ignoresMemory :
    OwnRuleHas lay ρ L IgnoresMemory (d := CoreDialect) (.fieldAddr s j n w) :=
  fieldAddr_ownRuleHas s j n w lay ρ L fun c => IgnoresMemory.lift c

/-- `fieldAddr` has one outcome from any memories. -/
theorem fieldAddr_finitelyMany
    (args : HVector toType (Fir.sig (d := CoreDialect) (Op.fieldAddr s j n w))) :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ L
    FinitelyMany (DialectDenote.denote (d := CoreDialect)
      (m := StateT (Memories N (unitsOf lay)) SetM) (Op.fieldAddr s j n w) args) := by
  rw [fieldAddr_denote]
  exact FinitelyMany.lift ⟨[fieldAddrResult (L.layout? s) j w args], fun a h => by
    cases h
    exact List.mem_singleton_self _⟩

end

/-- A poison operand gives a poison result. -/
theorem fieldAddrResult_poison {l : Option LayoutPlace}
    {args : HVector toType (Fir.sig (d := CoreDialect) (Op.fieldAddr s j n w))}
    (h : args.Any TyPoison.IsPoison) : (fieldAddrResult l j w args).All TyPoison.IsPoison := by
  cases w with
  | none =>
    match args, h with
    | .cons p .nil, .inl hp =>
      show fieldAddrValue l j p = .poison ∧ True
      cases hp
      exact ⟨rfl, trivial⟩
  | some _ =>
    match args, h with
    | .cons p (.cons k .nil), h =>
      refine ⟨?_, trivial⟩
      show elemAddrValue l j p k = .poison
      rcases h with hp | hk | hk
      · cases hp
        rfl
      · cases hk
        cases p <;> rfl
      · exact hk.elim

/-- On a pointer and an index, neither poison, the result is a pointer. -/
theorem fieldAddrResult_defined {l : Option LayoutPlace}
    {args : HVector toType (Fir.sig (d := CoreDialect) (Op.fieldAddr s j n w))}
    (h : ¬ args.Any TyPoison.IsPoison) : ¬ (fieldAddrResult l j w args).Any TyPoison.IsPoison := by
  cases w with
  | none =>
    match args, h with
    | .cons (.value _) .nil, _ => rintro (h | h) <;> cases h
    | .cons .poison .nil, h => exact absurd (.inl rfl) h
  | some _ =>
    match args, h with
    | .cons (.value _) (.cons (.value _) .nil), _ => rintro (h | h) <;> cases h
    | .cons .poison (.cons _ .nil), h => exact absurd (.inl rfl) h
    | .cons (.value _) (.cons .poison .nil), h => exact absurd (.inr (.inl rfl)) h

/-- On operands that refine others, the result refines the other's. -/
theorem fieldAddrResult_isRefinedBy {l : Option LayoutPlace}
    {args args' : HVector toType (Fir.sig (d := CoreDialect) (Op.fieldAddr s j n w))}
    (h : args.Forall₂ TyRefinement.IsRefinedBy args') :
    (fieldAddrResult l j w args).Forall₂ TyRefinement.IsRefinedBy (fieldAddrResult l j w args') := by
  cases w with
  | none =>
    match args, args', h with
    | .cons p .nil, .cons p' .nil, ⟨hp, _⟩ =>
      refine ⟨?_, trivial⟩
      show fieldAddrValue l j p ⊑ fieldAddrValue l j p'
      cases p with
      | poison => trivial
      | value x =>
        cases p' with
        | poison => exact hp.elim
        | value x' =>
          cases (hp : x = x')
          exact rfl
  | some _ =>
    match args, args', h with
    | .cons p (.cons k .nil), .cons p' (.cons k' .nil), ⟨hp, hk, _⟩ =>
      refine ⟨?_, trivial⟩
      show elemAddrValue l j p k ⊑ elemAddrValue l j p' k'
      cases p with
      | poison => trivial
      | value x =>
        cases k with
        | poison => trivial
        | value y =>
          cases p' with
          | poison => exact hp.elim
          | value x' =>
            cases k' with
            | poison => exact hk.elim
            | value y' =>
              cases (hp : x = x')
              cases (hk : y = y')
              exact rfl

/-- `fieldAddr` never ends in UB. -/
theorem fieldAddr_neverUB : NeverUB (d := CoreDialect) (.fieldAddr s j n w) := fun lay ρ L args =>
  ⟨fun _ => by rw [fieldAddr_denote]; exact noUB_lift fun _ h => (by cases h),
    fun h => nomatch h⟩

/-- On a pointer and an index, neither poison, `fieldAddr` gives a pointer,
never poison. -/
theorem fieldAddr_makesNoPoison : MakesNoPoison (d := CoreDialect) (.fieldAddr s j n w) := by
  intro _ N _ lay ρ L args hnp S rs S' h
  rw [fieldAddr_denote] at h
  rcases (SetM.lift_apply _ S _).1 h with ⟨a, ha, he⟩ | ⟨_, -, he⟩
  · cases he
    cases ha
    exact fieldAddrResult_defined s j n w hnp
  · cases he

/-- `fieldAddr` has an outcome from any memories. -/
theorem fieldAddr_memTotal : MemTotal (d := CoreDialect) (.fieldAddr s j n w) := fun lay ρ L args =>
  ⟨fun _ => (by rw [fieldAddr_denote]; exact hasOutcome_lift ⟨_, rfl⟩), fun h => nomatch h⟩

/-- On operands that refine others, from memories that refine others,
`fieldAddr` gives a pointer that refines the other's and keeps the
memories. -/
theorem fieldAddr_memMonotone : MemMonotone (d := CoreDialect) (.fieldAddr s j n w) :=
  fun lay ρ L args args' hr => by
    refine ⟨fun _ => ?_, fun h => nomatch h⟩
    rw [fieldAddr_denote, fieldAddr_denote]
    refine StateRefinedBy.lift fun e he => ?_
    cases he
    exact ⟨_, rfl, fieldAddrResult_isRefinedBy s j n w hr⟩

/-- A poison operand gives a poison pointer, and `fieldAddr` is never UB,
so it propagates poison with memory. -/
theorem fieldAddr_memPropagates : MemPropagatesPoison (d := CoreDialect) (.fieldAddr s j n w) where
  poisonOut lay ρ L args hany S rs S' h := by
    rw [fieldAddr_denote] at h
    rcases (SetM.lift_apply _ S _).1 h with ⟨a, ha, he⟩ | ⟨_, -, he⟩
    · cases he
      cases ha
      exact fieldAddrResult_poison s j n w hany
    · cases he
  ubByOwnRules lay ρ L args S r _ h := by
    rw [fieldAddr_denote] at h
    rcases (SetM.lift_apply _ S _).1 h with ⟨_, -, he⟩ | ⟨_, hr, -⟩
    · cases he
    · cases hr

/-- The operands of `fieldAddr` of the pointer with no provenance at offset
0, and the index 0 when it takes one: neither is poison. -/
def fieldAddrZero : (w : Option Nat) → HVector toType (Fir.sig (d := CoreDialect) (Op.fieldAddr s j n w))
  | none => .cons (.value ⟨none, 0⟩) .nil
  | some _ => .cons (.value ⟨none, 0⟩) (.cons (.value 0) .nil)

/-- `fieldAddr` gives a result on a defined pointer and index, from memories
inside a call. -/
theorem fieldAddr_memReturnsOnDefined :
    MemReturnsOnDefined (d := CoreDialect) (.fieldAddr s j n w) := by
  intro _ _ lay ρ L
  refine ⟨fieldAddrZero s j n w, ?_, Memories.empty.enter,
    fieldAddrResult (L.layout? s) j w (fieldAddrZero s j n w), Memories.empty.enter,
    List.cons_ne_nil _ _, ?_⟩
  · cases w <;> rintro (h | h | h) <;> cases h
  · rw [fieldAddr_denote]
    exact (SetM.lift_apply _ _ _).2 (.inl ⟨_, rfl, rfl⟩)

end Fir.Core
