import Fir.Core.MemRules
import Fir.Execution.MemoryLoadLaws
import Fir.Execution.MemoryPoison

/-!
# Load obligations

`load` touches memory, so it has no rule in the set monad and no tie to it:
it meets each obligation with memory by its own rule, wherever a run names
the core's memories and whatever their layout entries. On a poison pointer
its rule is UB, and on a pointer it is a load in the state layer with its
units decoded, and that load has one outcome from any memories, the units
it loads or UB, and keeps the memories (the section on loads in the state
layer). So:

* _Effects._ It may be UB and may give poison, as it declares, so neither
  obligation asks anything of it. It writes no unit of any memory, and
  allocates and frees in none. It reads no memory but the memory of its
  pointer, the one it declares: replacing another memory changes neither
  what it loads nor why it faults.
* _Totality._ It has an outcome from any memories: UB, or a value.
* _Monotonicity._ A poison pointer is UB, which every outcome refines. On
  the same pointer, from memories that refine others, it faults for the
  same reason or loads units that refine the others', and their decoding
  refines the others' value.
* _Poison with memory._ Its one operand is the pointer, so a poison operand
  gives no result, and its UB is the UB that a pointer with no provenance in
  its place gives, from the same memories. It gives a result from memories
  inside a call that hold an allocation of its type, at its alignment.
* _Finitely many outcomes._ It has at most one that ends, from any
  memories.

In the set monad it has no outcome, so it propagates poison there and is
monotone there with nothing to check.
-/

namespace Fir.Core

open Memory

variable (o : Memory.Ordering) (w : Nat) (a : Option Nat) (n : Nat)

section

variable {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : Mem → N) (L : RunItems)

local notation "SM" => StateT (Memories N (unitsOf lay)) SetM

/-- The load that `load`'s rule makes through the pointer `p`, in the state
layer over the set monad. -/
abbrev loadAccess (p : Pointer) : SM (List (MemUnit (unitsOf lay (ρ n)))) :=
  MonadMemory.load (ρ n) p (loadShape (lay (ρ n)) w a).1 (loadShape (lay (ρ n)) w a).2

/-- `load` runs with memory by its rule. -/
theorem load_denote (p : PoisonOr Pointer) :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ L
    @Eq (SM (HVector toType [Ty.int w]))
      (DialectDenote.denote (d := CoreDialect) (m := SM) (Op.load o w a n) (.cons p .nil))
      (loadRule lay ρ w a n p) :=
  rfl

/-- On a poison pointer, `load`'s rule ends in UB, from any memories. -/
theorem loadRule_poison (S : Memories N (unitsOf lay)) (e : Ev (HVector toType [Ty.int w] ×
    Memories N (unitsOf lay))) : (loadRule lay ρ w a n .poison : SM _) S e ↔ e = .ub poisonPointer :=
  Iff.rfl

/-- On a pointer, `load`'s rule is its load, with the units decoded. -/
theorem loadRule_value (p : Pointer) :
    (loadRule lay ρ w a n (.value p) : SM _) = loadResult (lay (ρ n)) w <$> loadAccess w a n lay ρ p :=
  rfl

/-- What `load` runs by its own rule has a property when its rule has it on
every pointer. -/
theorem load_ownRuleHas {P : {α : Type} → SM α → Prop}
    (h : ∀ p, P (loadRule lay ρ w a n p : SM (HVector toType [Ty.int w]))) :
    OwnRuleHas lay ρ L P (d := CoreDialect) (.load o w a n) := fun
  | .cons p .nil => ⟨fun _ => h p, fun h => nomatch h⟩

/-- `load` writes no unit of any memory. -/
theorem load_writesNot (x : N) :
    OwnRuleHas lay ρ L (WritesNot x) (d := CoreDialect) (.load o w a n) :=
  load_ownRuleHas o w a n lay ρ L fun
    | .poison => fun _ _ _ h => nomatch h
    | .value p => (Fir.load_writesNot (unit := unitsOf lay) _ p _ _ x).map _

/-- `load` neither allocates nor frees in any memory. -/
theorem load_allocatesNot (x : N) :
    OwnRuleHas lay ρ L (AllocatesNot x) (d := CoreDialect) (.load o w a n) :=
  load_ownRuleHas o w a n lay ρ L fun
    | .poison => fun _ _ _ h => nomatch h
    | .value p => (Fir.load_allocatesNot (unit := unitsOf lay) _ p _ _ x).map _

/-- `load` reads no memory but the memory of its pointer. -/
theorem load_readsNot (x : N)
    (hx : ¬ ((Fir.effects (d := CoreDialect) (.load o w a n)).reads.map ρ).Has x) :
    OwnRuleHas lay ρ L (ReadsNot x) (d := CoreDialect) (.load o w a n) :=
  load_ownRuleHas o w a n lay ρ L fun
    | .poison => fun _ _ _ e he => by
      subst he
      exact ⟨_, rfl, rfl⟩
    | .value p => (Fir.load_readsNot (unit := unitsOf lay) _ p _ _
        fun h => hx (List.mem_singleton.2 h.symm)).map _

/-- `load` has an outcome from any memories. -/
theorem load_memTotal : MemTotal (d := CoreDialect) (.load o w a n) := fun lay ρ L =>
  load_ownRuleHas o w a n lay ρ L fun
    | .poison => fun _ => ⟨_, rfl⟩
    | .value p => (Fir.load_hasOutcome (unit := unitsOf lay) _ p _ _).map _

/-- `load` has at most one outcome that ends, from any memories. -/
theorem load_finitelyMany
    (args : HVector toType (Fir.sig (d := CoreDialect) (Op.load o w a n))) :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ L
    FinitelyMany (DialectDenote.denote (d := CoreDialect)
      (m := SM) (Op.load o w a n) args) := by
  match args with
  | .cons p .nil =>
    show FinitelyMany (loadRule lay ρ w a n p : SM _)
    cases (p : PoisonOr Pointer) with
    | poison => exact fun _ => ⟨[], fun _ h => nomatch h⟩
    | value q =>
      intro S
      obtain ⟨L, hL⟩ := Fir.load_finitelyMany (unit := unitsOf lay) (ρ n) q
        (loadShape (lay (ρ n)) w a).1 (loadShape (lay (ρ n)) w a).2 S
      refine ⟨L.map fun r => (loadResult (lay (ρ n)) w r.1, r.2), fun x hx => ?_⟩
      rcases (SetM.stateMap_apply _ _ S _).1 hx with ⟨us, S', hp, he⟩ | ⟨_, _, he⟩ <;> cases he
      exact List.mem_map.2 ⟨(us, S'), hL _ hp, rfl⟩

end

/-- From memories that refine others, `load` on a pointer that refines
another faults for the same reason or gives a value that refines the
other's; on a poison pointer it is UB, which every outcome refines. -/
theorem load_memMonotone : MemMonotone (d := CoreDialect) (.load o w a n) := by
  intro N _ lay ρ L args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons p .nil, .cons p' .nil, ⟨hp, _⟩ =>
    show StateRefinedBy _ (loadRule lay ρ w a n p) (loadRule lay ρ w a n p')
    cases p with
    | poison => exact fun _ _ _ _ _ => ⟨_, rfl, trivial⟩
    | value q =>
      cases p' with
      | poison => exact (hp : False).elim
      | value q' =>
        cases (hp : q = q')
        exact StateRefinedBy.map (loadResult (lay (ρ n)) w)
          (fun h => ⟨decodeInt_isRefinedBy w _ h, trivial⟩)
          (Fir.load_refines (unit := unitsOf lay) _ q _ _)

/-- `load` propagates poison with memory: a poison pointer gives no result,
and its UB is the UB of a pointer with no provenance, from the same
memories. -/
theorem load_memPropagates : MemPropagatesPoison (d := CoreDialect) (.load o w a n) where
  poisonOut _ _ _ args hany _ _ _ h := by
    match args, hany with
    | .cons p .nil, hany =>
      have hp : p = .poison := hany.elim id False.elim
      subst hp
      exact nomatch h
  ubByOwnRules lay ρ L args S _ hany _ := by
    match args, hany with
    | .cons p .nil, hany =>
      refine ⟨HVector.cons (f := toType) (a := Ty.ptr n) (.value ⟨none, 0⟩ : PoisonOr Pointer) .nil,
        ⟨?_, .inl ?_, trivial⟩, Fault.noProvenance.reason, ?_⟩
      · rintro (h | h) <;> cases h
      · exact hany.elim id False.elim
      · show (loadResult (lay (ρ n)) w <$> loadAccess w a n lay ρ ⟨none, 0⟩) S _
        exact (SetM.stateMap_apply _ _ S _).2 (.inr ⟨_, (Fir.load_apply _ _ _ _ S _).2
          (.inr ⟨.noProvenance, rfl, rfl⟩), rfl⟩)

/-- `load` gives a result from memories inside a call that hold a fresh
allocation of its units at its alignment, through the pointer to it: the
value its poison units decode to. -/
theorem load_memReturnsOnDefined : MemReturnsOnDefined (d := CoreDialect) (.load o w a n) :=
  fun lay ρ L => by
  let sh := loadShape (lay (ρ n)) w a
  let q := (Memories.empty : Memories _ (unitsOf lay)).enter.alloc (ρ n) .heap sh.1 sh.2
  have hl : q.2.load (ρ n) q.1 sh.1 sh.2 = .ok (List.replicate sh.1 .poison) := by
    show (q.2.mem (ρ n)).loadAligned q.1 sh.1 sh.2 = _
    rw [Memories.alloc_mem_self, Memories.alloc_fst]
    rw [Memory.loadAligned_of_aligned (by rw [← Memory.alloc_fst, Memory.aligned_alloc]; simp)]
    exact Memory.load_alloc _ _ (Int.le_refl 0) (by simp)
  refine ⟨HVector.cons (f := toType) (a := Ty.ptr n) (.value q.1 : PoisonOr Pointer) .nil, ?_, q.2,
    loadResult (lay (ρ n)) w (List.replicate sh.1 .poison), q.2, ?_, ?_⟩
  · rintro (h | h) <;> cases h
  · rw [Memories.alloc_frames (by decide)]
    exact List.cons_ne_nil _ _
  · show (loadResult (lay (ρ n)) w <$> loadAccess w a n lay ρ q.1) q.2 _
    exact (SetM.stateMap_apply _ _ q.2 _).2
      (.inl ⟨_, q.2, (Fir.load_apply _ _ _ _ q.2 _).2 (.inl ⟨_, hl, rfl⟩), rfl⟩)

end Fir.Core
