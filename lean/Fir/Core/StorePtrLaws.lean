import Fir.Core.StoreLaws
import Fir.Core.LoadPtrLaws

/-!
# Pointer store obligations

`storePtr` touches memory, so it meets each obligation with memory by its
own rule, as `store` does (the section on store obligations), wherever a
run names the core's memories and whatever their layout entries. Its rule
is `store`'s with the encoding of a pointer of its memory `M`, so each
proof is `store`'s with that encoding:

* _Effects._ It may be UB, as it declares. It gives no result, so it makes
  no poison. It writes no memory but the memory of its pointer, reads no
  memory, its own included, and allocates and frees in none.
* _Totality._ It has an outcome from any memories: UB, or the memories it
  writes.
* _Monotonicity._ A poison pointer is UB, which every outcome refines. On
  the same pointer, a value that refines another has an encoding that
  refines the other's (`encodePtr_isRefinedBy`), so to memories that refine
  others the store faults for the same reason or gives memories that refine
  the others'.
* _Poison with memory._ It has no result. Its UB on a poison pointer is the
  UB of a pointer with no provenance in its place, and a poison value is UB
  only where a defined pointer's units, as many, are, from the same
  memories. It gives a result from memories inside a call that hold an
  allocation of its units at its alignment.
* _Finitely many outcomes._ It has at most one that ends, from any
  memories.
-/

namespace Fir.Core

open Memory

variable (o : Memory.Ordering) (mp : Nat) (a : Option Nat) (n : Nat)

section

variable {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : Mem → N)

local notation "SM" => StateT (Memories N (unitsOf lay)) SetM

/-- The store that `storePtr`'s rule makes of the value `v` through the
pointer `p`, in the state layer over the set monad. -/
abbrev storePtrAccess (v : PoisonOr Pointer) (p : Pointer) : SM Unit :=
  MonadMemory.store (ρ n) p (storePtrUnits lay ρ mp n v) (ptrShape lay ρ mp a n).2

/-- `storePtr` runs with memory by its rule. -/
theorem storePtr_denote (v p : PoisonOr Pointer) :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ
    @Eq (SM (HVector toType ([] : List Ty)))
      (DialectDenote.denote (d := CoreDialect) (m := SM) (Op.storePtr o mp a n)
        (.cons v (.cons p .nil)))
      (storePtrRule lay ρ mp a n v p) :=
  rfl

/-- What `storePtr` runs by its own rule has a property when its rule has
it on every value and pointer. -/
theorem storePtr_ownRuleHas {P : {α : Type} → SM α → Prop}
    (h : ∀ v p, P (storePtrRule lay ρ mp a n v p : SM (HVector toType ([] : List Ty)))) :
    OwnRuleHas lay ρ P (d := CoreDialect) (.storePtr o mp a n) := fun
  | .cons v (.cons p .nil) => ⟨fun _ => h v p, fun h => nomatch h⟩

/-- `storePtr` writes no memory but the memory of its pointer. -/
theorem storePtr_writesNot (x : N)
    (hx : ¬ ((Fir.effects (d := CoreDialect) (.storePtr o mp a n)).writes.map ρ).Has x) :
    OwnRuleHas lay ρ (WritesNot x) (d := CoreDialect) (.storePtr o mp a n) :=
  storePtr_ownRuleHas o mp a n lay ρ fun
    | _, .poison => fun _ _ _ h => nomatch h
    | _, .value p => (Fir.store_writesNot (unit := unitsOf lay) _ p _ _
        fun h => hx (List.mem_singleton.2 h.symm)).map _

/-- `storePtr` reads no memory, its own included. -/
theorem storePtr_readsNot (x : N) :
    OwnRuleHas lay ρ (ReadsNot x) (d := CoreDialect) (.storePtr o mp a n) :=
  storePtr_ownRuleHas o mp a n lay ρ fun
    | _, .poison => fun _ _ _ e he => by
      subst he
      exact ⟨_, rfl, rfl⟩
    | _, .value p => (Fir.store_readsNot (unit := unitsOf lay) _ p _ _ x).map _

/-- `storePtr` neither allocates nor frees in any memory. -/
theorem storePtr_allocatesNot (x : N) :
    OwnRuleHas lay ρ (AllocatesNot x) (d := CoreDialect) (.storePtr o mp a n) :=
  storePtr_ownRuleHas o mp a n lay ρ fun
    | _, .poison => fun _ _ _ h => nomatch h
    | _, .value p => (Fir.store_allocatesNot (unit := unitsOf lay) _ p _ _ x).map _

/-- `storePtr` has an outcome from any memories. -/
theorem storePtr_memTotal : MemTotal (d := CoreDialect) (.storePtr o mp a n) := fun lay ρ =>
  storePtr_ownRuleHas o mp a n lay ρ fun
    | _, .poison => fun _ => ⟨_, rfl⟩
    | _, .value p => (Fir.store_hasOutcome (unit := unitsOf lay) _ p _ _).map _

/-- `storePtr` has at most one outcome that ends, from any memories. -/
theorem storePtr_finitelyMany
    (args : HVector toType (Fir.sig (d := CoreDialect) (Op.storePtr o mp a n))) :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ
    FinitelyMany (DialectDenote.denote (d := CoreDialect)
      (m := SM) (Op.storePtr o mp a n) args) := by
  match args with
  | .cons v (.cons p .nil) =>
    show FinitelyMany (storePtrRule lay ρ mp a n v p : SM _)
    cases (p : PoisonOr Pointer) with
    | poison => exact fun _ => ⟨[], fun _ h => nomatch h⟩
    | value q =>
      intro S
      obtain ⟨L, hL⟩ := Fir.store_finitelyMany (unit := unitsOf lay) (ρ n) q
        (storePtrUnits lay ρ mp n v) (ptrShape lay ρ mp a n).2 S
      refine ⟨L.map fun r => (HVector.nil, r.2), fun x hx => ?_⟩
      rcases (SetM.stateMap_apply _ _ S _).1 hx with ⟨u, S', hp, he⟩ | ⟨_, _, he⟩ <;> cases he
      exact List.mem_map.2 ⟨(u, S'), hL _ hp, rfl⟩

end

/-- `storePtr` gives no result, so none is poison. -/
theorem storePtr_makesNoPoison : MakesNoPoison (d := CoreDialect) (.storePtr o mp a n) := by
  intro _ N _ lay ρ args _ S rs S' _ h
  cases rs
  exact h

/-- To memories that refine others, `storePtr` of a pointer that refines
another, through a pointer that refines another, faults for the same
reason or gives memories that refine the others'; on a poison pointer it
is UB, which every outcome refines. -/
theorem storePtr_memMonotone : MemMonotone (d := CoreDialect) (.storePtr o mp a n) := by
  intro N _ lay ρ args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons v (.cons p .nil), .cons v' (.cons p' .nil), ⟨hv, hp, _⟩ =>
    show StateRefinedBy _ (storePtrRule lay ρ mp a n v p) (storePtrRule lay ρ mp a n v' p')
    cases p with
    | poison => exact fun _ _ _ _ _ => ⟨_, rfl, trivial⟩
    | value q =>
      cases p' with
      | poison => exact (hp : False).elim
      | value q' =>
        cases (hp : q = q')
        exact StateRefinedBy.map (fun _ => HVector.nil) (fun _ => trivial)
          (Fir.store_refines (unit := unitsOf lay) _ q _ (encodePtr_isRefinedBy _ _ _ hv))

/-- `storePtr` propagates poison with memory: it gives no result, a poison
pointer is the UB of a pointer with no provenance, and a poison value is UB
only where a defined pointer's units, as many, are, from the same
memories. -/
theorem storePtr_memPropagates : MemPropagatesPoison (d := CoreDialect) (.storePtr o mp a n) where
  poisonOut _ _ _ _ _ rs _ _ := by
    cases rs
    trivial
  ubByOwnRules lay ρ args S r hany hub := by
    match args, hany, hub with
    | .cons v (.cons .poison .nil), _, _ =>
      refine ⟨HVector.cons (f := toType) (a := Ty.ptr mp) (.value (match v with
          | .poison => ⟨none, 0⟩
          | .value q => q) : PoisonOr Pointer)
        (HVector.cons (f := toType) (a := Ty.ptr n) (.value ⟨none, 0⟩ : PoisonOr Pointer) .nil),
        ⟨?_, ?_, .inl rfl, trivial⟩, Fault.noProvenance.reason, ?_⟩
      · rintro (h | h | h) <;> cases h
      · cases v
        · exact .inl rfl
        · exact .inr rfl
      · let v' : PoisonOr Pointer := .value (match v with
          | .poison => ⟨none, 0⟩
          | .value q => q)
        show ((fun _ => HVector.nil) <$> storePtrAccess mp a n lay ρ v' ⟨none, 0⟩) S _
        have hn : S.store (ρ n) ⟨none, 0⟩ (storePtrUnits lay ρ mp n v') (ptrShape lay ρ mp a n).2 =
            .error .noProvenance := rfl
        exact (SetM.stateMap_apply _ _ S _).2 (.inr ⟨_, (Fir.store_apply _ _ _ _ S _).2
          (.inr ⟨.noProvenance, hn, rfl⟩), rfl⟩)
    | .cons .poison (.cons (.value q) .nil), _, hub =>
      have hub : ((fun _ => HVector.nil) <$> storePtrAccess mp a n lay ρ .poison q) S (.ub r) := hub
      rcases (SetM.stateMap_apply _ _ S _).1 hub with ⟨_, _, _, he⟩ | ⟨r', hs, he⟩
      · cases he
      rcases (Fir.store_apply _ _ _ _ S _).1 hs with ⟨_, _, he'⟩ | ⟨f, hf, -⟩
      · cases he'
      refine ⟨HVector.cons (f := toType) (a := Ty.ptr mp) (.value ⟨none, 0⟩ : PoisonOr Pointer)
        (HVector.cons (f := toType) (a := Ty.ptr n) (.value q : PoisonOr Pointer) .nil),
        ⟨?_, .inl rfl, .inr rfl, trivial⟩, f.reason, ?_⟩
      · rintro (h | h | h) <;> cases h
      · show ((fun _ => HVector.nil) <$> storePtrAccess mp a n lay ρ (.value ⟨none, 0⟩) q) S _
        refine (SetM.stateMap_apply _ _ S _).2 (.inr ⟨_, (Fir.store_apply _ _ _ _ S _).2
          (.inr ⟨f, Memory.Memories.store_error_length ?_ hf, rfl⟩), rfl⟩)
        simp only [storePtrUnits, length_encodePtr]
    | .cons (.value _) (.cons (.value _) .nil), hany, _ =>
      rcases hany with h | h | h <;> cases h

/-- `storePtr` gives a result from memories inside a call that hold a
fresh allocation of its units at its alignment, through the pointer to it:
it stores a pointer with no provenance there. -/
theorem storePtr_memReturnsOnDefined :
    MemReturnsOnDefined (d := CoreDialect) (.storePtr o mp a n) := fun lay ρ => by
  let v : PoisonOr Pointer := .value ⟨none, 0⟩
  let us := storePtrUnits lay ρ mp n v
  let al := (ptrShape lay ρ mp a n).2
  let q := (Memories.empty : Memories _ (unitsOf lay)).enter.alloc (ρ n) .heap us.length al
  have hs : ∃ M', (q.2.mem (ρ n)).storeAligned q.1 us al = .ok M' := by
    rw [Memories.alloc_mem_self, Memories.alloc_fst]
    rw [Memory.storeAligned_of_aligned (by rw [← Memory.alloc_fst, Memory.aligned_alloc]; simp)]
    exact ⟨_, Memory.store_of_locate (Memory.locate_eq_ok.2 ⟨rfl, Memory.alloc_blocks_new _ _ _ _,
      rfl, Int.le_refl 0, by simp, rfl⟩)⟩
  obtain ⟨M', hM'⟩ := hs
  refine ⟨HVector.cons (f := toType) (a := Ty.ptr mp) (.value ⟨none, 0⟩ : PoisonOr Pointer)
    (HVector.cons (f := toType) (a := Ty.ptr n) (.value q.1 : PoisonOr Pointer) .nil), ?_, q.2,
    HVector.nil, q.2.set (ρ n) M', ?_, ?_⟩
  · rintro (h | h | h) <;> cases h
  · rw [Memories.alloc_frames (by decide)]
    exact List.cons_ne_nil _ _
  · show ((fun _ => HVector.nil) <$> storePtrAccess mp a n lay ρ v q.1) q.2 _
    exact (SetM.stateMap_apply _ _ q.2 _).2
      (.inl ⟨_, _, (Fir.store_apply _ _ _ _ q.2 _).2 (.inl ⟨q.2.set (ρ n) M', by
        show ((q.2.mem (ρ n)).storeAligned q.1 us al).map (q.2.set (ρ n)) = _
        rw [hM']
        rfl, rfl⟩), rfl⟩)

end Fir.Core
