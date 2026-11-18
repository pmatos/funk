import Fir.Core.MemRules
import Fir.Execution.MemoryStoreLaws
import Fir.Execution.MemoryPoison

/-!
# Store obligations

`store` touches memory, so it has no rule in the set monad and no tie to
it: it meets each obligation with memory by its own rule, wherever a run
names the core's memories and whatever their layout entries. On a poison
pointer its rule is UB, and on a pointer it is a store in the state layer
of the value's encoding, and that store has one outcome from any memories,
UB or the memories with its units written (the section on stores in the
state layer). So:

* _Effects._ It may be UB, as it declares, so that obligation asks nothing
  of it. It gives no result, so it makes no poison. It writes no memory but
  the memory of its pointer, the one it declares. It reads no memory, its
  own included, and allocates and frees in none.
* _Totality._ It has an outcome from any memories: UB, or the memories it
  writes.
* _Monotonicity._ A poison pointer is UB, which every outcome refines. On
  the same pointer, a value that refines another has an encoding that
  refines the other's, so to memories that refine others the store faults
  for the same reason or gives memories that refine the others'.
* _Poison with memory._ It has no result, so a poison operand gives none.
  Its UB on a poison pointer is the UB that a pointer with no provenance in
  its place gives, from the same memories. A poison value is never UB by
  itself: a store of its poison units faults only where a store of a
  defined value's units, as many, faults too, since whether a store faults
  depends on how many units it writes, not on what they hold. It gives a
  result from memories inside a call that hold an allocation of its type,
  at its alignment.
* _Finitely many outcomes._ It has at most one that ends, from any
  memories.

In the set monad it has no outcome, so it propagates poison there and is
monotone there with nothing to check.
-/

namespace Fir

open Memory

/-- Whether an aligned store faults, and why, depends on how many units it
writes, not on what they hold. -/
theorem Memory.Memory.storeAligned_error_length {u : Nat} {M : Memory u} {p : Pointer}
    {us us' : List (MemUnit u)} {al : Nat} {f : Fault} (hl : us'.length = us.length)
    (h : M.storeAligned p us al = .error f) : M.storeAligned p us' al = .error f := by
  unfold Memory.storeAligned at h ⊢
  cases hs : M.store p us with
  | error g =>
    rw [hs] at h
    cases h
    rw [Memory.store_eq_error.2 (hl ▸ Memory.store_eq_error.1 hs)]
  | ok M' =>
    rw [hs] at h
    obtain ⟨a, b, o, hloc, -⟩ := Memory.store_eq_ok hs
    rw [Memory.store_of_locate (us := us') (by rw [hl]; exact hloc)]
    cases ha : M.aligned p al <;> simp_all

/-- Whether a store to the memories of a run faults, and why, depends on how
many units it writes, not on what they hold. -/
theorem Memory.Memories.store_error_length {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]
    {S : Memories Mem unit} {x : Mem} {p : Pointer} {us us' : List (MemUnit (unit x))} {al : Nat}
    {f : Fault} (hl : us'.length = us.length) (h : S.store x p us al = .error f) :
    S.store x p us' al = .error f := by
  unfold Memories.store at h ⊢
  cases hs : (S.mem x).storeAligned p us al with
  | ok _ => rw [hs] at h; cases h
  | error g =>
    rw [hs] at h
    cases h
    rw [Memory.Memory.storeAligned_error_length hl hs]
    rfl

end Fir

namespace Fir.Core

open Memory

variable (o : Memory.Ordering) (w : Nat) (a : Option Nat) (n : Nat)

section

variable {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : Mem → N) (L : RunItems)

local notation "SM" => StateT (Memories N (unitsOf lay)) SetM

/-- The store that `store`'s rule makes of the value `v` through the
pointer `p`, in the state layer over the set monad. -/
abbrev storeAccess (v : PoisonOr (BitVec w)) (p : Pointer) : SM Unit :=
  MonadMemory.store (ρ n) p (storeUnits (lay (ρ n)) v) (storeAlign (lay (ρ n)) w a)

/-- `store` runs with memory by its rule. -/
theorem store_denote (v : PoisonOr (BitVec w)) (p : PoisonOr Pointer) :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ L
    @Eq (SM (HVector toType ([] : List Ty)))
      (DialectDenote.denote (d := CoreDialect) (m := SM) (Op.store o w a n) (.cons v (.cons p .nil)))
      (storeRule lay ρ w a n v p) :=
  rfl

/-- On a poison pointer, `store`'s rule ends in UB, from any memories. -/
theorem storeRule_poison (v : PoisonOr (BitVec w)) (S : Memories N (unitsOf lay))
    (e : Ev (HVector toType ([] : List Ty) × Memories N (unitsOf lay))) :
    (storeRule lay ρ w a n v .poison : SM _) S e ↔ e = .ub poisonStorePointer :=
  Iff.rfl

/-- On a pointer, `store`'s rule is its store, with no result. -/
theorem storeRule_value (v : PoisonOr (BitVec w)) (p : Pointer) :
    (storeRule lay ρ w a n v (.value p) : SM _) =
      (fun _ => HVector.nil) <$> storeAccess w a n lay ρ v p :=
  rfl

/-- What `store` runs by its own rule has a property when its rule has it
on every value and pointer. -/
theorem store_ownRuleHas {P : {α : Type} → SM α → Prop}
    (h : ∀ v p, P (storeRule lay ρ w a n v p : SM (HVector toType ([] : List Ty)))) :
    OwnRuleHas lay ρ L P (d := CoreDialect) (.store o w a n) := fun
  | .cons v (.cons p .nil) => ⟨fun _ => h v p, fun h => nomatch h⟩

/-- `store` writes no memory but the memory of its pointer. -/
theorem store_writesNot (x : N)
    (hx : ¬ ((Fir.effects (d := CoreDialect) (.store o w a n)).writes.map ρ).Has x) :
    OwnRuleHas lay ρ L (WritesNot x) (d := CoreDialect) (.store o w a n) :=
  store_ownRuleHas o w a n lay ρ L fun
    | _, .poison => fun _ _ _ h => nomatch h
    | _, .value p => (Fir.store_writesNot (unit := unitsOf lay) _ p _ _
        fun h => hx (List.mem_singleton.2 h.symm)).map _

/-- `store` reads no memory, its own included. -/
theorem store_readsNot (x : N) :
    OwnRuleHas lay ρ L (ReadsNot x) (d := CoreDialect) (.store o w a n) :=
  store_ownRuleHas o w a n lay ρ L fun
    | _, .poison => fun _ _ _ e he => by
      subst he
      exact ⟨_, rfl, rfl⟩
    | _, .value p => (Fir.store_readsNot (unit := unitsOf lay) _ p _ _ x).map _

/-- `store` neither allocates nor frees in any memory. -/
theorem store_allocatesNot (x : N) :
    OwnRuleHas lay ρ L (AllocatesNot x) (d := CoreDialect) (.store o w a n) :=
  store_ownRuleHas o w a n lay ρ L fun
    | _, .poison => fun _ _ _ h => nomatch h
    | _, .value p => (Fir.store_allocatesNot (unit := unitsOf lay) _ p _ _ x).map _

/-- `store` has an outcome from any memories. -/
theorem store_memTotal : MemTotal (d := CoreDialect) (.store o w a n) := fun lay ρ L =>
  store_ownRuleHas o w a n lay ρ L fun
    | _, .poison => fun _ => ⟨_, rfl⟩
    | _, .value p => (Fir.store_hasOutcome (unit := unitsOf lay) _ p _ _).map _

/-- `store` has at most one outcome that ends, from any memories. -/
theorem store_finitelyMany
    (args : HVector toType (Fir.sig (d := CoreDialect) (Op.store o w a n))) :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ L
    FinitelyMany (DialectDenote.denote (d := CoreDialect)
      (m := SM) (Op.store o w a n) args) := by
  match args with
  | .cons v (.cons p .nil) =>
    show FinitelyMany (storeRule lay ρ w a n v p : SM _)
    cases (p : PoisonOr Pointer) with
    | poison => exact fun _ => ⟨[], fun _ h => nomatch h⟩
    | value q =>
      intro S
      obtain ⟨L, hL⟩ := Fir.store_finitelyMany (unit := unitsOf lay) (ρ n) q
        (storeUnits (lay (ρ n)) v) (storeAlign (lay (ρ n)) w a) S
      refine ⟨L.map fun r => (HVector.nil, r.2), fun x hx => ?_⟩
      rcases (SetM.stateMap_apply _ _ S _).1 hx with ⟨u, S', hp, he⟩ | ⟨_, _, he⟩ <;> cases he
      exact List.mem_map.2 ⟨(u, S'), hL _ hp, rfl⟩

end

/-- `store` gives no result, so none is poison. -/
theorem store_makesNoPoison : MakesNoPoison (d := CoreDialect) (.store o w a n) := by
  intro _ N _ lay ρ L args _ S rs S' _ h
  cases rs
  exact h

/-- To memories that refine others, `store` of a value that refines
another, through a pointer that refines another, faults for the same
reason or gives memories that refine the others'; on a poison pointer it
is UB, which every outcome refines. -/
theorem store_memMonotone : MemMonotone (d := CoreDialect) (.store o w a n) := by
  intro N _ lay ρ L args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons v (.cons p .nil), .cons v' (.cons p' .nil), ⟨hv, hp, _⟩ =>
    show StateRefinedBy _ (storeRule lay ρ w a n v p) (storeRule lay ρ w a n v' p')
    cases p with
    | poison => exact fun _ _ _ _ _ => ⟨_, rfl, trivial⟩
    | value q =>
      cases p' with
      | poison => exact (hp : False).elim
      | value q' =>
        cases (hp : q = q')
        exact StateRefinedBy.map (fun _ => HVector.nil) (fun _ => trivial)
          (Fir.store_refines (unit := unitsOf lay) _ q _ (encodeInt_isRefinedBy _ hv))

/-- `store` propagates poison with memory: it gives no result, a poison
pointer is the UB of a pointer with no provenance, and a poison value is UB
only where a defined value's units, as many, are, from the same memories. -/
theorem store_memPropagates : MemPropagatesPoison (d := CoreDialect) (.store o w a n) where
  poisonOut _ _ _ _ _ _ rs _ _ := by
    cases rs
    trivial
  ubByOwnRules lay ρ L args S r hany hub := by
    match args, hany, hub with
    | .cons v (.cons .poison .nil), _, _ =>
      refine ⟨HVector.cons (f := toType) (a := Ty.int w) (.value (match v with
          | .poison => 0#w
          | .value b => b))
        (HVector.cons (f := toType) (a := Ty.ptr n) (.value ⟨none, 0⟩ : PoisonOr Pointer) .nil),
        ⟨?_, ?_, .inl rfl, trivial⟩, Fault.noProvenance.reason, ?_⟩
      · rintro (h | h | h) <;> cases h
      · cases v
        · exact .inl rfl
        · exact .inr rfl
      · let v' : PoisonOr (BitVec w) := .value (match v with
          | .poison => 0#w
          | .value b => b)
        show ((fun _ => HVector.nil) <$> storeAccess w a n lay ρ v' ⟨none, 0⟩) S _
        have hn : S.store (ρ n) ⟨none, 0⟩ (storeUnits (lay (ρ n)) v') (storeAlign (lay (ρ n)) w a) =
            .error .noProvenance := rfl
        exact (SetM.stateMap_apply _ _ S _).2 (.inr ⟨_, (Fir.store_apply _ _ _ _ S _).2
          (.inr ⟨.noProvenance, hn, rfl⟩), rfl⟩)
    | .cons .poison (.cons (.value q) .nil), _, hub =>
      have hub : ((fun _ => HVector.nil) <$> storeAccess w a n lay ρ .poison q) S (.ub r) := hub
      rcases (SetM.stateMap_apply _ _ S _).1 hub with ⟨_, _, _, he⟩ | ⟨r', hs, he⟩
      · cases he
      rcases (Fir.store_apply _ _ _ _ S _).1 hs with ⟨_, _, he'⟩ | ⟨f, hf, -⟩
      · cases he'
      refine ⟨HVector.cons (f := toType) (a := Ty.int w) (.value 0#w : PoisonOr (BitVec w))
        (HVector.cons (f := toType) (a := Ty.ptr n) (.value q : PoisonOr Pointer) .nil),
        ⟨?_, .inl rfl, .inr rfl, trivial⟩, f.reason, ?_⟩
      · rintro (h | h | h) <;> cases h
      · show ((fun _ => HVector.nil) <$> storeAccess w a n lay ρ (.value 0#w) q) S _
        refine (SetM.stateMap_apply _ _ S _).2 (.inr ⟨_, (Fir.store_apply _ _ _ _ S _).2
          (.inr ⟨f, Memory.Memories.store_error_length ?_ hf, rfl⟩), rfl⟩)
        simp only [storeUnits, length_encodeInt]
    | .cons (.value _) (.cons (.value _) .nil), hany, _ =>
      rcases hany with h | h | h <;> cases h

/-- `store` gives a result from memories inside a call that hold a fresh
allocation of its units at its alignment, through the pointer to it: it
stores a zero there. -/
theorem store_memReturnsOnDefined : MemReturnsOnDefined (d := CoreDialect) (.store o w a n) :=
  fun lay ρ L => by
  let e := lay (ρ n)
  let us := storeUnits e (.value 0#w)
  let al := storeAlign e w a
  let q := (Memories.empty : Memories _ (unitsOf lay)).enter.alloc (ρ n) .heap us.length al
  have hs : ∃ M', (q.2.mem (ρ n)).storeAligned q.1 us al = .ok M' := by
    rw [Memories.alloc_mem_self, Memories.alloc_fst]
    rw [Memory.storeAligned_of_aligned (by rw [← Memory.alloc_fst, Memory.aligned_alloc]; simp)]
    exact ⟨_, Memory.store_of_locate (Memory.locate_eq_ok.2 ⟨rfl, Memory.alloc_blocks_new _ _ _ _,
      rfl, Int.le_refl 0, by simp, rfl⟩)⟩
  obtain ⟨M', hM'⟩ := hs
  refine ⟨HVector.cons (f := toType) (a := Ty.int w) (.value 0#w : PoisonOr (BitVec w))
    (HVector.cons (f := toType) (a := Ty.ptr n) (.value q.1 : PoisonOr Pointer) .nil), ?_, q.2,
    HVector.nil, q.2.set (ρ n) M', ?_, ?_⟩
  · rintro (h | h | h) <;> cases h
  · rw [Memories.alloc_frames (by decide)]
    exact List.cons_ne_nil _ _
  · show ((fun _ => HVector.nil) <$> storeAccess w a n lay ρ (.value 0#w) q.1) q.2 _
    exact (SetM.stateMap_apply _ _ q.2 _).2
      (.inl ⟨_, _, (Fir.store_apply _ _ _ _ q.2 _).2 (.inl ⟨q.2.set (ρ n) M', by
        show ((q.2.mem (ρ n)).storeAligned q.1 us al).map (q.2.set (ρ n)) = _
        rw [hM']
        rfl, rfl⟩), rfl⟩)

end Fir.Core
