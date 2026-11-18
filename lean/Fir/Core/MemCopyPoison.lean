import Fir.Core.MemCopyLaws

/-!
# Copy and move poison obligations

`memCopy` propagates poison, so it carries the poison obligations with
memory, which it meets by its own rule:

* _Poison out._ It gives no result, so a poison operand gives none.
* _UB only by its own rules._ Where it is UB from the memories `S` on a
  poison operand, it is UB from `S` on defined operands that fill each
  poison. A poison length is UB only where the length it chose is, so that
  length fills it. A poison pointer is UB only for a length other than 0,
  and there a pointer with no provenance fills it: a copy of units through
  it faults, whatever the other pointer is, and a copy whose filled ranges
  partly overlap is UB by that check.
* _A result on defined operands._ A length of 0 gives no result and does
  nothing, from any memories, whatever the pointers are.

It gives no result, so it makes no poison either.
-/

namespace Fir.Core

open Memory

variable (k : CopyKind) (o : Memory.Ordering) (w n : Nat)

/-- The pointer that fills a poison pointer: one with no provenance. -/
def fillPtr : PoisonOr Pointer → Pointer
  | .value p => p
  | .poison => ⟨none, 0⟩

section

variable {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : Mem → N)

local notation "SM" => StateT (Memories N (unitsOf lay)) SetM

/-- A copy of units through a pointer with no provenance, the destination
or the source, faults from any memories. -/
theorem copyUnits_ub_of_noProv (x : N) (dst src : Pointer) (len : Nat)
    (S : Memories N (unitsOf lay)) (h : dst.prov = none ∨ src.prov = none) :
    ∃ r, copyUnits (m := SM) x dst src len 1 1 S (.ub r) := by
  cases hl : S.load x src len 1 with
  | error f => exact ⟨_, (copyUnits_load x dst src len 1 1 S _).2 (.inr ⟨f, hl, rfl⟩)⟩
  | ok us =>
    have hd : dst.prov = none := by
      rcases h with h | h
      · exact h
      · obtain ⟨_, _⟩ := src
        cases h
        cases hl
    have hs : S.store x dst us 1 = .error .noProvenance := by
      obtain ⟨_, _⟩ := dst
      cases hd
      rfl
    exact ⟨_, (copyUnits_load x dst src len 1 1 S _).2
      (.inl ⟨us, hl, (store_apply x dst us 1 S _).2 (.inr ⟨_, hs, rfl⟩)⟩)⟩

/-- The step of a copy or a move of a defined length other than 0 through
two pointers, one of them with no provenance, is UB from any memories: by
the overlap check, or by the copy of units. -/
theorem copyStep_ub_of_noProv (d s : Pointer) (len : Nat) (S : Memories N (unitsOf lay))
    (h : d.prov = none ∨ s.prov = none) :
    ∃ r, (if (k == .copy && partlyOverlap d s len) = true then MonadUB.ub overlapCopy
      else (fun _ => .nil) <$> copyUnits (m := SM) (ρ n) d s len 1 1 :
        SM (HVector toType ([] : List Ty))) S (.ub r) := by
  by_cases hb : (k == .copy && partlyOverlap d s len) = true
  · simp only [hb, ↓reduceIte]
    exact ⟨_, rfl⟩
  · simp only [hb, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨r, hr⟩ := copyUnits_ub_of_noProv lay _ _ _ len S h
    exact ⟨r, (SetM.stateMap_apply _ _ S _).2 (.inr ⟨r, hr, rfl⟩)⟩

/-- Where the rule of a defined length is UB, it is UB on the pointers
that fill each poison pointer. -/
theorem copyLenRule_ub_fill {len : Nat} {d s : PoisonOr Pointer} {S : Memories N (unitsOf lay)}
    {r : String} (h : copyLenRule (m := SM) lay ρ k n len d s S (.ub r)) :
    ∃ r', copyLenRule (m := SM) lay ρ k n len (.value (fillPtr d)) (.value (fillPtr s)) S
      (.ub r') := by
  unfold copyLenRule at h ⊢
  by_cases hlen : len = 0
  · simp only [hlen, ↓reduceIte] at h
    cases h
  · simp only [hlen, ↓reduceIte] at h ⊢
    match d, s, h with
    | .value d, .value s, h => exact ⟨r, h⟩
    | .poison, s, _ => exact copyStep_ub_of_noProv k n lay ρ _ _ len S (.inl rfl)
    | .value _, .poison, _ => exact copyStep_ub_of_noProv k n lay ρ _ _ len S (.inr rfl)

end

/-- `memCopy` gives no result, so none is poison. -/
theorem memCopy_makesNoPoison : MakesNoPoison (d := CoreDialect) (.memCopy k o w n) := by
  intro _ N _ lay ρ L args _ S rs S' _ h
  cases rs
  exact h

/-- `memCopy` propagates poison with memory: it gives no result, a poison
length is UB only where the length it chose is, and a poison pointer only
where a pointer with no provenance is, from the same memories. -/
theorem memCopy_memPropagates : MemPropagatesPoison (d := CoreDialect) (.memCopy k o w n) where
  poisonOut _ _ _ _ _ _ rs _ _ := by
    cases rs
    trivial
  ubByOwnRules lay ρ L args S r _ hub := by
    match args, hub with
    | .cons d (.cons s (.cons l .nil)), hub =>
      have hub : memCopyRule (m := StateT (Memories _ (unitsOf lay)) SetM) lay ρ k w n d s l S
          (.ub r) := hub
      have hl : ∃ v : BitVec w, (l = .poison ∨ l = .value v) ∧
          copyLenRule (m := StateT (Memories _ (unitsOf lay)) SetM) lay ρ k n v.toNat d s S
            (.ub r) := by
        cases l with
        | value v => exact ⟨v, .inr rfl, hub⟩
        | poison =>
          obtain ⟨v, hv⟩ := (SetM.chooseBind_apply _ S _).1 hub
          exact ⟨v, .inl rfl, hv⟩
      obtain ⟨v, hlv, hc⟩ := hl
      obtain ⟨r', hr'⟩ := copyLenRule_ub_fill k n lay ρ hc
      refine ⟨HVector.cons (f := toType) (a := Ty.ptr n) (.value (fillPtr d) : PoisonOr Pointer)
        (HVector.cons (f := toType) (a := Ty.ptr n) (.value (fillPtr s) : PoisonOr Pointer)
        (HVector.cons (f := toType) (a := Ty.int w) (.value v : PoisonOr (BitVec w)) .nil)),
        ⟨?_, ?_, ?_, ?_, trivial⟩, r', hr'⟩
      · rintro (h | h | h | h) <;> cases h
      · cases d
        · exact .inl rfl
        · exact .inr rfl
      · cases s
        · exact .inl rfl
        · exact .inr rfl
      · exact hlv

/-- `memCopy` gives a result on defined operands from memories inside a
call: a length of 0 does nothing. -/
theorem memCopy_memReturnsOnDefined : MemReturnsOnDefined (d := CoreDialect) (.memCopy k o w n) :=
    fun lay ρ L => by
  refine ⟨HVector.cons (f := toType) (a := Ty.ptr n) (.value ⟨none, 0⟩ : PoisonOr Pointer)
    (HVector.cons (f := toType) (a := Ty.ptr n) (.value ⟨none, 0⟩ : PoisonOr Pointer)
    (HVector.cons (f := toType) (a := Ty.int w) (.value 0#w : PoisonOr (BitVec w)) .nil)),
    ?_, Memories.empty.enter, HVector.nil, Memories.empty.enter, List.cons_ne_nil _ _, ?_⟩
  · rintro (h | h | h | h) <;> cases h
  · show (copyLenRule lay ρ k n (0#w).toNat (.value ⟨none, 0⟩) (.value ⟨none, 0⟩) :
      StateT (Memories _ (unitsOf lay)) SetM _) _ _
    simp only [copyLenRule, BitVec.toNat_zero, ↓reduceIte]
    rfl

end Fir.Core
