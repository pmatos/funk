import FirTest.Equiv

/-!
Pairs 3 and 4 of the equivalence experiment of #282, the pairs with the
flag `nsw`. `FirTest.Equiv` explains the method and lists the results.

A flag makes an op give poison where it overflows, so each proof splits on
whether the op overflows before `bv_decide`, or a proof by hand at every
width, closes what is left. Where an op with `nsw` is the target and an op
without it the source, the target gives poison where the source gives a
value, so that direction fails; the refutations name such an argument, and
`#guard`s run both functions on it with `fir-ref`.
-/

namespace FirTest.Equiv

open Fir Core EquivSteps

/-! # Pair 3: `add nsw %x, %x` and `shl %x, 1`

fir's `shl` has no flags, so the flagged pair keeps `shl` as it is. -/

/-- At `i32`, `shl %x, 1` refines `add nsw %x, %x`: where `add nsw`
overflows it gives poison, which every value refines. -/
theorem addNsw_shl_32 :
    funcRuns (pairs 32) (addNswSelf 32) ⊑ funcRuns (pairs 32) (shlOne 32) := by
  refine (unary_isRefinedBy_iff (addSelfWith_runs _) shlOne_runs).2 fun x => ?_
  cases x with
  | poison => trivial
  | value x =>
    cases h : x.saddOverflow x <;>
      simp [h, addWith, wrapValues, addValues, shlValues, shiftValues,
        HRefinement.IsRefinedBy, PoisonOr.IsRefinedBy]
    bv_decide

/-- At `i32`, `add nsw %x, %x` does not refine `shl %x, 1`: on `2^30`, `shl`
gives `-2^31` and `add nsw` overflows, so gives poison. -/
theorem shl_addNsw_fails_32 :
    ¬ funcRuns (pairs 32) (shlOne 32) ⊑ funcRuns (pairs 32) (addNswSelf 32) := by
  intro h
  exact (unary_isRefinedBy_iff shlOne_runs (addSelfWith_runs _)).1 h (.value 1073741824)

-- `fir-ref` agrees, on `2^30`.
#guard runValid (pairsText 32) "@shl_one" ["1073741824"] == returns ["-2147483648"]
#guard runValid (pairsText 32) "@add_nsw_self" ["1073741824"] == returns ["poison"]

/-- At every width of two bits or more, `shl %x, 1` refines
`add nsw %x, %x`. -/
theorem addNsw_shl (w : Nat) (hw : 2 ≤ w) :
    funcRuns (pairs w) (addNswSelf w) ⊑ funcRuns (pairs w) (shlOne w) := by
  refine (unary_isRefinedBy_iff (addSelfWith_runs _) shlOne_runs).2 fun x => ?_
  cases x with
  | poison => trivial
  | value x =>
    cases h : x.saddOverflow x <;>
      simp [h, addWith, wrapValues, addValues, shlValues, shiftValues,
        HRefinement.IsRefinedBy, PoisonOr.IsRefinedBy, Nat.one_mod_two_pow (n := w) (by omega),
        show 1 < w by omega]
    exact add_self_eq_shl x

/-- At `i1`, `shl %x, 1` does not refine `add nsw %x, %x`: on `false`,
`add nsw` gives `false` and `shl` gives poison. -/
theorem addNsw_shl_fails_1 :
    ¬ funcRuns (pairs 1) (addNswSelf 1) ⊑ funcRuns (pairs 1) (shlOne 1) := by
  intro h
  exact (unary_isRefinedBy_iff (addSelfWith_runs _) shlOne_runs).1 h (.value 0)

#guard runValid (pairsText 1) "@add_nsw_self" ["false"] == returns ["false"]

/-- At `i1`, `add nsw %x, %x` refines `shl %x, 1`: `shl` shifts by the
width there, so gives poison, which every value refines. -/
theorem shl_addNsw_1 : funcRuns (pairs 1) (shlOne 1) ⊑ funcRuns (pairs 1) (addNswSelf 1) := by
  refine (unary_isRefinedBy_iff shlOne_runs (addSelfWith_runs _)).2 fun x => ?_
  cases x <;> trivial

/-! # Pair 4: `mul nsw %x, 2` and `add nsw %x, %x` -/

/-- At `i32`, `add nsw %x, %x` refines `mul nsw %x, 2`. -/
theorem mulNsw_addNsw_32 :
    funcRuns (pairs 32) (mulNswTwo 32) ⊑ funcRuns (pairs 32) (addNswSelf 32) := by
  refine (unary_isRefinedBy_iff (mulTwoWith_runs _) (addSelfWith_runs _)).2 fun x => ?_
  cases x with
  | poison => trivial
  | value x =>
    cases h₁ : x.saddOverflow x <;> cases h₂ : x.smulOverflow 2#32 <;>
      simp [h₁, h₂, mulWith, addWith, wrapValues, mulValues, addValues,
        HRefinement.IsRefinedBy, PoisonOr.IsRefinedBy] <;>
      bv_decide

/-- At `i32`, `mul nsw %x, 2` refines `add nsw %x, %x`. -/
theorem addNsw_mulNsw_32 :
    funcRuns (pairs 32) (addNswSelf 32) ⊑ funcRuns (pairs 32) (mulNswTwo 32) := by
  refine (unary_isRefinedBy_iff (addSelfWith_runs _) (mulTwoWith_runs _)).2 fun x => ?_
  cases x with
  | poison => trivial
  | value x =>
    cases h₁ : x.saddOverflow x <;> cases h₂ : x.smulOverflow 2#32 <;>
      simp [h₁, h₂, mulWith, addWith, wrapValues, mulValues, addValues,
        HRefinement.IsRefinedBy, PoisonOr.IsRefinedBy] <;>
      bv_decide

/-! # Pair 3 at every width, and pair 4 at small widths -/

/-- `2^k`, at `i(k+2)`, overflows as a signed integer when doubled. -/
theorem pow_saddOverflow (k : Nat) :
    (BitVec.ofNat (k + 2) (2 ^ k)).saddOverflow (BitVec.ofNat (k + 2) (2 ^ k)) = true := by
  have hp : 0 < 2 ^ k := Nat.pow_pos (by decide)
  have h4 : 2 ^ (k + 2) = 2 ^ k * 4 := by rw [Nat.pow_add]
  have hn : (BitVec.ofNat (k + 2) (2 ^ k)).toNat = 2 ^ k := by
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hi : (BitVec.ofNat (k + 2) (2 ^ k)).toInt = 2 ^ k := by
    rw [BitVec.toInt_eq_toNat_cond, hn]
    simp only [h4]
    split <;> push_cast <;> omega
  have hk : k + 2 - 1 = k + 1 := rfl
  have h2 : (2 : Int) ^ (k + 1) = 2 ^ k * 2 := Int.pow_succ 2 k
  simp only [BitVec.saddOverflow, hi, hk, h2, Bool.or_eq_true, decide_eq_true_eq]
  omega

/-- At every width of two bits or more, `add nsw %x, %x` does not refine
`shl %x, 1`: on `2^(N-2)`, `shl` gives a value and `add nsw` overflows. -/
theorem shl_addNsw_fails (k : Nat) :
    ¬ funcRuns (pairs (k + 2)) (shlOne (k + 2)) ⊑ funcRuns (pairs (k + 2)) (addNswSelf (k + 2)) := by
  intro h
  have h1 := (unary_isRefinedBy_iff shlOne_runs (addSelfWith_runs _)).1 h
    (.value (BitVec.ofNat (k + 2) (2 ^ k)))
  simp [shlValues, shiftValues, addWith, wrapValues, pow_saddOverflow,
    HRefinement.IsRefinedBy, PoisonOr.IsRefinedBy, Nat.one_mod_two_pow (n := k + 2) (by omega)] at h1

/-- `2`, read as signed, at a width of three bits or more. -/
theorem two_toInt {w : Nat} (hw : 3 ≤ w) : (2#w).toInt = 2 := by
  have h8 : 2 ^ 3 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
  have h2 : (2#w).toNat = 2 := by
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toInt_eq_toNat_cond, h2]
  simp only [Nat.reducePow] at h8
  split <;> omega

/-- At three bits or more, `x * 2` overflows as a signed integer exactly
when `x + x` does. -/
theorem saddOverflow_eq_smulOverflow {w : Nat} (hw : 3 ≤ w) (x : BitVec w) :
    x.saddOverflow x = x.smulOverflow 2#w := by
  have h : x.toInt * 2 = x.toInt + x.toInt := by omega
  simp [BitVec.saddOverflow, BitVec.smulOverflow, two_toInt hw, h]

/-- At every width of three bits or more, `add nsw %x, %x` refines
`mul nsw %x, 2`. -/
theorem mulNsw_addNsw (w : Nat) (hw : 3 ≤ w) :
    funcRuns (pairs w) (mulNswTwo w) ⊑ funcRuns (pairs w) (addNswSelf w) := by
  refine (unary_isRefinedBy_iff (mulTwoWith_runs _) (addSelfWith_runs _)).2 fun x => ?_
  cases x with
  | poison => trivial
  | value x =>
    cases h : x.saddOverflow x <;>
      simp [← saddOverflow_eq_smulOverflow hw, h, mulWith, addWith, wrapValues, mulValues,
        addValues, HRefinement.IsRefinedBy, PoisonOr.IsRefinedBy]
    exact BitVec.mul_two (x := x)

/-- At every width of three bits or more, `mul nsw %x, 2` refines
`add nsw %x, %x`. -/
theorem addNsw_mulNsw (w : Nat) (hw : 3 ≤ w) :
    funcRuns (pairs w) (addNswSelf w) ⊑ funcRuns (pairs w) (mulNswTwo w) := by
  refine (unary_isRefinedBy_iff (addSelfWith_runs _) (mulTwoWith_runs _)).2 fun x => ?_
  cases x with
  | poison => trivial
  | value x =>
    cases h : x.saddOverflow x <;>
      simp [← saddOverflow_eq_smulOverflow hw, h, mulWith, addWith, wrapValues, mulValues,
        addValues, HRefinement.IsRefinedBy, PoisonOr.IsRefinedBy]
    exact (BitVec.mul_two (x := x)).symm

/-- At `i2`, `add nsw %x, %x` does not refine `mul nsw %x, 2`: `2` is `-2`
there, so on `1`, `mul nsw` gives `-2` and `add nsw` overflows. -/
theorem mulNsw_addNsw_fails_2 :
    ¬ funcRuns (pairs 2) (mulNswTwo 2) ⊑ funcRuns (pairs 2) (addNswSelf 2) := by
  intro h
  exact (unary_isRefinedBy_iff (mulTwoWith_runs _) (addSelfWith_runs _)).1 h (.value 1)

/-- At `i2`, `mul nsw %x, 2` does not refine `add nsw %x, %x`: on `-1`,
`add nsw` gives `-2` and `mul nsw` overflows, since `-1 * -2` is `2`. -/
theorem addNsw_mulNsw_fails_2 :
    ¬ funcRuns (pairs 2) (addNswSelf 2) ⊑ funcRuns (pairs 2) (mulNswTwo 2) := by
  intro h
  exact (unary_isRefinedBy_iff (addSelfWith_runs _) (mulTwoWith_runs _)).1 h (.value 3)

#guard runValid (pairsText 2) "@mul_nsw_two" ["1"] == returns ["-2"]
#guard runValid (pairsText 2) "@add_nsw_self" ["1"] == returns ["poison"]
#guard runValid (pairsText 2) "@add_nsw_self" ["-1"] == returns ["-2"]
#guard runValid (pairsText 2) "@mul_nsw_two" ["-1"] == returns ["poison"]

/-- At `i1`, `add nsw %x, %x` does not refine `mul nsw %x, 2`: `2` is `0`
there, so on `true`, `mul nsw` gives `false` and `add nsw` overflows. -/
theorem mulNsw_addNsw_fails_1 :
    ¬ funcRuns (pairs 1) (mulNswTwo 1) ⊑ funcRuns (pairs 1) (addNswSelf 1) := by
  intro h
  exact (unary_isRefinedBy_iff (mulTwoWith_runs _) (addSelfWith_runs _)).1 h (.value 1)

/-- At `i1`, `mul nsw %x, 2` refines `add nsw %x, %x`: on `true`, `add nsw`
gives poison. -/
theorem addNsw_mulNsw_1 :
    funcRuns (pairs 1) (addNswSelf 1) ⊑ funcRuns (pairs 1) (mulNswTwo 1) := by
  refine (unary_isRefinedBy_iff (addSelfWith_runs _) (mulTwoWith_runs _)).2 fun x => ?_
  cases x with
  | poison => trivial
  | value x =>
    cases h₁ : x.saddOverflow x <;>
      simp [h₁, mulWith, addWith, wrapValues, mulValues, addValues,
        HRefinement.IsRefinedBy, PoisonOr.IsRefinedBy] <;>
      bv_decide

#guard runValid (pairsText 1) "@mul_nsw_two" ["true"] == returns ["false"]
#guard runValid (pairsText 1) "@add_nsw_self" ["true"] == returns ["poison"]

/-! # With memory

As in `FirTest.Equiv`, each result holds of the runs with memory, at every
naming of the core's memories. -/

/-- Pair 3 at `i32`, the direction that holds, for the runs with memory. -/
theorem addNsw_shl_32_mem {N : Type} [DecidableEq N] (unit : N → Nat)
    (ρ : DialectEffects.Mem CoreDialect → N) :
    (addNswSelf 32).memRuns unit ρ (pairs 32) ⊑ (shlOne 32).memRuns unit ρ (pairs 32) := by
  rw [Func.memRuns_eq, Func.memRuns_eq]
  exact addNsw_shl_32

/-- Pair 4 at `i32`, both ways, for the runs with memory. -/
theorem mulNsw_addNsw_32_mem {N : Type} [DecidableEq N] (unit : N → Nat)
    (ρ : DialectEffects.Mem CoreDialect → N) :
    (mulNswTwo 32).memRuns unit ρ (pairs 32) ⊑ (addNswSelf 32).memRuns unit ρ (pairs 32) ∧
      (addNswSelf 32).memRuns unit ρ (pairs 32) ⊑ (mulNswTwo 32).memRuns unit ρ (pairs 32) := by
  rw [Func.memRuns_eq, Func.memRuns_eq]
  exact ⟨mulNsw_addNsw_32, addNsw_mulNsw_32⟩

end FirTest.Equiv
