import Fir.Core.MemSetLaws
import Fir.Core.MemCopyPoison
import Fir.Core.StoreLaws

/-!
# Fill poison obligations

`memSet` propagates poison, so it carries the poison obligations with
memory, which it meets by its own rule:

* _Poison out._ It gives no result, so a poison operand gives none.
* _UB only by its own rules._ Where it is UB from the memories `S` on a
  poison operand, it is UB from `S` on defined operands that fill each
  poison. A poison length is UB only where the length it chose is, so that
  length fills it. A poison pointer is UB only for a length other than 0,
  and there a pointer with no provenance fills it: a store through it
  faults. A poison value is never UB by itself: a store of its poison
  units faults only where a store of as many units of a defined value
  faults, since whether a store faults depends on how many units it
  writes, not on what they hold, so a zero fills it.
* _A result on defined operands._ A length of 0 gives no result and does
  nothing, from any memories, whatever the pointer and the value are.

It gives no result, so it makes no poison either.
-/

namespace Fir.Core

open Memory

/-- The bits that fill a poison value: zero. -/
def fillBits {v : Nat} : PoisonOr (BitVec v) → BitVec v
  | .value b => b
  | .poison => 0#v

variable (o : Memory.Ordering) (v w n : Nat)

section

variable {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : Mem → N)

local notation "SM" => StateT (Memories N (unitsOf lay)) SetM

/-- Where the rule of a defined length is UB, it is UB on the pointer that
fills a poison pointer and the bits that fill a poison value. -/
theorem setLenRule_ub_fill {len : Nat} {p : PoisonOr Pointer} {x : PoisonOr (BitVec v)}
    {S : Memories N (unitsOf lay)} {r : String}
    (h : setLenRule (m := SM) lay ρ v n len p x S (.ub r)) :
    ∃ r', setLenRule (m := SM) lay ρ v n len (.value (fillPtr p)) (.value (fillBits x)) S
      (.ub r') := by
  unfold setLenRule at h ⊢
  by_cases hlen : len = 0
  · simp only [hlen, ↓reduceIte] at h
    cases h
  · simp only [hlen, ↓reduceIte] at h ⊢
    let us := setUnits (lay (ρ n)) len (.value (fillBits x) : PoisonOr (BitVec v))
    cases p with
    | poison =>
      have hn : S.store (ρ n) ⟨none, 0⟩ us 1 = .error .noProvenance := rfl
      exact ⟨_, (SetM.stateMap_apply _ _ S _).2 (.inr ⟨_, (Fir.store_apply _ _ _ _ S _).2
        (.inr ⟨.noProvenance, hn, rfl⟩), rfl⟩)⟩
    | value q =>
      rcases (SetM.stateMap_apply _ _ S _).1 h with ⟨_, _, _, he⟩ | ⟨r', hs, -⟩
      · cases he
      rcases (Fir.store_apply _ _ _ _ S _).1 hs with ⟨_, _, he'⟩ | ⟨f, hf, -⟩
      · cases he'
      exact ⟨_, (SetM.stateMap_apply _ _ S _).2 (.inr ⟨_, (Fir.store_apply _ _ _ _ S _).2
        (.inr ⟨f, Memory.Memories.store_error_length (unit := unitsOf lay) (x := ρ n)
          (us := setUnits (lay (ρ n)) len x) (us' := us)
          (by simp [us, setUnits]) hf, rfl⟩), rfl⟩)⟩

end

/-- `memSet` gives no result, so none is poison. -/
theorem memSet_makesNoPoison : MakesNoPoison (d := CoreDialect) (.memSet o v w n) := by
  intro _ N _ lay ρ L args _ S rs S' _ h
  cases rs
  exact h

/-- `memSet` propagates poison with memory: it gives no result, a poison
length is UB only where the length it chose is, a poison pointer only
where a pointer with no provenance is, and a poison value only where a
zero is, from the same memories. -/
theorem memSet_memPropagates : MemPropagatesPoison (d := CoreDialect) (.memSet o v w n) where
  poisonOut _ _ _ _ _ _ rs _ _ := by
    cases rs
    trivial
  ubByOwnRules lay ρ L args S r _ hub := by
    match args, hub with
    | .cons p (.cons x (.cons l .nil)), hub =>
      have hub : memSetRule (m := StateT (Memories _ (unitsOf lay)) SetM) lay ρ v w n p x l S
          (.ub r) := hub
      have hl : ∃ b : BitVec w, (l = .poison ∨ l = .value b) ∧
          setLenRule (m := StateT (Memories _ (unitsOf lay)) SetM) lay ρ v n b.toNat p x S
            (.ub r) := by
        cases l with
        | value b => exact ⟨b, .inr rfl, hub⟩
        | poison =>
          obtain ⟨b, hb⟩ := (SetM.chooseBind_apply _ S _).1 hub
          exact ⟨b, .inl rfl, hb⟩
      obtain ⟨b, hlb, hc⟩ := hl
      obtain ⟨r', hr'⟩ := setLenRule_ub_fill v n lay ρ hc
      refine ⟨HVector.cons (f := toType) (a := Ty.ptr n) (.value (fillPtr p) : PoisonOr Pointer)
        (HVector.cons (f := toType) (a := Ty.int v) (.value (fillBits x) : PoisonOr (BitVec v))
        (HVector.cons (f := toType) (a := Ty.int w) (.value b : PoisonOr (BitVec w)) .nil)),
        ⟨?_, ?_, ?_, ?_, trivial⟩, r', hr'⟩
      · rintro (h | h | h | h) <;> cases h
      · cases p
        · exact .inl rfl
        · exact .inr rfl
      · cases x
        · exact .inl rfl
        · exact .inr rfl
      · exact hlb

/-- `memSet` gives a result on defined operands from memories inside a
call: a length of 0 does nothing. -/
theorem memSet_memReturnsOnDefined : MemReturnsOnDefined (d := CoreDialect) (.memSet o v w n) :=
    fun lay ρ L => by
  refine ⟨HVector.cons (f := toType) (a := Ty.ptr n) (.value ⟨none, 0⟩ : PoisonOr Pointer)
    (HVector.cons (f := toType) (a := Ty.int v) (.value 0#v : PoisonOr (BitVec v))
    (HVector.cons (f := toType) (a := Ty.int w) (.value 0#w : PoisonOr (BitVec w)) .nil)),
    ?_, Memories.empty.enter, HVector.nil, Memories.empty.enter, List.cons_ne_nil _ _, ?_⟩
  · rintro (h | h | h | h) <;> cases h
  · show (setLenRule lay ρ v n (0#w).toNat (.value ⟨none, 0⟩) (.value 0#v) :
      StateT (Memories _ (unitsOf lay)) SetM _) _ _
    simp only [setLenRule, BitVec.toNat_zero, ↓reduceIte]
    rfl

end Fir.Core
