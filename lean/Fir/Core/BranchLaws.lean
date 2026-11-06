import Fir.Core.Semantics
import Fir.Core.Poison

/-!
# Branches are lawful

`br` and `cond_br` are exceptions to poison propagation
(ADR-2026-10-30-0818), so of the obligations of the poison classes section
they meet two: they are total and monotone. Both look at the op's exit.

* _Totality._ `br` goes to its successor on every operand vector. `cond_br`
  goes to one of its two successors on a condition that is not poison, and
  is UB on poison, so it has an outcome on every condition too.
* _Monotonicity._ Where a terminator goes refines only by being the same.
  A poison condition makes `cond_br` UB, which allows anything. A defined
  condition is refined only by itself, so on a condition that refines
  another, `cond_br` goes where it went before. `br` has no operands and
  always goes to the same place.

The values that a successor passes are not operands of the op: the
interpreter passes them on to the block's arguments as they are, poison
included. So neither op has a rule for poison values beyond `cond_br`'s
condition.

# Each branch names a successor it has

A run is stuck when a terminator's exit says to go to its successor _i_
and the terminator has no successor _i_. Validation fixes how many
successors a terminator has, and no obligation of the poison classes
section says which successors its exit may name. So the no-stuck
obligation of a valid function with branches needs one more fact of each
op: every successor that its exit may name is one it has. Below, `br`
goes only to its one successor, and `cond_br` only to one of its two.
The proofs that every valid core function without a `call` op runs within
itself, and that every function of a valid core module runs within the
module, rest on these two facts.
-/

namespace Fir.Core

/-- In the set monad, `exitOfEv e` ends exactly as `e` says. -/
theorem exitOfEv_iff (e e' : Ev Exit) : exitOfEv (m := SetM) e e' ↔ e' = e := by
  cases e <;> exact Iff.rfl

/-- In the set monad, `br` goes to its one successor, and nowhere else. -/
theorem br_exit (args : HVector toType (Fir.sig (d := CoreDialect) .br)) (e : Ev Exit) :
    DialectDenote.exit (m := SetM) (d := CoreDialect) .br args e ↔ e = .ok (.goto 0) :=
  Iff.rfl

/-- In the set monad, `cond_br` on the condition `c` ends exactly as
`condBrExit c` says. -/
theorem condBr_exit (c : PoisonOr (BitVec 1)) (e : Ev Exit) :
    DialectDenote.exit (m := SetM) (d := CoreDialect) .condBr (.cons c .nil) e ↔
      e = condBrExit c :=
  exitOfEv_iff _ _

/-! # `br` -/

/-- `br` has an exit on every operand vector. -/
theorem br_total : OpTotal (d := CoreDialect) .br :=
  fun args => ⟨(fun h => nomatch h), fun _ => ⟨_, (br_exit args _).2 rfl⟩⟩

/-- `br` is monotone: on any operands, it goes to its one successor. -/
theorem br_monotone : OpMonotone (d := CoreDialect) .br :=
  fun _ _ _ => ⟨(fun h => nomatch h), fun _ e he => by cases he; exact ⟨_, rfl, rfl⟩⟩

/-- Every `goto i` that `br`'s exit may give names a successor it has. -/
theorem br_goto_lt (args : HVector toType (Fir.sig (d := CoreDialect) .br)) {i : Nat}
    (h : DialectDenote.exit (m := SetM) (d := CoreDialect) .br args (.ok (.goto i))) :
    i < succCount (d := CoreDialect) .br := by
  cases (br_exit args _).1 h
  decide

/-! # `cond_br` -/

/-- `cond_br` has an exit on every operand vector: a successor, or UB on a
poison condition. -/
theorem condBr_total : OpTotal (d := CoreDialect) .condBr := fun
  | .cons c .nil => ⟨(fun h => nomatch h), fun _ => ⟨_, (condBr_exit c _).2 rfl⟩⟩

/-- `cond_br` is monotone: on a condition that refines another, it goes
where it went on that other, or that other was poison, which is UB. -/
theorem condBr_monotone : OpMonotone (d := CoreDialect) .condBr := by
  intro args args' h
  refine ⟨(fun h => nomatch h), fun _ => ?_⟩
  match args, args', h with
  | .cons c .nil, .cons c' .nil, ⟨hc, _⟩ =>
    cases c with
    | poison => exact fun _ _ => ⟨_, (condBr_exit _ _).2 rfl, trivial⟩
    | value x =>
      cases c' with
      | poison => exact hc.elim
      | value x' =>
        have hx : x = x' := hc
        subst hx
        exact SetM.isRefinedBy_refl (fun _ => rfl) _

/-- Every `goto i` that `cond_br`'s exit may give names a successor it
has. -/
theorem condBr_goto_lt (args : HVector toType (Fir.sig (d := CoreDialect) .condBr)) {i : Nat}
    (h : DialectDenote.exit (m := SetM) (d := CoreDialect) .condBr args (.ok (.goto i))) :
    i < succCount (d := CoreDialect) .condBr := by
  match args, h with
  | .cons c .nil, h =>
    have h' := (condBr_exit c _).1 h
    show i < 2
    cases c with
    | poison => cases h'
    | value x =>
      simp only [condBrExit] at h'
      split at h' <;> cases h' <;> decide

end Fir.Core
