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

The interpreter is stuck when a terminator's exit says `goto i` and the
terminator has no successor `i` (`Func.jump`). Validation fixes how many
successors a terminator has, its `succCount`, and no obligation of the
poison classes section says which `goto` it may give. So the no-stuck
obligation of a valid function with branches needs one more fact of each
op: every `goto i` that its exit may give has `i` below its successor
count. `br_goto_lt` and `condBr_goto_lt` prove it of `br`, which goes only
to successor `0` of its one, and of `cond_br`, which goes only to
successor `0` or `1` of its two.
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
