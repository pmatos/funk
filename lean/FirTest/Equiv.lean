import FirTest.EquivFuncs
import Std.Tactic.BVDecide

/-!
# Are two fir functions equivalent? An experiment in Lean (#282)

Before a tool that asks whether two fir functions mean the same thing is
built, the human asked for an experiment (#282, ruling Q4): prove a few
small pairs equivalent in Lean, against the semantics in `lean/Fir`, and
report what it took before an automatic tactic such as `bv_decide` could
finish each proof. This file and `FirTest.EquivNsw` hold the results;
`FirTest.EquivFuncs` holds the functions and `FirTest.EquivSteps` the
reusable lemmas.

## What is proved

"Equivalent" means refinement both ways (`Behaviour.IsRefinedBy`,
ADR-2026-10-29-2008): the target refines the source when every way the
target can end is allowed by some way the source can end, on every
argument, poison included. A poison result is refined by any value; a value
only by itself. Each direction is its own theorem. A direction that fails
is refuted: a theorem says it does not hold, by a concrete argument, and a
`#guard` runs both functions on that argument with `fir-ref`. Below, "A to
B" names the direction that replaces A with B: B refines A.

The pairs, each a function `@f(%x: iN) -> iN`:

* pair 1: `add %x, %x` and `shl %x, 1`;
* pair 2: `mul %x, 2` and `add %x, %x`;
* pair 3: `add nsw %x, %x` and `shl %x, 1` (fir's `shl` has no flags);
* pair 4: `mul nsw %x, 2` and `add nsw %x, %x`.

## The method, in plain words

1. _Write the functions down._ Each is a value of `Func CoreDialect`, the
   abstract syntax the interpreter runs. Printed, they are a module that
   `fir-ref` validates and runs (`pairsText`).
2. _Run each function on paper._ The interpreter does not give a value: it
   gives a set of the ways a run may end, at each fuel budget. Four lemmas,
   proved once for every dialect, take one step of a run each: enter the
   function, run one op, run `ret`, look up an operand. Chained, they show
   that each function returns one value after two or three steps
   (`addSelfWith_runs` and its siblings). A single `simp` over the
   interpreter did not work: it cannot rewrite inside the types that depend
   on an op's signature, so the steps are taken one lemma at a time.
3. _One budget is enough._ Every function's runs are fuel-monotone, so a
   run that returns at one budget has that return as its whole observable
   behaviour (`observable_of_runs`). Then the target refines the source
   exactly when, on every argument, the target's value refines the
   source's (`FuncRuns.isRefinedBy_iff_of_returns`, and
   `unary_isRefinedBy_iff` for these functions). That is an "if and only
   if", so it proves a direction and refutes one alike.
4. _Split poison away._ `bv_decide` decides statements about bitvectors
   only; it cannot see through poison. So the proof takes a poison
   argument apart from a value, unfolds the rules of the ops (`addWith`,
   `mulWith`, `wrapValues`, `shlValues`, `shiftValues`), and for an op with
   `nsw` splits on whether it overflows. What is left is a plain bitvector
   equation, such as `x + x = x <<< 1`.
5. _Close it._ At `i32`, `bv_decide` closes every such equation. At every
   width it cannot, since it needs a fixed width, so a short proof does it
   instead: read the bitvectors as numbers (`toNat`, `toInt`) and let
   `omega` do the arithmetic, or use Lean's lemma `BitVec.mul_two`.

## Results

At `i32` (each proof takes under 0.1 s; each run lemma about 0.15 s):

* pair 1: proved both ways (`add_shl_32`, `shl_add_32`);
* pair 2: proved both ways (`mul_add_32`, `add_mul_32`);
* pair 3: `add nsw %x, %x` to `shl %x, 1` proved (`addNsw_shl_32`); the
  other way refuted on `2^30`, where `shl` gives `-2^31` and `add nsw`
  overflows to poison (`shl_addNsw_fails_32`);
* pair 4: proved both ways (`mulNsw_addNsw_32`, `addNsw_mulNsw_32`).

At every width; some statements need a width condition:

* pair 1: `add` to `shl` holds from `i2` up (`add_shl`) and fails at `i1`,
  where a shift by 1 is a shift by the width, so poison
  (`add_shl_fails_1`); `shl` to `add` holds at every width (`shl_add`);
* pair 2: both ways at every width (`mul_add`, `add_mul`);
* pair 3: `add nsw` to `shl` holds from `i2` up (`addNsw_shl`), fails at
  `i1` (`addNsw_shl_fails_1`); the other way fails at every width from
  `i2` up, on `2^(N-2)` (`shl_addNsw_fails`), and holds at `i1`, where
  `shl` gives poison (`shl_addNsw_1`);
* pair 4: both ways from `i3` up (`mulNsw_addNsw`, `addNsw_mulNsw`). At
  `i2` the constant `2` is `-2`, and both ways fail
  (`mulNsw_addNsw_fails_2`, `addNsw_mulNsw_fails_2`). At `i1` it is `0`:
  `add nsw` to `mul nsw` holds (`addNsw_mulNsw_1`), the other way fails
  (`mulNsw_addNsw_fails_1`).

The runs compared are the runs with memory of #231, at the module's layout
(`Core.funcRuns`). Each result holds at every layout and naming of the
core's memories too (`add_shl_32_mem` and its siblings).

What the proofs trust: Lean's standard axioms, and for pair 4 at `i32`
alone one axiom of native evaluation, where `bv_decide` ran its SAT
solver (ADR-2026-10-30-1452). For pairs 1 to 3, `bv_decide`'s own
rewriting closed the equation before any SAT call, so nothing native is
trusted.
-/

namespace FirTest.Equiv

open Fir Core EquivSteps

/- Each proof below unfolds the rules of the ops and of `PoisonOr`
refinement, so `simp` does so by default in this file. -/
attribute [local simp] addWith mulWith wrapValues addValues mulValues shlValues shiftValues
  HRefinement.IsRefinedBy PoisonOr.IsRefinedBy

/-! # Pair 1: `add %x, %x` and `shl %x, 1` -/

/-- At `i32`, `shl %x, 1` refines `add %x, %x`. -/
theorem add_shl_32 : funcRuns (pairs 32) (addSelf 32) ⊑ funcRuns (pairs 32) (shlOne 32) := by
  refine (unary_isRefinedBy_iff _ _ (addSelfWith_runs _ _ _) (shlOne_runs _ _)).2 fun x => ?_
  cases x with
  | poison => trivial
  | value x =>
    simp
    bv_decide

/-- At `i32`, `add %x, %x` refines `shl %x, 1`. -/
theorem shl_add_32 : funcRuns (pairs 32) (shlOne 32) ⊑ funcRuns (pairs 32) (addSelf 32) := by
  refine (unary_isRefinedBy_iff _ _ (shlOne_runs _ _) (addSelfWith_runs _ _ _)).2 fun x => ?_
  cases x with
  | poison => trivial
  | value x =>
    simp
    bv_decide

/-- Doubling is a shift by one, at every width. -/
theorem add_self_eq_shl {w : Nat} (x : BitVec w) : x + x = x <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_two]

/-- At every width of two bits or more, `shl %x, 1` refines `add %x, %x`. -/
theorem add_shl (w : Nat) (hw : 2 ≤ w) :
    funcRuns (pairs w) (addSelf w) ⊑ funcRuns (pairs w) (shlOne w) := by
  refine (unary_isRefinedBy_iff _ _ (addSelfWith_runs _ _ _) (shlOne_runs _ _)).2 fun x => ?_
  cases x with
  | poison => trivial
  | value x =>
    simp [Nat.one_mod_two_pow (n := w) (by omega), show 1 < w by omega]
    exact add_self_eq_shl x

/-- At every width, `add %x, %x` refines `shl %x, 1`: at `i1` the shift is
by the width, so `shl` gives poison, which every value refines. -/
theorem shl_add (w : Nat) : funcRuns (pairs w) (shlOne w) ⊑ funcRuns (pairs w) (addSelf w) := by
  refine (unary_isRefinedBy_iff _ _ (shlOne_runs _ _) (addSelfWith_runs _ _ _)).2 fun x => ?_
  cases x with
  | poison => trivial
  | value x =>
    simp only [addWith, wrapValues, addValues, shlValues, shiftValues]
    split
    · rename_i h
      have hw : 0 < w := Nat.pos_of_ne_zero fun h0 => by subst h0; simp at h
      simp [Nat.one_mod_two_pow hw]
      exact (add_self_eq_shl x).symm
    · trivial

/-- At `i1`, `shl %x, 1` does not refine `add %x, %x`: on `false`, `add`
gives `false` and `shl` gives poison, since it shifts by the width. -/
theorem add_shl_fails_1 : ¬ funcRuns (pairs 1) (addSelf 1) ⊑ funcRuns (pairs 1) (shlOne 1) := by
  intro h
  exact (unary_isRefinedBy_iff _ _ (addSelfWith_runs _ _ _) (shlOne_runs _ _)).1 h (.value 0)

-- `fir-ref` runs the module's text and agrees: at `i1`, on `false`.
#guard runValid (pairsText 1) "@add_self" ["false"] == returns ["false"]
#guard runValid (pairsText 1) "@shl_one" ["false"] == returns ["poison"]

/-! # Pair 2: `mul %x, 2` and `add %x, %x` -/

/-- At `i32`, `add %x, %x` refines `mul %x, 2`. -/
theorem mul_add_32 : funcRuns (pairs 32) (mulTwo 32) ⊑ funcRuns (pairs 32) (addSelf 32) := by
  refine (unary_isRefinedBy_iff _ _ (mulTwoWith_runs _ _ _) (addSelfWith_runs _ _ _)).2 fun x => ?_
  cases x with
  | poison => trivial
  | value x =>
    simp
    bv_decide

/-- At `i32`, `mul %x, 2` refines `add %x, %x`. -/
theorem add_mul_32 : funcRuns (pairs 32) (addSelf 32) ⊑ funcRuns (pairs 32) (mulTwo 32) := by
  refine (unary_isRefinedBy_iff _ _ (addSelfWith_runs _ _ _) (mulTwoWith_runs _ _ _)).2 fun x => ?_
  cases x with
  | poison => trivial
  | value x =>
    simp
    bv_decide

/-- At every width, `add %x, %x` refines `mul %x, 2`. -/
theorem mul_add (w : Nat) : funcRuns (pairs w) (mulTwo w) ⊑ funcRuns (pairs w) (addSelf w) := by
  refine (unary_isRefinedBy_iff _ _ (mulTwoWith_runs _ _ _) (addSelfWith_runs _ _ _)).2 fun x => ?_
  cases x with
  | poison => trivial
  | value x => exact BitVec.mul_two (x := x)

/-- At every width, `mul %x, 2` refines `add %x, %x`. -/
theorem add_mul (w : Nat) : funcRuns (pairs w) (addSelf w) ⊑ funcRuns (pairs w) (mulTwo w) := by
  refine (unary_isRefinedBy_iff _ _ (addSelfWith_runs _ _ _) (mulTwoWith_runs _ _ _)).2 fun x => ?_
  cases x with
  | poison => trivial
  | value x => exact (BitVec.mul_two (x := x)).symm

/-! # At every layout and naming

The runs above are the runs with memory at the module's layout. Each
function returns the same value at every layout and naming of the core's
memories, so each result above holds there too: the value-level fact that a
result proves carries it to any other layout and naming. Pairs 1 and 2 at
`i32`, both ways; `FirTest.EquivNsw` does pairs 3 and 4. -/

/-- Pair 1 at `i32`, both ways, for the runs with memory at every layout
and naming. -/
theorem add_shl_32_mem {N : Type} [DecidableEq N] (lay : N → MemLayout)
    (ρ : DialectEffects.Mem CoreDialect → N) :
    (addSelf 32).memRuns lay ρ (pairs 32) ⊑ (shlOne 32).memRuns lay ρ (pairs 32) ∧
      (shlOne 32).memRuns lay ρ (pairs 32) ⊑ (addSelf 32).memRuns lay ρ (pairs 32) :=
  ⟨(unary_isRefinedBy_iff lay ρ (addSelfWith_runs _ _ _) (shlOne_runs _ _)).2
      ((unary_isRefinedBy_iff _ _ (addSelfWith_runs _ _ _) (shlOne_runs _ _)).1 add_shl_32),
    (unary_isRefinedBy_iff lay ρ (shlOne_runs _ _) (addSelfWith_runs _ _ _)).2
      ((unary_isRefinedBy_iff _ _ (shlOne_runs _ _) (addSelfWith_runs _ _ _)).1 shl_add_32)⟩

/-- Pair 2 at `i32`, both ways, for the runs with memory at every layout
and naming. -/
theorem mul_add_32_mem {N : Type} [DecidableEq N] (lay : N → MemLayout)
    (ρ : DialectEffects.Mem CoreDialect → N) :
    (mulTwo 32).memRuns lay ρ (pairs 32) ⊑ (addSelf 32).memRuns lay ρ (pairs 32) ∧
      (addSelf 32).memRuns lay ρ (pairs 32) ⊑ (mulTwo 32).memRuns lay ρ (pairs 32) :=
  ⟨(unary_isRefinedBy_iff lay ρ (mulTwoWith_runs _ _ _) (addSelfWith_runs _ _ _)).2
      ((unary_isRefinedBy_iff _ _ (mulTwoWith_runs _ _ _) (addSelfWith_runs _ _ _)).1 mul_add_32),
    (unary_isRefinedBy_iff lay ρ (addSelfWith_runs _ _ _) (mulTwoWith_runs _ _ _)).2
      ((unary_isRefinedBy_iff _ _ (addSelfWith_runs _ _ _) (mulTwoWith_runs _ _ _)).1 add_mul_32)⟩

end FirTest.Equiv
