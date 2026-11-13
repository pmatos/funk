import FirTest.EquivSteps
import FirTest.Calls

/-!
The functions of the equivalence experiment of #282, and their runs.

Each function takes one `iN` argument `%x` and returns one `iN`:

* `@add_self` returns `add %x, %x`;
* `@shl_one` returns `shl %x, 1`;
* `@mul_two` returns `mul %x, 2`;
* `@add_nsw_self` returns `add nsw %x, %x`;
* `@mul_nsw_two` returns `mul nsw %x, 2`.

`pairs w` is the module of all five at `iN` with `N = w`. Its printed text is
what `fir-ref` validates and runs in `FirTest.Equiv` and `FirTest.EquivNsw`.

Each run lemma below gives a function's run with memory at one budget, on
any argument, in any module, at every layout and naming of the core's
memories: it calls no function and touches no memory, so neither the module
nor the memories matter. The
proof names the function's ops one by one, with the lemmas of
`FirTest.EquivSteps`; each side condition, such as the lookup of an
operand, holds by `rfl`. `add` and `mul` take their flags as a parameter, so
one proof serves each op with and without `nsw`.

`unary_isRefinedBy_iff` puts the pieces together: one such function refines
another with memory exactly when the value it returns refines the other's,
on every argument value, poison included. The runs of a core function are
its runs with memory at its module's layout (`Core.funcRuns`), so it speaks
of them.
-/

namespace FirTest.Equiv

open Fir Core EquivSteps

/-- A function `@name(%x: iN) -> iN`, with `N = w`, of one block, whose ops
are `ops`. -/
abbrev unary (name : Name) (w : Nat) (ops : List (Operation CoreDialect)) : Func CoreDialect where
  name := name
  params := [("x", i w)]
  results := [i w]
  body := ⟨none, [⟨"entry", [], ops⟩]⟩

/-- `add %x, %x`, with the flags `f`, as `@name`. -/
abbrev addSelfWith (name : Name) (f : WrapFlags) (w : Nat) : Func CoreDialect := unary name w [
  op [("y", i w)] (.add w f) ["x", "x"],
  op [] (.ret [i w]) ["y"]]

/-- `mul %x, 2`, with the flags `f`, as `@name`. -/
abbrev mulTwoWith (name : Name) (f : WrapFlags) (w : Nat) : Func CoreDialect := unary name w [
  op [("two", i w)] (.const w 2) [],
  op [("y", i w)] (.mul w f) ["x", "two"],
  op [] (.ret [i w]) ["y"]]

/-- `@add_self`: `add %x, %x`. -/
abbrev addSelf (w : Nat) : Func CoreDialect := addSelfWith "add_self" {} w

/-- `@add_nsw_self`: `add nsw %x, %x`. -/
abbrev addNswSelf (w : Nat) : Func CoreDialect := addSelfWith "add_nsw_self" { nsw := true } w

/-- `@mul_two`: `mul %x, 2`. -/
abbrev mulTwo (w : Nat) : Func CoreDialect := mulTwoWith "mul_two" {} w

/-- `@mul_nsw_two`: `mul nsw %x, 2`. -/
abbrev mulNswTwo (w : Nat) : Func CoreDialect := mulTwoWith "mul_nsw_two" { nsw := true } w

/-- `@shl_one`: `shl %x, 1`. fir's `shl` has no flags. -/
abbrev shlOne (w : Nat) : Func CoreDialect := unary "shl_one" w [
  op [("one", i w)] (.const w 1) [],
  op [("y", i w)] (.shl w) ["x", "one"],
  op [] (.ret [i w]) ["y"]]

/-- The module of the five functions at `iN`, with `N = w`. -/
def pairs (w : Nat) : Module CoreDialect :=
  ⟨[], [], [addSelf w, shlOne w, mulTwo w, addNswSelf w, mulNswTwo w].map .func, [(0, .unknown)]⟩

/-- The module's text, as `fir-ref` reads it. -/
def pairsText (w : Nat) : String := (pairs w).print

/-! # The run of each function -/

variable {M : Module CoreDialect} {w : Nat} {name : Name} {N : Type} [DecidableEq N]
  (lay : N → MemLayout) (ρ : DialectEffects.Mem CoreDialect → N)

/-- `add %x, %x`, with any flags, returns after two steps, with memory. -/
theorem addSelfWith_runs (f : WrapFlags) (x : ⟦i w⟧) :
    (addSelfWith name f w).memRuns lay ρ M (.cons x .nil) 2 =
      (pure (.ret [⟨i w, addWith f x x⟩]) : ExceptT Stuck SetM (Result Core.Obs)) := by
  letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ
  refine memRuns_of_ret lay ρ (f := addSelfWith name f w) (args := .cons x .nil)
    (Func.enter_ok rfl rfl (HVector.toDVals_types _)) ⟨0, ?_⟩
  rw [runOps_denote (args := .cons x (.cons x .nil)) (rs := .cons (addWith f x x) .nil)
    rfl (operands_cons rfl (operands_cons rfl rfl)) rfl rfl rfl rfl,
    runOps_ret (args := .cons (addWith f x x) .nil) rfl (operands_cons rfl rfl) rfl rfl rfl]
  rfl

/-- `mul %x, 2`, with any flags, returns after three steps, with memory. -/
theorem mulTwoWith_runs (f : WrapFlags) (x : ⟦i w⟧) :
    (mulTwoWith name f w).memRuns lay ρ M (.cons x .nil) 3 =
      (pure (.ret [⟨i w, mulWith f x (.value 2)⟩]) : ExceptT Stuck SetM (Result Core.Obs)) := by
  letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ
  refine memRuns_of_ret lay ρ (f := mulTwoWith name f w) (args := .cons x .nil)
    (Func.enter_ok rfl rfl (HVector.toDVals_types _)) ⟨0, ?_⟩
  rw [runOps_denote (args := .nil) (rs := .cons (constValue w 2) .nil) rfl rfl rfl rfl rfl rfl,
    runOps_denote (args := .cons x (.cons (PoisonOr.value 2) .nil))
      (rs := .cons (mulWith f x (.value 2)) .nil)
      rfl (operands_cons rfl (operands_cons rfl rfl)) rfl rfl rfl rfl,
    runOps_ret (args := .cons (mulWith f x (.value 2)) .nil) rfl (operands_cons rfl rfl) rfl rfl rfl]
  rfl

/-- `@shl_one` returns `shl %x, 1` after three steps, with memory. -/
theorem shlOne_runs (x : ⟦i w⟧) :
    (shlOne w).memRuns lay ρ M (.cons x .nil) 3 =
      (pure (.ret [⟨i w, shlValues x (.value 1)⟩]) : ExceptT Stuck SetM (Result Core.Obs)) := by
  letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ
  refine memRuns_of_ret lay ρ (f := shlOne w) (args := .cons x .nil)
    (Func.enter_ok rfl rfl (HVector.toDVals_types _)) ⟨0, ?_⟩
  rw [runOps_denote (args := .nil) (rs := .cons (constValue w 1) .nil) rfl rfl rfl rfl rfl rfl,
    runOps_denote (args := .cons x (.cons (PoisonOr.value 1) .nil))
      (rs := .cons (shlValues x (.value 1)) .nil)
      rfl (operands_cons rfl (operands_cons rfl rfl)) rfl rfl rfl rfl,
    runOps_ret (args := .cons (shlValues x (.value 1)) .nil) rfl (operands_cons rfl rfl) rfl rfl rfl]
  rfl

/-! # Refinement of two such functions -/

/-- Two functions `@f(%x: iN) -> iN` that each return one value at a fixed
budget with memory, `vf x` and `vg x`: the second refines the first, with
memory, exactly when `vf x ⊑ vg x` for every argument value `x`, poison
included. -/
theorem unary_isRefinedBy_iff {M M' : Module CoreDialect} {n n' : Name}
    {os os' : List (Operation CoreDialect)} {Nf Ng : Nat}
    {vf vg : PoisonOr (BitVec w) → PoisonOr (BitVec w)}
    (hf : ∀ x, (unary n w os).memRuns lay ρ M (.cons x .nil) Nf =
      (pure (.ret [⟨i w, vf x⟩]) : ExceptT Stuck SetM (Result Core.Obs)))
    (hg : ∀ x, (unary n' w os').memRuns lay ρ M' (.cons x .nil) Ng =
      (pure (.ret [⟨i w, vg x⟩]) : ExceptT Stuck SetM (Result Core.Obs))) :
    (unary n w os).memRuns lay ρ M ⊑ (unary n' w os').memRuns lay ρ M' ↔ ∀ x, vf x ⊑ vg x := by
  have h := FuncRuns.isRefinedBy_iff_of_returns (Core.fuelMonotone lay ρ M (unary n w os))
    (Core.fuelMonotone lay ρ M' (unary n' w os'))
    (vs := fun a => match a with | .cons x .nil => [⟨i w, vf x⟩])
    (vt := fun a => match a with | .cons x .nil => [⟨i w, vg x⟩])
    (fun a => match a with | .cons x .nil => ⟨Nf, hf x⟩)
    (fun a => match a with | .cons x .nil => ⟨Ng, hg x⟩)
  refine h.trans ⟨fun h' x => (obs_isRefinedBy_iff _ _).1 (h' (.cons x .nil)), fun h' a => ?_⟩
  match a with
  | .cons x .nil => exact (obs_isRefinedBy_iff _ _).2 (h' x)

end FirTest.Equiv
