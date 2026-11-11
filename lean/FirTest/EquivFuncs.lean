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

Each run lemma below gives a function's run at one budget, on any argument,
in any module: it calls no function, so the module does not matter. The
proof names the function's ops one by one, with the lemmas of
`FirTest.EquivSteps`; each side condition, such as the lookup of an
operand, holds by `rfl`.
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

/-- `@add_self`: `add %x, %x`. -/
abbrev addSelf (w : Nat) : Func CoreDialect := unary "add_self" w [
  op [("y", i w)] (.add w {}) ["x", "x"],
  op [] (.ret [i w]) ["y"]]

/-- `@shl_one`: `shl %x, 1`. -/
abbrev shlOne (w : Nat) : Func CoreDialect := unary "shl_one" w [
  op [("one", i w)] (.const w 1) [],
  op [("y", i w)] (.shl w) ["x", "one"],
  op [] (.ret [i w]) ["y"]]

/-- `@mul_two`: `mul %x, 2`. -/
abbrev mulTwo (w : Nat) : Func CoreDialect := unary "mul_two" w [
  op [("two", i w)] (.const w 2) [],
  op [("y", i w)] (.mul w {}) ["x", "two"],
  op [] (.ret [i w]) ["y"]]

/-- The flag `nsw` alone. -/
def nsw : WrapFlags := { nsw := true }

/-- `@add_nsw_self`: `add nsw %x, %x`. -/
abbrev addNswSelf (w : Nat) : Func CoreDialect := unary "add_nsw_self" w [
  op [("y", i w)] (.add w nsw) ["x", "x"],
  op [] (.ret [i w]) ["y"]]

/-- `@mul_nsw_two`: `mul nsw %x, 2`. -/
abbrev mulNswTwo (w : Nat) : Func CoreDialect := unary "mul_nsw_two" w [
  op [("two", i w)] (.const w 2) [],
  op [("y", i w)] (.mul w nsw) ["x", "two"],
  op [] (.ret [i w]) ["y"]]

/-- The module of the five functions at `iN`, with `N = w`. -/
def pairs (w : Nat) : Module CoreDialect :=
  ⟨[], [addSelf w, shlOne w, mulTwo w, addNswSelf w, mulNswTwo w].map .func, [(0, .unknown)]⟩

/-- The module's text, as `fir-ref` reads it. -/
def pairsText (w : Nat) : String := (pairs w).print

/-- The one argument of an argument vector. -/
def arg {w : Nat} : HVector toType [i w] → ⟦i w⟧
  | .cons x _ => x

/-! # The run of each function -/

variable {M : Module CoreDialect} {w : Nat}

/-- `@add_self` returns `add %x, %x` after two steps. -/
theorem addSelf_runs (a : HVector toType ((addSelf w).params.map (·.2))) :
    (addSelf w).runs M a 2 =
      (pure (.ret [⟨i w, addWith {} (arg a) (arg a)⟩]) : ExceptT Stuck SetM (Result Core.Obs)) := by
  match a with
  | .cons x .nil =>
  refine (run_of_enter (f := addSelf w) (args := .cons x .nil)
    (Func.enter_ok rfl rfl (HVector.toDVals_types _)) 2).trans ?_
  rw [runOps_denote (args := .cons x (.cons x .nil)) (rs := .cons (addWith {} x x) .nil)
    rfl (operands_cons rfl (operands_cons rfl rfl)) rfl rfl rfl rfl,
    runOps_ret (args := .cons (addWith {} x x) .nil) rfl (operands_cons rfl rfl) rfl rfl rfl]
  simp
  rfl

/-- `@add_nsw_self` returns `add nsw %x, %x` after two steps. -/
theorem addNswSelf_runs (a : HVector toType ((addNswSelf w).params.map (·.2))) :
    (addNswSelf w).runs M a 2 =
      (pure (.ret [⟨i w, addWith nsw (arg a) (arg a)⟩]) : ExceptT Stuck SetM (Result Core.Obs)) := by
  match a with
  | .cons x .nil =>
  refine (run_of_enter (f := addNswSelf w) (args := .cons x .nil)
    (Func.enter_ok rfl rfl (HVector.toDVals_types _)) 2).trans ?_
  rw [runOps_denote (args := .cons x (.cons x .nil)) (rs := .cons (addWith nsw x x) .nil)
    rfl (operands_cons rfl (operands_cons rfl rfl)) rfl rfl rfl rfl,
    runOps_ret (args := .cons (addWith nsw x x) .nil) rfl (operands_cons rfl rfl) rfl rfl rfl]
  simp
  rfl

/-- `@shl_one` returns `shl %x, 1` after three steps. -/
theorem shlOne_runs (a : HVector toType ((shlOne w).params.map (·.2))) :
    (shlOne w).runs M a 3 =
      (pure (.ret [⟨i w, shlValues (arg a) (.value 1)⟩]) : ExceptT Stuck SetM (Result Core.Obs)) := by
  match a with
  | .cons x .nil =>
  refine (run_of_enter (f := shlOne w) (args := .cons x .nil)
    (Func.enter_ok rfl rfl (HVector.toDVals_types _)) 3).trans ?_
  rw [runOps_denote (args := .nil) (rs := .cons (constValue w 1) .nil) rfl rfl rfl rfl rfl rfl,
    runOps_denote (args := .cons x (.cons (PoisonOr.value 1) .nil)) (rs := .cons (shlValues x (.value 1)) .nil)
      rfl (operands_cons rfl (operands_cons rfl rfl)) rfl rfl rfl rfl,
    runOps_ret (args := .cons (shlValues x (.value 1)) .nil) rfl (operands_cons rfl rfl) rfl rfl rfl]
  simp
  rfl

/-- `@mul_two` returns `mul %x, 2` after three steps. -/
theorem mulTwo_runs (a : HVector toType ((mulTwo w).params.map (·.2))) :
    (mulTwo w).runs M a 3 =
      (pure (.ret [⟨i w, mulWith {} (arg a) (.value 2)⟩]) : ExceptT Stuck SetM (Result Core.Obs)) := by
  match a with
  | .cons x .nil =>
  refine (run_of_enter (f := mulTwo w) (args := .cons x .nil)
    (Func.enter_ok rfl rfl (HVector.toDVals_types _)) 3).trans ?_
  rw [runOps_denote (args := .nil) (rs := .cons (constValue w 2) .nil) rfl rfl rfl rfl rfl rfl,
    runOps_denote (args := .cons x (.cons (PoisonOr.value 2) .nil))
      (rs := .cons (mulWith {} x (.value 2)) .nil)
      rfl (operands_cons rfl (operands_cons rfl rfl)) rfl rfl rfl rfl,
    runOps_ret (args := .cons (mulWith {} x (.value 2)) .nil) rfl (operands_cons rfl rfl) rfl rfl rfl]
  simp
  rfl

/-- `@mul_nsw_two` returns `mul nsw %x, 2` after three steps. -/
theorem mulNswTwo_runs (a : HVector toType ((mulNswTwo w).params.map (·.2))) :
    (mulNswTwo w).runs M a 3 =
      (pure (.ret [⟨i w, mulWith nsw (arg a) (.value 2)⟩]) : ExceptT Stuck SetM (Result Core.Obs)) := by
  match a with
  | .cons x .nil =>
  refine (run_of_enter (f := mulNswTwo w) (args := .cons x .nil)
    (Func.enter_ok rfl rfl (HVector.toDVals_types _)) 3).trans ?_
  rw [runOps_denote (args := .nil) (rs := .cons (constValue w 2) .nil) rfl rfl rfl rfl rfl rfl,
    runOps_denote (args := .cons x (.cons (PoisonOr.value 2) .nil))
      (rs := .cons (mulWith nsw x (.value 2)) .nil)
      rfl (operands_cons rfl (operands_cons rfl rfl)) rfl rfl rfl rfl,
    runOps_ret (args := .cons (mulWith nsw x (.value 2)) .nil) rfl (operands_cons rfl rfl) rfl rfl rfl]
  simp
  rfl

end FirTest.Equiv
