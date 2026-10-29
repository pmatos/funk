import FirLeanMLIR.CFG

/-!
# The same samples as `FirOwn.Examples`, as LeanMLIR terms

LeanMLIR terms are intrinsically typed: a variable is a de Bruijn index with a
proof of its type, and names and locations are not part of the term. The fir
text of each sample is in `FirOwn.Examples`.
-/

namespace FirLeanMLIR.Examples

open FirOwn (Prog)

variable {Γ : Ctxt Ty} {eff : EffectKind}

def cst (w : Nat) (v : Int) : Expr Fir Γ eff [.int w] :=
  Expr.mk (.const w v) rfl (EffectKind.pure_le _) .nil .nil

def add (w : Nat) (nsw : Bool) (x y : Γ.Var (.int w)) : Expr Fir Γ eff [.int w] :=
  Expr.mk (.add w nsw) rfl (EffectKind.pure_le _) [x, y]ₕ .nil

def xor (w : Nat) (x y : Γ.Var (.int w)) : Expr Fir Γ eff [.int w] :=
  Expr.mk (.xor w) rfl (EffectKind.pure_le _) [x, y]ₕ .nil

def freeze (w : Nat) (x : Γ.Var (.int w)) : Expr Fir Γ .impure [.int w] :=
  Expr.mk (.freeze w) rfl (EffectKind.le_refl _) [x]ₕ .nil

def br (k : Nat) (ws : List Nat) (args : HVector Γ.Var (ints ws)) :
    Expr Fir Γ .impure [.ctl] :=
  Expr.mk (.br k ws) rfl (EffectKind.pure_le _) args .nil

/-- `cond_br` to two blocks that take no arguments. -/
def condBr (c : Γ.Var (.int 1)) (kt kf : Nat) : Expr Fir Γ .impure [.ctl] :=
  Expr.mk (.condBr kt [] kf []) rfl (EffectKind.le_refl _) [c]ₕ .nil

def ret (w : Nat) (x : Γ.Var (.int w)) : Expr Fir Γ .impure [.ctl] :=
  Expr.mk (.ret [w]) rfl (EffectKind.pure_le _) [x]ₕ .nil

/-- End a block with the `ctl` value just computed. -/
def done : Com Fir ([Ty.ctl] ++ Γ) .impure [.ctl] := .rets [⟨0, rfl⟩]ₕ

/-- `@add3(%x: i8)`: `%c = const 3; %r = add %x, %c; ret %r`. -/
def add3 : Func := ⟨[{
  params := [8]
  body :=
    .var (cst 8 3) <|                       -- Γ = [%c, %x]
    .var (add 8 false ⟨1, rfl⟩ ⟨0, rfl⟩) <| -- Γ = [%r, %c, %x]
    .var (ret 8 ⟨0, rfl⟩) done }]⟩

/-- Two blocks; the branch passes `(%s, %a)` to `next(%p, %q)`. -/
def twoBlocks : Func := ⟨[
  { params := [32, 32]                      -- Γ = [%a, %b]
    body :=
      .var (add 32 false ⟨0, rfl⟩ ⟨1, rfl⟩) <| -- Γ = [%s, %a, %b]
      .var (br 1 [32, 32] [⟨0, rfl⟩, ⟨1, rfl⟩]ₕ) done },
  { params := [32, 32]                      -- Γ = [%p, %q]
    body :=
      .var (add 32 false ⟨0, rfl⟩ ⟨1, rfl⟩) <|
      .var (ret 32 ⟨0, rfl⟩) done }]⟩

/-- Poison from `add nsw`, then `freeze`, then `ret %f` or `ret (xor %f, %f)`. -/
def frozen (w : Nat) (big : Int) (useXor : Bool) : Func := ⟨[{
  params := []
  body :=
    .var (cst w big) <|                  -- Γ = [%m]
    .var (cst w 1) <|                    -- Γ = [%one, %m]
    .var (add w true ⟨1, rfl⟩ ⟨0, rfl⟩) <| -- Γ = [%p, %one, %m]
    .var (freeze w ⟨0, rfl⟩) <|          -- Γ = [%f, %p, ...]
    .var (xor w ⟨0, rfl⟩ ⟨0, rfl⟩) <|    -- Γ = [%z, %f, %p, ...]
    .var (ret w (if useXor then ⟨0, rfl⟩ else ⟨1, rfl⟩)) done }]⟩

def retPoison : Func := ⟨[{
  params := []
  body :=
    .var (cst 8 127) <| .var (cst 8 1) <|
    .var (add 8 true ⟨1, rfl⟩ ⟨0, rfl⟩) <|
    .var (ret 8 ⟨0, rfl⟩) done }]⟩

def branchOnPoison : Func := ⟨[
  { params := []
    body :=
      .var (cst 1 1) <|
      .var (add 1 true ⟨0, rfl⟩ ⟨0, rfl⟩) <|
      .var (condBr ⟨0, rfl⟩ 1 1) done },
  { params := []
    body := .var (cst 8 0) <| .var (ret 8 ⟨0, rfl⟩) done }]⟩

def spin : Func := ⟨[{ params := [], body := .var (br 0 [] .nil) done }]⟩

/-! ## Runs, with the handlers and proofs of `FirOwn.Prog` -/

inductive Obs where
  | poison
  | value (w : Nat) (n : Nat)
  deriving Repr, DecidableEq

def obs : IntVal → Obs
  | ⟨_, .poison⟩ => .poison
  | ⟨w, .value x⟩ => .value w x.toNat

inductive Outcome where
  | ret (vals : List Obs)
  | ub (reason : String)
  | fuelExhausted
  | stuck (msg : String)
  deriving Repr, DecidableEq

def toOutcome : Prog.Ev Result → Outcome
  | .ok (.ret vs) => .ret (vs.map obs)
  | .ok .fuelExhausted => .fuelExhausted
  | .ok (.stuck msg) => .stuck msg
  | .ub r => .ub r

def runAll (f : Func) (args : List IntVal) (fuel := 64) (budget := 16) :
    List Outcome × Bool :=
  let (es, over) := Prog.exhaustive (run f fuel args) budget
  (es.map toOutcome, over)

def runScripted (f : Func) (args : List IntVal) (script : List Nat) (fuel := 64) :
    Option (Outcome × Bool) :=
  (Prog.scripted (run f fuel args) script).map fun (e, u) => (toOutcome e, u)

def iv (w : Nat) (n : Int) : IntVal := ⟨w, .value (BitVec.ofInt w n)⟩

#guard runAll add3 [iv 8 40] == ([.ret [.value 8 43]], false)
#guard runAll twoBlocks [iv 32 5, iv 32 7] == ([.ret [.value 32 17]], false)
#guard runAll retPoison [] == ([.ret [.poison]], false)
#guard runAll branchOnPoison [] == ([.ub "branch on poison"], false)
#guard runAll spin [] == ([.fuelExhausted], false)
#guard runAll (frozen 2 1 false) [] ==
  ((List.range 4).map fun n => .ret [.value 2 n], false)
#guard runAll (frozen 8 127 true) [] ==
  ((List.range 256).map fun _ => .ret [.value 8 0], false)
#guard (runAll (frozen 8 127 true) [] (budget := 4)).2 == true
#guard runScripted (frozen 2 1 false) [] [3] == some (.ret [.value 2 3], true)

/-! ## Proofs about one sample -/

theorem frozen_i2_outcomes :
    runAll (frozen 2 1 false) [] =
      ([.ret [.value 2 0], .ret [.value 2 1], .ret [.value 2 2], .ret [.value 2 3]],
        false) := by
  decide

theorem frozen_xor_run :
    run (frozen 8 127 true) 64 [] =
      Prog.choose 8 fun b => .pure (.ret [⟨8, .value (b ^^^ b)⟩]) := by
  rfl

end FirLeanMLIR.Examples
