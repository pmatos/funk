import LeanMLIR.Basic
import LeanMLIR.Util.Poison
import FirOwn.Prog

/-!
# fir's spike subset as a LeanMLIR dialect

Values of `iN` are LeanMLIR's own `PoisonOr (BitVec N)`. The dialect monad is
`FirOwn.Prog`, the free monad over choice and UB, so `freeze` really chooses
and `cond_br` on poison is UB, distinct from poison.

LeanMLIR has no CFG: a region is one straight-line `Com` ending in `rets`.
Terminators are therefore encoded as ops that return a value of type `ctl`,
which says where control goes next. `CFG.lean` walks those blocks.
-/

namespace FirLeanMLIR

open FirOwn (Prog MonadFir)

inductive Ty where
  | int (w : Nat)
  /-- The result of a terminator: where control goes next. -/
  | ctl
  deriving DecidableEq, Repr

/-- Block arguments cross block boundaries dynamically typed. -/
abbrev IntVal := Σ w, PoisonOr (BitVec w)

/-- Where control goes: to block `k` with arguments, or back to the caller. -/
inductive Ctl where
  | goto (k : Nat) (args : List IntVal)
  | ret (vals : List IntVal)

inductive Op where
  | const (w : Nat) (v : Int)
  | add (w : Nat) (nsw : Bool)
  | xor (w : Nat)
  | freeze (w : Nat)
  /-- `br k(args)`: jump to block `k`; `ws` are the argument widths. -/
  | br (k : Nat) (ws : List Nat)
  /-- `cond_br %c, kt(args), kf(args)`. -/
  | condBr (kt : Nat) (wt : List Nat) (kf : Nat) (wf : List Nat)
  | ret (ws : List Nat)
  deriving DecidableEq, Repr

abbrev Fir : Dialect where
  Op := Op
  Ty := Ty
  m := Prog

@[reducible]
instance : TyDenote Ty where
  toType
    | .int w => PoisonOr (BitVec w)
    | .ctl => Ctl

instance instInhabitedTy (t : Ty) : Inhabited ⟦t⟧ :=
  match t with
  | .int _ => ⟨.poison⟩
  | .ctl => ⟨.ret []⟩

def ints (ws : List Nat) : List Ty := ws.map .int

instance : DialectSignature Fir where
  signature
    | .const w _ => ⟨[], [], [.int w], .pure⟩
    | .add w _ | .xor w => ⟨[.int w, .int w], [], [.int w], .pure⟩
    | .freeze w => ⟨[.int w], [], [.int w], .impure⟩
    | .br _ ws => ⟨ints ws, [], [.ctl], .pure⟩
    | .condBr _ wt _ wf => ⟨.int 1 :: ints (wt ++ wf), [], [.ctl], .impure⟩
    | .ret ws => ⟨ints ws, [], [.ctl], .pure⟩

def toInts : (ws : List Nat) → HVector toType (ints ws) → List IntVal
  | [], .nil => []
  | w :: ws, .cons x xs => ⟨w, x⟩ :: toInts ws xs

namespace Sem

def add (nsw : Bool) (x y : PoisonOr (BitVec w)) : PoisonOr (BitVec w) := do
  let x ← x
  let y ← y
  if nsw ∧ (x + y).toInt ≠ x.toInt + y.toInt then .poison else .value (x + y)

def xor (x y : PoisonOr (BitVec w)) : PoisonOr (BitVec w) := do
  return (← x) ^^^ (← y)

/-- `freeze`: poison becomes one chosen value. -/
def freeze (x : PoisonOr (BitVec w)) : Prog (PoisonOr (BitVec w)) :=
  match x with
  | .poison => .value <$> MonadFir.choose w
  | .value a => pure (.value a)

/-- `cond_br`: branching on poison is immediate UB. -/
def condBr (kt : Nat) (nt : Nat) (kf : Nat) (c : PoisonOr (BitVec 1))
    (args : List IntVal) : Prog Ctl :=
  match c with
  | .poison => MonadFir.ub "branch on poison"
  | .value b => pure <|
    if b = 1#1 then .goto kt (args.take nt) else .goto kf (args.drop nt)

end Sem

instance : DialectDenote Fir where
  denote
    | .const w v, .nil, .nil => [PoisonOr.value (BitVec.ofInt w v)]ₕ
    | .add _ nsw, (x ::ₕ y ::ₕ .nil), .nil => [Sem.add nsw x y]ₕ
    | .xor _, (x ::ₕ y ::ₕ .nil), .nil => [Sem.xor x y]ₕ
    | .freeze _, (x ::ₕ .nil), .nil => (fun y => [y]ₕ) <$> Sem.freeze x
    | .br k ws, args, .nil => [Ctl.goto k (toInts ws args)]ₕ
    | .condBr kt wt kf wf, (c ::ₕ args), .nil =>
      (fun y => [y]ₕ) <$> Sem.condBr kt wt.length kf c (toInts (wt ++ wf) args)
    | .ret ws, args, .nil => [Ctl.ret (toInts ws args)]ₕ

end FirLeanMLIR
