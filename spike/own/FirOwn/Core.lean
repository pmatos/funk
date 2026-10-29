import FirOwn.Prog
import FirOwn.Syntax

/-!
# The core dialect, spike subset

`const`, `add` (with `nsw`, so that poison can arise), `xor`, `freeze`,
`br`, `cond_br` and `ret`. A value of `iN` is poison or an `N`-bit vector.
Poison is a value; immediate UB is an effect of the monad. They never meet.
-/

namespace FirOwn

/-- Poison or a value, as LeanMLIR's `PoisonOr`. -/
inductive PoisonOr (α : Type) where
  | poison
  | value (a : α)
  deriving Repr, DecidableEq

namespace Core

/-- Core types: `iN` for any `N` (validation requires `N ≥ 1`). -/
inductive Ty where
  | int (w : Nat)
  deriving Repr, DecidableEq

/-- Core ops in this spike. Attributes (width, constant, flags) live in the
op, as in LeanMLIR. `ret` carries the types it returns. -/
inductive Op where
  | const (w : Nat) (v : Int)
  | add (w : Nat) (nsw : Bool)
  | xor (w : Nat)
  | freeze (w : Nat)
  | br
  | condBr
  | ret (ts : List Ty)
  deriving Repr, DecidableEq

end Core

abbrev Core : Dialect := ⟨Core.Op, Core.Ty⟩

instance : TyDenote Core.Ty where
  toType | .int w => PoisonOr (BitVec w)

instance : DialectSignature Core where
  sig
    | .const _ _ | .br => []
    | .add w _ | .xor w => [.int w, .int w]
    | .freeze w => [.int w]
    | .condBr => [.int 1]
    | .ret ts => ts
  returnTypes
    | .const w _ | .add w _ | .xor w | .freeze w => [.int w]
    | .br | .condBr | .ret _ => []
  isTerminator
    | .br | .condBr | .ret _ => true
    | _ => false

namespace Core

/-- `add`: poison in, poison out; with `nsw`, signed overflow is poison. -/
def add (nsw : Bool) : PoisonOr (BitVec w) → PoisonOr (BitVec w) → PoisonOr (BitVec w)
  | .value x, .value y =>
    if nsw ∧ (x + y).toInt ≠ x.toInt + y.toInt then .poison else .value (x + y)
  | _, _ => .poison

def xor : PoisonOr (BitVec w) → PoisonOr (BitVec w) → PoisonOr (BitVec w)
  | .value x, .value y => .value (x ^^^ y)
  | _, _ => .poison

/-- `freeze`: poison becomes one chosen value. The op runs once, so every use
of its result sees the same bits. -/
def freeze [Monad m] [MonadFir m] : PoisonOr (BitVec w) → m (PoisonOr (BitVec w))
  | .poison => .value <$> MonadFir.choose w
  | .value x => pure (.value x)

/-- `cond_br`: branching on poison is immediate UB (S1). -/
def condBr [Monad m] [MonadFir m] : PoisonOr (BitVec 1) → m Exit
  | .poison => MonadFir.ub "branch on poison"
  | .value c => pure (if c = 1#1 then .goto 0 else .goto 1)

end Core

instance [Monad m] [MonadFir m] : DialectDenote Core m where
  denote
    | .const w v, .nil => pure (.cons (.value (BitVec.ofInt w v)) .nil)
    | .add _ nsw, .cons x (.cons y .nil) => pure (.cons (Core.add nsw x y) .nil)
    | .xor _, .cons x (.cons y .nil) => pure (.cons (Core.xor x y) .nil)
    | .freeze _, .cons x .nil => do return .cons (← Core.freeze x) .nil
    | .br, _ | .condBr, _ | .ret _, _ => pure .nil
  exit
    | .condBr, .cons c .nil => Core.condBr c
    | .br, _ => pure (.goto 0)
    | _, _ => pure .ret

end FirOwn
