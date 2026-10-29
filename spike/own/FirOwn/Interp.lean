import FirOwn.Syntax

/-!
# The interpreter: a CFG walk with fuel, generic over dialect and monad

Fuel counts block transfers. Running out is an outcome of its own. A type
error ("stuck") is also reported, but validation rules it out, which is the
type-safety property #11 asks for.
-/

namespace FirOwn

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DecidableEq d.Ty]

/-- A value tagged with its type. -/
abbrev DVal (d : Dialect) [TyDenote d.Ty] := Σ t : d.Ty, ⟦t⟧

abbrev Env (d : Dialect) [TyDenote d.Ty] := List (Name × DVal d)

/-- The end of a run that did not hit UB. -/
inductive Result (V : Type) where
  | ret (vals : List V)
  | fuelExhausted
  | stuck (msg : String)

def Result.map (f : V → W) : Result V → Result W
  | .ret vs => .ret (vs.map f)
  | .fuelExhausted => .fuelExhausted
  | .stuck msg => .stuck msg

def lookup (env : Env d) (x : Name) : Except String (DVal d) :=
  match env.find? (·.1 == x) with
  | some (_, v) => .ok v
  | none => .error s!"unbound value %{x}"

def DVal.cast? : DVal d → (t : d.Ty) → Option ⟦t⟧
  | ⟨t', v⟩, t => if h : t' = t then some (h ▸ v) else none

def toHVector : (ts : List d.Ty) → List (DVal d) → Except String (HVector toType ts)
  | [], [] => .ok .nil
  | t :: ts, v :: vs => do
    let some x := v.cast? t | .error "operand type mismatch"
    return .cons x (← toHVector ts vs)
  | _, _ => .error "operand count mismatch"

def ofHVector : {ts : List d.Ty} → HVector toType ts → List (DVal d)
  | [], .nil => []
  | t :: _, .cons x xs => ⟨t, x⟩ :: ofHVector xs

/-- Bind names to values, checking types and count. -/
def bindAll (env : Env d) : List (Name × d.Ty) → List (DVal d) → Except String (Env d)
  | [], [] => .ok env
  | (x, t) :: ps, v :: vs =>
    if v.1 = t then bindAll ((x, v) :: env) ps vs else .error s!"type mismatch at %{x}"
  | _, _ => .error "argument count mismatch"

variable {m : Type → Type} [Monad m] [DialectDenote d m]

abbrev M (m : Type → Type) := ExceptT String m

def liftE (x : Except String α) : M m α := ExceptT.mk (pure x)

/-- Run a block's ops. Returns the environment, the terminator's exit, the
terminator and its operand values. -/
def runBody (env : Env d) : List (Inst d) → M m (Env d × Exit × Inst d × List (DVal d))
  | [] => throw "block has no terminator"
  | i :: rest => do
    let vs ← liftE (i.args.mapM (lookup env))
    let xs ← liftE (toHVector (sig i.op) vs)
    if isTerminator i.op then
      let e ← (DialectDenote.exit i.op xs : m Exit)
      return (env, e, i, vs)
    else
      let rs ← (DialectDenote.denote i.op xs : m _)
      let env ← liftE (bindAll env i.results (ofHVector rs))
      runBody env rest

def findBlock (f : Func d) (l : Name) : Except String (Block d) :=
  match f.blocks.find? (·.label == l) with
  | some b => .ok b
  | none => .error s!"no block {l}"

/-- Run from block `b`, spending one unit of fuel per block. -/
def runFrom (f : Func d) : Nat → Block d → Env d → M m (Result (DVal d))
  | 0, _, _ => return .fuelExhausted
  | fuel + 1, b, env => do
    let (env, ex, i, vs) ← runBody env b.body
    match ex with
    | .ret => return .ret vs
    | .goto k =>
      let some s := i.succs[k]? | throw "missing successor"
      let tgt ← liftE (findBlock f s.block)
      let avs ← liftE (s.args.mapM (lookup env))
      let env ← liftE (bindAll env tgt.params avs)
      runFrom f fuel tgt env

/-- Run a function on its arguments. -/
def run (f : Func d) (fuel : Nat) (args : List (DVal d)) : m (Result (DVal d)) := do
  let r ← (do
    let some entry := f.blocks.head? | throw "no entry block"
    let env ← liftE (bindAll [] entry.params args)
    runFrom f fuel entry env : M m _).run
  match r with
  | .ok r => pure r
  | .error msg => pure (.stuck msg)

end FirOwn
