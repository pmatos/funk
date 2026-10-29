import FirLeanMLIR.Dialect

/-!
# A CFG layer on top of LeanMLIR

This layer is outside LeanMLIR. Each block is a LeanMLIR `Com` over its own
arguments only, ending in a terminator op that yields a `Ctl`. Values cross
block boundaries untyped (`IntVal`) and are type-checked on entry. Block
bodies cannot see values of dominating blocks: everything live must be passed
as a block argument.
-/

namespace FirLeanMLIR

open FirOwn (Prog)

/-- A block: argument widths, and a body over exactly those arguments. -/
structure Block where
  params : List Nat
  body : Com Fir (.ofList (ints params)) .impure [.ctl]

/-- A function: its blocks; block 0 is the entry. -/
structure Func where
  blocks : List Block

inductive Result where
  | ret (vals : List IntVal)
  | fuelExhausted
  | stuck (msg : String)

/-- Type-check block arguments against the block's parameter widths. -/
def argsFor : (ps : List Nat) → List IntVal → Option (HVector toType (ints ps))
  | [], [] => some .nil
  | p :: ps, ⟨w, v⟩ :: vs =>
    if h : w = p then (fun rest => (h ▸ v) ::ₕ rest) <$> argsFor ps vs else none
  | _, _ => none

/-- Run from block `k`, spending one unit of fuel per block. -/
def runFrom (f : Func) : Nat → Nat → List IntVal → Prog Result
  | 0, _, _ => pure .fuelExhausted
  | fuel + 1, k, args => do
    let some b := f.blocks[k]? | pure (.stuck s!"no block {k}")
    let some xs := argsFor b.params args | pure (.stuck s!"bad arguments to block {k}")
    let out ← (b.body.denote (Ctxt.Valuation.ofHVector xs) : Prog _)
    match out.head with
    | .ret vs => pure (.ret vs)
    | .goto k' vs => runFrom f fuel k' vs

def run (f : Func) (fuel : Nat) (args : List IntVal) : Prog Result :=
  runFrom f fuel 0 args

end FirLeanMLIR
