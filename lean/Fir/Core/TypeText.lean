import Fir.Core.Types
import Fir.Syntax.Module

/-!
How each core type is written: `iN`, a float format by its alias or as
`float(e, m)`, and `ptr` or `ptr(N)`. The section on the core's text uses
it for the types of values, and for a type that an op carries as an
attribute, as `alloca` carries the type it allocates.
-/

namespace Fir.Core

/-- The alias of the float format `float<e,m>`, if it has one. -/
def floatAlias : Nat → Nat → Option String
  | 5, 10 => some "f16"
  | 8, 7 => some "bf16"
  | 8, 23 => some "f32"
  | 11, 52 => some "f64"
  | 15, 112 => some "f128"
  | _, _ => none

/-- The float format that an alias names: its exponent and mantissa bits. -/
def aliasFormat : String → Option (Nat × Nat)
  | "f16" => some (5, 10)
  | "bf16" => some (8, 7)
  | "f32" => some (8, 23)
  | "f64" => some (11, 52)
  | "f128" => some (15, 112)
  | _ => none

/-- How a core type is written. -/
def Ty.attr : Ty → Attr
  | .int w => .word ("i" ++ toString w)
  | .float e m => match floatAlias e m with
    | some n => .word n
    | none => .app "float" [.int e, .int m]
  | .ptr 0 => .word "ptr"
  | .ptr (n + 1) => .app "ptr" [.int (n + 1)]

/-- Reads `float(e, m)`: a format with no alias, whose numbers are not
negative and which is no wider than `maxWidth` bits in all. -/
def decodeFloat (e m : Int) : Option Ty :=
  if 0 ≤ e ∧ 0 ≤ m ∧ e + m + 1 ≤ maxWidth ∧ floatAlias e.toNat m.toNat = none then
    some (.float e.toNat m.toNat)
  else none

/-- Reads `ptr(N)`: the pointer of a memory other than the default one, no
higher than `maxMemory`. -/
def decodePtr (n : Int) : Option Ty :=
  if 1 ≤ n ∧ n ≤ maxMemory then some (.ptr n.toNat) else none

/-- Reads a core type: `ptr` or `ptr(N)`, `i` and a width of at most
`maxWidth` with no leading zeros, a float format's alias, or
`float(e, m)`. -/
def Ty.decode : Attr → Option Ty
  | .word "ptr" => some (.ptr 0)
  | .word s => match s.toList with
    | 'i' :: ds =>
      let digits := String.ofList ds
      (digits.toNat?).bind fun w =>
        if toString w = digits ∧ w ≤ maxWidth then some (.int w) else none
    | _ => (aliasFormat s).map fun (e, m) => .float e m
  | .app "float" [.int e, .int m] => decodeFloat e m
  | .app "ptr" [.int n] => decodePtr n
  | _ => none

end Fir.Core
