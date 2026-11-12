import Fir.Core.Signature

/-!
# How the float arithmetic, the bit casts and the conversions are written

Each float op of arithmetic is written with its name, and each one that
rounds carries the attribute `round(rne)`: round to nearest, ties to even,
the one rounding mode that M1 has (ADR-2026-11-09-1549,
ADR-2026-11-11-1801). So

* `%s: f32 = fadd round(rne) %a, %b @1`, and `fsub`, `fmul` and `fdiv`
  likewise, take two values of one float type and give one of it;
* `%r: f64 = sqrt round(rne) %a @1` takes one value and gives one;
* `%n: f16 = fneg %a @1` and `%p: f16 = fabs %a @1` take one value and
  give one, and have no attribute: they do not round;
* `%f: bf16 = fma round(rne) %a, %b, %c @1` takes three values and gives
  `a * b + c`, rounded once;
* `%b: i32 = bitcast %f @1` takes a value of a float type and gives its
  bits as an integer of its width, and `%f: f32 = bitcast %b @1` the other
  way. It has no attribute: it does not round;
* `%f: f32 = sitofp round(rne) %i @1` takes a value of an integer type, of
  any width, and gives the integer it holds, read as signed, as a value of
  a float type, rounded; `uitofp` reads it as unsigned.

`round(rne)` is written in the applied form of the grammar, as
`float(e, m)` is. Every op has one spelling: `fadd %a, %b` with no
attribute does not decode, and neither does `fadd round(rtz) %a, %b` or
`fneg round(rne) %a`. A rounding mode other than `rne` is text that does
not decode, as a flag the op does not have is, so `funk verify` and
`fir-ref` reject it. The operands and the result of an op of arithmetic
have one float type, a bit cast's integer has its float's width, a
conversion from an integer takes an integer type and gives a float type,
and an op whose types are otherwise does not decode.

This section gives the names of the ops, their attributes, and how an op
is read back, with the facts that the proof of the round trip uses.
-/

namespace Fir.Core

/-- The name of a float op of two operands. -/
def FBin.name : FBin → String
  | .fadd => "fadd" | .fsub => "fsub" | .fmul => "fmul" | .fdiv => "fdiv"

/-- The name of a float op of one operand. -/
def FUnary.name : FUnary → String
  | .fneg => "fneg" | .fabs => "fabs" | .sqrt => "sqrt"

/-- The attribute of an op that rounds: `round(rne)`. -/
def roundAttr : Attr := .app "round" [.word "rne"]

/-- The attributes of a float op of one operand: `round(rne)` for `sqrt`,
and none for `fneg` and `fabs`, which do not round. -/
def FUnary.attrs : FUnary → List Attr
  | .sqrt => [roundAttr]
  | .fneg | .fabs => []

/-- Whether attributes are exactly `round(rne)`. -/
def isRoundAttrs : List Attr → Bool
  | [.app "round" [.word "rne"]] => true
  | _ => false

/-- The format of a float op of `k` operands: `float<e,m>` when the
operands are `k` values of it and the result is one. -/
def floatOpFormat (k : Nat) : List Ty → List Ty → Option (Nat × Nat)
  | ts, [.float e m] => if ts = List.replicate k (.float e m) then some (e, m) else none
  | _, _ => none

/-- Reads `fadd`, `fsub`, `fmul` or `fdiv`: `round(rne)`, two operands and
one result of one float type. -/
def decodeFBin (o : FBin) (as : List Attr) (ts rs : List Ty) : Option Op :=
  if isRoundAttrs as then (floatOpFormat 2 ts rs).map fun (e, m) => .fbin o e m else none

/-- Whether attributes are those of a float op of one operand: exactly
`round(rne)` for `sqrt`, and none for `fneg` and `fabs`. -/
def FUnary.attrsOk : FUnary → List Attr → Bool
  | .sqrt, as => isRoundAttrs as
  | .fneg, as | .fabs, as => as.isEmpty

/-- Reads `fneg`, `fabs` or `sqrt`: its attributes, one operand and one
result of one float type. -/
def decodeFUnary (o : FUnary) (as : List Attr) (ts rs : List Ty) : Option Op :=
  if o.attrsOk as then (floatOpFormat 1 ts rs).map fun (e, m) => .funary o e m else none

/-- Reads `fma`: `round(rne)`, three operands and one result of one float
type. -/
def decodeFma (as : List Attr) (ts rs : List Ty) : Option Op :=
  if isRoundAttrs as then (floatOpFormat 3 ts rs).map fun (e, m) => .fma e m else none

/-- Reads `bitcast`: no attributes, and one operand and one result, a
float type and an integer type of its width, in either order. -/
def decodeBitcast (as : List Attr) : List Ty → List Ty → Option Op
  | [.float e m], [.int w] => if as.isEmpty ∧ w = floatWidth e m then some (.toBits e m) else none
  | [.int w], [.float e m] => if as.isEmpty ∧ w = floatWidth e m then some (.ofBits e m) else none
  | _, _ => none

/-- Reads `sitofp`, with `signed`, or `uitofp`: `round(rne)`, one operand
of an integer type and one result of a float type. -/
def decodeIntToFloat (signed : Bool) (as : List Attr) : List Ty → List Ty → Option Op
  | [.int n], [.float e m] =>
    if isRoundAttrs as then some (if signed then .sitofp n e m else .uitofp n e m) else none
  | _, _ => none

/-! # Facts for the round trip -/

/-- Attributes that read as `round(rne)` are exactly `round(rne)`. -/
theorem eq_of_isRoundAttrs {as : List Attr} (h : isRoundAttrs as = true) : as = [roundAttr] := by
  unfold isRoundAttrs at h
  split at h
  · rfl
  · cases h

/-- Attributes that read as those of a float op of one operand are its
own. -/
theorem FUnary.attrs_of_attrsOk {o : FUnary} {as : List Attr} (h : o.attrsOk as = true) :
    o.attrs = as := by
  cases o with
  | sqrt => exact (eq_of_isRoundAttrs h).symm
  | fneg | fabs => exact (List.isEmpty_iff.mp h).symm

/-- A float op's format is found only at its `k` operands and one result
of that format. -/
theorem floatOpFormat_eq {k : Nat} {ts rs : List Ty} {e m : Nat}
    (h : floatOpFormat k ts rs = some (e, m)) :
    ts = List.replicate k (.float e m) ∧ rs = [.float e m] := by
  unfold floatOpFormat at h
  split at h
  · split at h
    · cases h
      exact ⟨by assumption, rfl⟩
    · cases h
  · cases h

/-- A float op's format is found at its own operands and result. -/
theorem floatOpFormat_replicate (k e m : Nat) :
    floatOpFormat k (List.replicate k (.float e m)) [.float e m] = some (e, m) := by
  simp [floatOpFormat]

-- `round(rne)` is the one rounding attribute, and each op has its own
-- number of operands.
#guard isRoundAttrs [roundAttr] && !isRoundAttrs [.app "round" [.word "rtz"]] &&
  !isRoundAttrs [] && !isRoundAttrs [roundAttr, roundAttr] && !isRoundAttrs [.word "rne"]
#guard floatOpFormat 2 [.float 8 23, .float 8 23] [.float 8 23] == some (8, 23)
#guard floatOpFormat 2 [.float 8 23, .float 11 52] [.float 8 23] == none
#guard floatOpFormat 1 [.float 8 23, .float 8 23] [.float 8 23] == none
#guard floatOpFormat 1 [.int 32] [.int 32] == none
-- A bit cast reads from the types which way it goes, and its widths must
-- match.
#guard decodeBitcast [] [.float 8 23] [.int 32] == some (.toBits 8 23)
#guard decodeBitcast [] [.int 16] [.float 8 7] == some (.ofBits 8 7)
#guard decodeBitcast [] [.float 8 23] [.int 64] == none &&
  decodeBitcast [] [.int 32] [.int 32] == none && decodeBitcast [] [.float 8 23] [.float 8 23] == none
#guard decodeBitcast [roundAttr] [.float 8 23] [.int 32] == none

-- A conversion from an integer needs `round(rne)`, an integer operand and a
-- float result, of any width and format.
#guard decodeIntToFloat true [roundAttr] [.int 32] [.float 8 23] == some (.sitofp 32 8 23)
#guard decodeIntToFloat false [roundAttr] [.int 1] [.float 15 112] == some (.uitofp 1 15 112)
#guard decodeIntToFloat true [] [.int 32] [.float 8 23] == none &&
  decodeIntToFloat true [.app "round" [.word "rtz"]] [.int 32] [.float 8 23] == none
#guard decodeIntToFloat false [roundAttr] [.float 8 23] [.int 32] == none &&
  decodeIntToFloat false [roundAttr] [.int 32] [.int 32] == none &&
  decodeIntToFloat true [roundAttr] [.int 32, .int 32] [.float 8 23] == none

end Fir.Core
