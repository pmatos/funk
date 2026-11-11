import FirTest.Modes

/-!
Tests of the text of float constants (ADR-2026-11-11-1438) on the shared
cases of `tests/dialects/float-text.cases`, which
`crates/funk-ir/tests/float_text.rs` reads too.
`scripts/harness/float_text_cases.py` writes the cases from
`scripts/harness/float_text.py`, an exact-rational reference written apart
from Lean: every value of `float<2,1>` and `float<3,2>`, the hard values and
seeded random ones of `f16`, `bf16`, `f32`, `f64`, `f128` and other formats,
and decimals at and around the midpoint of two neighbouring floats, where
reading rounds to nearest even.

Each case is read with `fir-ref`'s reader of a constant, `floatConstOf`,
which lexes the text and decodes it with `Core.Op.decode`, and with the
spec's `Core.readFloatLit`, which reads a literal before checking that it
is a spelling.
-/

namespace FirTest.FloatText

open Fir FirRef

/-- The format `e,m` of a case. -/
def format (s : String) : Option (Nat × Nat) :=
  match s.splitOn "," with
  | [e, m] => do pure (← e.toNat?, ← m.toNat?)
  | _ => none

/-- The value of bits written `0x` and hexadecimal digits. -/
def bitsOf (s : String) : Option Nat :=
  match s.toList with
  | '0' :: 'x' :: ds => some (Text.hexValue ds)
  | _ => none

/-- The bits that the literal `text` reads as at `float<e,m>`, before the
check that it is their spelling. -/
def readText (e m : Nat) (text : String) : Option Nat :=
  match argAttr text with
  | some (.float l) => (Core.readFloatLit e m l).map (·.toNat)
  | _ => none

/-- Whether a case holds. -/
def holds (line : String) : Bool :=
  match line.splitOn " " with
  | ["spell", f, b, text] => Id.run do
    let some (e, m) := format f | false
    let some b := bitsOf b | false
    (Core.floatLit e m (.ofNat _ b)).print == text &&
      (floatConstOf e m text).map (·.toNat) == some b
  | ["read", f, text, b] => Id.run do
    let some (e, m) := format f | false
    readText e m text == bitsOf b && floatConstOf e m text == none
  | ["reject", f, text] => Id.run do
    let some (e, m) := format f | false
    readText e m text == none && floatConstOf e m text == none
  | _ => false

/-- The cases of the shared file, one per line below `---`. -/
def cases : List String :=
  match (include_str "../../tests/dialects/float-text.cases").splitOn "---\n" with
  | [_, body] => (body.splitOn "\n").filter (!·.isEmpty)
  | _ => []

#guard cases.length > 400
#guard cases.filter (!holds ·) == []

end FirTest.FloatText
