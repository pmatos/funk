import FirTest.Bit
import FirTest.Mixed

/-!
A sum of three dialects: the core and two extensions of it with different
prefixes, each written over the core alone (ADR-2026-11-10-1310). The toy
dialect `toy` and the bit dialect `bit` know nothing of each other. The sum
`CoreToy ⊞ BitOverToy` adds the bit dialect to the sum of the core and the
toy dialect by lifting it: an inclusion of the core's types in those of
`CoreToy` lets the bit dialect's ops take and give the core's values there.

The spec's theorems on lifts then give the sum's laws with no proof of its
own: its text is lawful, so its valid modules are well formed and its round
trip holds, and it meets the poison obligations, since the toy dialect and
the bit dialect do. The tests show that the sum reads, prints and validates
a module that uses all three prefixes, sends each word to its own dialect,
and that neither smaller sum reads that module.
-/

namespace FirTest

open Fir

/-- The core's types, included in those of the sum of the core and the toy
dialect, as the left side of the sum. -/
abbrev coreInToy : TyIncl CoreDialect.Ty CoreToy.Ty := TyIncl.inl

/-- The bit dialect, written over the core, lifted into the sum of the core
and the toy dialect. -/
abbrev BitOverToy : Dialect := BitExt.lift CoreDialect coreInToy

/-- The sum of the core, the toy dialect and the bit dialect. -/
abbrev CoreToyBit : Dialect := CoreToy ⊞ BitOverToy

/-- The sum's dialect set holds both extensions' names, in the order they
are added. -/
example : names CoreToyBit = ["toy", "bit"] := rfl

/-- The bit dialect's name is new to the sum of the core and the toy
dialect. -/
theorem bit_new : name BitOverToy ∉ names CoreToy := by decide

/-- The core's set, which the bit dialect's words may name, is in the set
of the sum of the core and the toy dialect. -/
theorem core_sub_toy : ∀ x ∈ names CoreDialect, x ∈ names CoreToy := fun _ h => nomatch h

/-! # Lawful text -/

instance : LawfulDialectName CoreToy BitOverToy := Dialect.lift.lawfulName core_sub_toy

instance : LawfulDialectText CoreToyBit := Dialect.lift.sum_lawfulText bit_new core_sub_toy

/-- The words of the sum name only its two extensions, or none. -/
example : LawfulDialectSet CoreToyBit := inferInstance

/-- Every valid module of the sum of three dialects is well formed. -/
theorem coreToyBit_validIsWellFormed : ValidIsWellFormed (d := CoreToyBit) :=
  Dialect.lift.sum_validIsWellFormed bit_new core_sub_toy

/-- The round trip of the sum of three dialects. -/
theorem coreToyBit_printThenParse : PrintThenParse (d := CoreToyBit) Fir.parse :=
  Dialect.lift.sum_printThenParse bit_new core_sub_toy

/-! # Lawful poison -/

/-- The sum of the core and the toy dialect is lawful. -/
instance coreToy_lawful : LawfulDialectPoison CoreToy := Dialect.sum.lawfulPoison fun _ h => h

/-- The sum of three dialects is lawful: the inclusion of the core's types
is lawful, and the bit dialect accepts each core type that the core
accepts. -/
instance coreToyBit_lawful : LawfulDialectPoison CoreToyBit :=
  Dialect.lift.sum_lawfulPoison TyIncl.lawful_inl fun _ h => h

/-! # Words routed to their own dialect -/

#guard decodeOp (d := CoreToyBit) "bit.low" [] [.inl (.inl (.int 8))] [.inr .bit] ==
  some (.inr (.low 8))
#guard decodeOp (d := CoreToyBit) "toy.mask" [.int 3] [.inl (.inl (.int 8))]
  [.inl (.inl (.int 8))] == some (.inl (.inr (.mask 8 3)))
#guard decodeOp (d := CoreToyBit) "add" [] [.inl (.inl (.int 8)), .inl (.inl (.int 8))]
  [.inl (.inl (.int 8))] == some (.inl (.inl (.add 8 {})))
-- A toy op does not decode at the bit dialect's type: the toy dialect
-- cannot write it.
#guard decodeOp (d := CoreToyBit) "toy.mask" [.int 3] [.inr .bit] [.inr .bit] == none
#guard decodeTy (d := CoreToyBit) (.word "bit.bit") == some (.inr .bit)
#guard decodeTy (d := CoreToyBit) (.word "i8") == some (.inl (.inl (.int 8)))
#guard decodeTy (d := CoreToyBit) (.word "bit.i8") == none
#guard decodeTy (d := CoreToyBit) (.word "toy.bit") == none

/-! # A module of three dialects -/

/-- Parses with the sum of three dialects. -/
def parseThree (t : String) : Except ParseError (Module CoreToyBit) := Fir.parse t

/-- `@f` masks `%a` with the toy op, takes its low bit with the bit
dialect, and returns it as an `i1`; `@g` takes a bit. -/
def threeText : String :=
  "func @f(%a: i8) -> i1 {\n^entry:\n  %m: i8 = toy.mask 3 %a @0\n" ++
  "  %b: bit.bit = bit.low %m @0\n  %c: i1 = bit.int %b @0\n  ret %c @0\n}\n\n" ++
  "func @g(%b: bit.bit) -> i1 {\n^entry:\n  %c: i1 = bit.int %b @0\n  ret %c @0\n}\n\n" ++
  "locs {\n  @0 = unknown\n}\n"

-- The sum reads the module, prints it as itself, and finds it valid.
#guard match parseThree threeText with
  | .ok m => m.print == threeText && m.problems.isEmpty
  | .error _ => false
-- Neither smaller sum reads it.
#guard (Fir.parse (d := CoreToy) threeText).toBool == false
#guard (Fir.parse (d := CoreDialect ⊞ BitExt) threeText).toBool == false
-- The toy op keeps its own rule in the sum of three: a mask of 9 bits at
-- `i8` breaks it.
#guard match parseThree (threeText.replace "toy.mask 3" "toy.mask 9") with
  | .ok m => m.problems.any (fun p => p.op == some 0 &&
      p.message == "the op breaks its dialect's own rule")
  | .error _ => false
-- A function that returns a bit holds no valid core or toy op, since
-- neither can write its result types; the bit dialect's op is valid.
#guard match parseThree ("func @h(%a: i8) -> bit.bit {\n^entry:\n" ++
    "  %m: i8 = toy.mask 3 %a @0\n  %b: bit.bit = bit.low %m @0\n  ret @0\n}\n\n" ++
    "locs {\n  @0 = unknown\n}\n") with
  | .ok m =>
    m.problems.any (fun p => p.op == some 0 && p.message == "the op breaks its dialect's own rule") &&
      !m.problems.any (·.op == some 1)
  | .error _ => false

/-! # The theorems' axioms -/

/-- info: 'Fir.Dialect.lift.lawfulText' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Dialect.lift.lawfulText

/-- info: 'Fir.Dialect.lift.lawfulPoison' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Dialect.lift.lawfulPoison

/-- info: 'FirTest.coreToyBit_validIsWellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms coreToyBit_validIsWellFormed

end FirTest
