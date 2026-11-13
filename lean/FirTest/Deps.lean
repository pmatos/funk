import FirTest.Bit
import FirTest.Mixed

/-!
A sum of three dialects: the core and two extensions of it with different
prefixes, each written over the core alone (ADR-2026-11-09-2306). The toy
dialect `toy` and the bit dialect `bit` know nothing of each other. The sum
`CoreToy ⊞ BitOverToy` adds the bit dialect to the sum of the core and the
toy dialect by lifting it: an inclusion of the core's types in those of
`CoreToy` lets the bit dialect's ops take and give the core's values there.

The spec's theorems on lifts then give the sum's laws with no proof of its
own: its text is lawful, so its valid modules are well formed and its round
trip holds, and it meets the poison and effect obligations, since the toy
dialect and the bit dialect do. The tests show that the sum reads, prints and validates
a module that uses all three prefixes, sends each word to its own dialect,
and that neither smaller sum reads that module.
-/

namespace FirTest

open Fir

/-- The core's types, included in those of the sum of the core and the toy
dialect, as the left side of the sum. -/
abbrev coreInToy : TyIncl CoreDialect.Ty CoreToy.Ty := TyIncl.inl

/-- The core's memories, named as the sum of the core and the toy dialect
names them: by the toy dialect's names for them. -/
abbrev coreMemInToy : DialectEffects.Mem CoreDialect → DialectEffects.Mem CoreToy :=
  DialectMemOver.ofBase (base := CoreDialect) (e := Ext Toy.Op)

/-- The bit dialect, written over the core, lifted into the sum of the core
and the toy dialect. -/
abbrev BitOverToy : Dialect := BitExt.lift CoreDialect coreInToy coreMemInToy

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

/-! # Lawful poison, effects and totality -/

/-- The sum of the core and the toy dialect is lawful. -/
instance coreToy_lawful : LawfulDialectPoison CoreToy := Dialect.sum.lawfulPoison fun _ h => h

/-- The sum of the core and the toy dialect is lawful in its effects, since
both are. -/
instance coreToy_lawfulEffects : LawfulDialectEffects CoreToy :=
  Dialect.sum.lawfulEffects fun _ h => h

/-- The sum of the core and the toy dialect is lawful in its totality, since
both are. -/
instance coreToy_lawfulTotal : LawfulDialectTotal CoreToy :=
  Dialect.sum.lawfulTotal fun _ h => h

/-- The sum of the core and the toy dialect is lawful in its monotonicity,
since both are. -/
instance coreToy_lawfulMonotone : LawfulDialectMonotone CoreToy :=
  Dialect.sum.lawfulMonotone fun _ h => h

/-- The sum of the core and the toy dialect is lawful in its poison with
memory, since both are. -/
instance coreToy_lawfulMemPoison : LawfulDialectMemPoison CoreToy :=
  Dialect.sum.lawfulMemPoison fun _ h => h

/-- The sum of three dialects is lawful: the inclusion of the core's types
is lawful, and the bit dialect accepts each core type that the core
accepts. -/
instance coreToyBit_lawful : LawfulDialectPoison CoreToyBit :=
  Dialect.lift.sum_lawfulPoison TyIncl.lawful_inl fun _ h => h

/-- The sum of three dialects is lawful in its effects, under the same
conditions. -/
instance coreToyBit_lawfulEffects : LawfulDialectEffects CoreToyBit :=
  Dialect.lift.sum_lawfulEffects TyIncl.lawful_inl fun _ h => h

/-- The sum of three dialects is lawful in its totality: the bit dialect
accepts each core type that the core accepts. -/
instance coreToyBit_lawfulTotal : LawfulDialectTotal CoreToyBit :=
  Dialect.lift.sum_lawfulTotal fun _ h => h

/-- The sum of three dialects is lawful in its monotonicity: the inclusion
of the core's types is lawful, and the bit dialect accepts each core type
that the core accepts. -/
instance coreToyBit_lawfulMonotone : LawfulDialectMonotone CoreToyBit :=
  Dialect.lift.sum_lawfulMonotone TyIncl.lawful_inl fun _ h => h

/-- The sum of three dialects is lawful in its poison with memory, under the
conditions of its lawfulness in the set monad. -/
instance coreToyBit_lawfulMemPoison : LawfulDialectMemPoison CoreToyBit :=
  Dialect.lift.sum_lawfulMemPoison TyIncl.lawful_inl fun _ h => h

/-- The effects of an op of the sum of three dialects, on the memories of
its three dialects. -/
def coreToyBitEffects (o : CoreToyBit.Op) : Effects ((Core.Mem ⊕ Empty) ⊕ Empty) := effects o

-- Each op of the sum of three dialects has its own dialect's effects.
#guard Core.samples.all (fun o =>
    coreToyBitEffects (.inl (.inl o)) == (Core.Op.effects o).map (.inl ∘ .inl)) &&
  coreToyBitEffects (.inl (.inr (.mask 8 3))) == {} &&
  coreToyBitEffects (.inr (.low 8)) == {} && coreToyBitEffects (.inr .int) == {}
#guard poisonClass (d := CoreToyBit) (.inr (.low 8)) == .propagates

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
  | .ok m => m.problems.any (fun p => p.func == some "f" && p.op == some 0 &&
      p.message == "the op breaks its dialect's own rule")
  | .error _ => false
-- A function that returns a bit holds no valid core or toy op, since
-- neither can write its result types: the toy op and the core `ret` break
-- their dialects' rules, and the bit dialect's op is valid.
#guard match parseThree ("func @h(%a: i8) -> bit.bit {\n^entry:\n" ++
    "  %m: i8 = toy.mask 3 %a @0\n  %b: bit.bit = bit.low %m @0\n  ret @0\n}\n\n" ++
    "locs {\n  @0 = unknown\n}\n") with
  | .ok m =>
    let broken (i : Nat) := m.problems.any fun p =>
      p.func == some "h" && p.op == some i && p.message == "the op breaks its dialect's own rule"
    broken 0 && broken 2 && !m.problems.any (·.op == some 1)
  | .error _ => false

/-! # Running a lifted op

The bit dialect's op runs in the sum by its own rule, with memory, on values
that cross the inclusion of the core's types, and keeps the memories. -/

/-- The layout entries of a run with one memory, in the tests below. -/
abbrev oneLayout : Unit → MemLayout := fun _ => MemLayout.default

/-- `bit.low` at `i8` takes the low bit of 5 in the sum of three, with
memory. -/
example : letI := DialectMemDenote.denoteAt (d := CoreToyBit) oneLayout (fun _ => ())
    DialectDenote.denote (m := StateT (Memory.Memories Unit (unitsOf oneLayout)) SetM)
      (d := CoreToyBit) (.inr (.low 8)) (.cons (.value 5) .nil) Memory.Memories.empty
      (.ok (.cons (.value true) .nil, Memory.Memories.empty)) :=
  .inl ⟨_, .inl ⟨_, rfl, rfl⟩, rfl⟩

/-- `bit.int` gives a poison bit back as poison, with memory. -/
example : letI := DialectMemDenote.denoteAt (d := CoreToyBit) oneLayout (fun _ => ())
    DialectDenote.denote (m := StateT (Memory.Memories Unit (unitsOf oneLayout)) SetM)
      (d := CoreToyBit) (.inr .int) (.cons .poison .nil) Memory.Memories.empty
      (.ok (.cons .poison .nil, Memory.Memories.empty)) :=
  .inl ⟨_, .inl ⟨_, rfl, rfl⟩, rfl⟩

/-! # Other inclusions

The core is included in the sum of three by `inl` twice, and the types of
an extension over the core and the bit dialect in those of the same
extension over the sum of three by `over`. Instance search finds a lift by
either. -/

/-- The core's types, included in those of the sum of three. -/
abbrev coreInThree : TyIncl CoreDialect.Ty CoreToyBit.Ty := coreInToy.comp TyIncl.inl

/-- The core's memories, named as the sum of three names them. -/
abbrev coreMemInThree : DialectEffects.Mem CoreDialect → DialectEffects.Mem CoreToyBit :=
  DialectMemOver.ofBase (base := CoreToy) (e := BitOverToy) ∘ coreMemInToy

#guard coreInThree.incl (.int 8) == .inl (.inl (.int 8))
#guard coreInThree.proj (.inl (.inl (.int 8))) == some (.int 8)
#guard coreInThree.proj (.inr .bit) == none

-- The bit dialect, lifted into the sum of three by `coreInThree`, reads
-- its op at the core's types there.
#guard decodeOp (d := CoreToyBit.over (BitExt.lift CoreDialect coreInThree coreMemInThree))
  "bit.low" []
  [.inl (.inl (.inl (.int 8)))] [.inr .bit] == some (.low 8)

/-- The types of the sum of the core and the bit dialect, included in those
of the sum of three. -/
abbrev coreBitInThree : TyIncl (CoreDialect ⊞ BitExt).Ty CoreToyBit.Ty := coreInToy.over

#guard coreBitInThree.incl (.inr .bit) == .inr .bit
#guard coreBitInThree.proj (.inl (.inl (.int 8))) == some (.inl (.int 8))

/-- The memories of the sum of the core and the bit dialect, named as the
sum of three names them: the bit dialect's memory map in the sum of three. -/
abbrev coreBitMemInThree :
    DialectEffects.Mem (CoreDialect ⊞ BitExt) → DialectEffects.Mem CoreToyBit :=
  Dialect.lift.liftMem (e := BitExt) coreMemInToy

section
variable (e : Dialect) [TyDenote e.Ty] [DialectName e]
  [DialectSignature ((CoreDialect ⊞ BitExt).over e)] [DialectText ((CoreDialect ⊞ BitExt).over e)]
  [DialectValidation ((CoreDialect ⊞ BitExt).over e)]

example :
    DialectText (CoreToyBit ⊞ e.lift (CoreDialect ⊞ BitExt) coreBitInThree coreBitMemInThree) :=
  inferInstance

example :
    DialectValidation (CoreToyBit ⊞ e.lift (CoreDialect ⊞ BitExt) coreBitInThree coreBitMemInThree) :=
  inferInstance

end

/-! # The theorems' axioms -/

/-- info: 'Fir.Dialect.lift.lawfulText' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Dialect.lift.lawfulText

/-- info: 'Fir.Dialect.lift.lawfulPoison' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Dialect.lift.lawfulPoison

/-- info: 'Fir.Dialect.lift.lawfulEffects' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Dialect.lift.lawfulEffects

/-- info: 'FirTest.Bit.lawfulDialectEffects' depends on axioms: [propext] -/
#guard_msgs in #print axioms Bit.lawfulDialectEffects

/-- info: 'FirTest.coreToyBit_validIsWellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms coreToyBit_validIsWellFormed

end FirTest
