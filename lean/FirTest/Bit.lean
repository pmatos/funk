import FirTest.OverCore

/-!
A test dialect named `bit`, with a type of its own, written over the core:
the second prefix that a sum of three dialects needs
(ADR-2026-11-10-1310). Every other test dialect is named `toy`
(ADR-2026-10-30-1146), and a sum holds two dialects only under different
names.

Its type `bit.bit` is one bit, or poison. `%b: bit.bit = bit.low %x` takes
the low bit of the integer `%x`, and `%y: i1 = bit.int %b` gives the bit
back as an `i1`. Both propagate poison and are pure. The dialect states
every class over the core, and meets the text laws and the poison and
effect obligations, so `FirTest.Deps` can lift it into the sum of the core
and the toy dialect.
-/

namespace FirTest.Bit

/-- The bit dialect's own types: one, `bit.bit`. -/
inductive Ty where
  | bit
  deriving Repr, DecidableEq

/-- An op of the bit dialect: `low w` takes the low bit of an `iN` with
`N = w`, and `int` gives a bit as an `i1`. -/
inductive Op where
  | low (w : Nat)
  | int
  deriving Repr, DecidableEq

end FirTest.Bit

namespace FirTest

open Fir

/-- The bit dialect, before it is put over a base. -/
abbrev BitExt : Dialect := ⟨Bit.Op, Bit.Ty⟩

instance : DialectName BitExt := ⟨"bit"⟩

/-- The bit dialect over the core: its ops, at the core's types and its own. -/
abbrev BitDialect : Dialect := CoreDialect.over BitExt

namespace Bit

/-- A bit is a `Bool`, or poison. -/
instance : TyDenote Ty := ⟨fun | .bit => PoisonOr Bool⟩

/-- A bit is poison when it is the poison. -/
def Ty.IsPoison : {t : Ty} → ⟦t⟧ → Prop
  | .bit, v => v = .poison

/-- A bit is refined as a `PoisonOr` value. -/
def Ty.IsRefinedBy : {t : Ty} → ⟦t⟧ → ⟦t⟧ → Prop
  | .bit, a, b => PoisonOr.IsRefinedBy a b

instance : TyPoison Ty := ⟨Ty.IsPoison⟩

instance : TyRefinement Ty := ⟨Ty.IsRefinedBy⟩

instance : DialectSignature BitDialect where
  sig
    | .low w => [.inl (.int w)]
    | .int => [.inr .bit]
  returnTypes
    | .low _ => [.inr .bit]
    | .int => [.inl (.int 1)]
  isTerminator _ := false
  succCount _ := 0

/-! # Text -/

/-- The name of a bit op. -/
def Op.name : Op → String
  | .low _ => "bit.low"
  | .int => "bit.int"

/-- The bit op with this name, at these operand and result types. -/
def Op.decode (n : String) (as : List Attr) (ts rs : List (Core.Ty ⊕ Ty)) : Option Op :=
  match as, ts, rs with
  | [], [.inl (.int w)], [.inr .bit] => if n = "bit.low" then some (.low w) else none
  | [], [.inr .bit], [.inl (.int 1)] => if n = "bit.int" then some .int else none
  | _, _, _ => none

/-- Writes a type: the core's as the core does, and `bit.bit`. -/
def tyAttr : Core.Ty ⊕ Ty → Attr
  | .inl t => t.attr
  | .inr .bit => .word "bit.bit"

/-- Reads a type: a type of the name `bit` is `bit.bit` or none, and every
other type is the core's. -/
def decodeTy (a : Attr) : Option (Core.Ty ⊕ Ty) :=
  if a.dialect? = some "bit" then
    match a with
    | .word "bit.bit" => some (.inr .bit)
    | _ => none
  else (Core.Ty.decode a).map .inl

instance : DialectText BitDialect where
  opName := Op.name
  opAttrs _ := []
  decodeOp := Op.decode
  tyAttr := tyAttr
  decodeTy := decodeTy

/-! # Validation -/

/-- The bit dialect accepts the core's valid types and its own. -/
def ValidTy : Core.Ty ⊕ Ty → Prop
  | .inl t => t.Valid
  | .inr _ => True

instance : DecidablePred ValidTy
  | .inl t => inferInstanceAs (Decidable t.Valid)
  | .inr _ => inferInstanceAs (Decidable True)

instance : DialectValidation BitDialect where
  validTy := ValidTy
  symbolRefs _ := []
  validOp _ _ := True
  validFunc _ _ _ := True

instance : DecidableDialectValidation BitDialect where
  decValidTy t := inferInstanceAs (Decidable (ValidTy t))
  decValidOp _ _ := inferInstanceAs (Decidable True)
  decValidFunc _ _ _ := inferInstanceAs (Decidable True)

/-! # Execution -/

/-- The low bit of an integer, and poison of poison. -/
def lowBit (w : Nat) : PoisonOr (BitVec w) → PoisonOr Bool
  | .value x => .value (x.getLsbD 0)
  | .poison => .poison

/-- A bit as an `i1`, and poison of poison. -/
def toInt : PoisonOr Bool → PoisonOr (BitVec 1)
  | .value b => .value (BitVec.ofBool b)
  | .poison => .poison

#guard lowBit 8 (.value 0b101) == .value true && lowBit 8 (.value 0b100) == .value false
#guard toInt (.value true) == .value 1 && toInt .poison == .poison

/-- The rule of each bit op, in the set monad. -/
def Op.denote : (op : Op) → HVector toType (Fir.sig (d := BitDialect) op) →
    SetM (HVector toType (Fir.returnTypes (d := BitDialect) op))
  | .low w, .cons a .nil => pure (.cons (lowBit w a) .nil)
  | .int, .cons a .nil => pure (.cons (toInt a) .nil)

/-- No bit op is a terminator, so no bit op has an exit. -/
instance : DialectDenote BitDialect SetM where
  denote := Op.denote
  exit _ _ := fun _ => False

/-- Both bit ops propagate poison, and both are pure: each gives a defined
result on a defined operand and is never UB. The bit dialect has no memory
of its own: its memories are the core's. -/
instance : DialectEffects BitDialect :=
  ⟨DialectEffects.Mem CoreDialect ⊕ Empty, fun _ => .propagates, fun _ => {}⟩

/-- The bit dialect's memories are the core's, and none of its own. -/
instance : DialectMemOver CoreDialect BitExt := ⟨Empty, id, id, fun _ => rfl, fun _ => rfl⟩

/-- No bit op calls a function. -/
instance : DialectCall BitDialect := ⟨fun _ => none⟩

/-- No bit op touches memory: at every naming of its memories, it runs by
its rule in the set monad and keeps the memories. -/
instance : DialectMemDenote BitDialect := DialectMemDenote.ofSetM

/-- The bit dialect's semantics with memory lifts its semantics in the set
monad. -/
instance : LiftsSetM BitDialect := DialectMemDenote.ofSetM_liftsSetM

/-! # The bit dialect's text is lawful -/

/-- The bit dialect's text meets the seven laws. -/
theorem lawfulDialectText : LawfulDialectText BitDialect where
  decodeOp_encode
    | .low _ => by simp [opName, opAttrs, decodeOp, Op.name, Op.decode, sig, returnTypes]
    | .int => by simp [opName, opAttrs, decodeOp, Op.name, Op.decode, sig, returnTypes]
  encode_decodeOp n as ts rs o h := by
    change Op.decode n as ts rs = some o at h
    unfold Op.decode at h
    split at h
    · split at h
      · rename_i hn
        cases h
        exact ⟨hn.symm, rfl, rfl, rfl⟩
      · cases h
    · split at h
      · rename_i hn
        cases h
        exact ⟨hn.symm, rfl, rfl, rfl⟩
      · cases h
    · cases h
  decodeTy_encode
    | .inl t, hv => by
      change decodeTy t.attr = _
      simp [decodeTy, OverCore.core_dialect? t, Core.Ty.decode_attr t hv]
    | .inr .bit, _ => by decide
  encode_decodeTy a t h := by
    change decodeTy a = some t at h
    unfold decodeTy at h
    split at h
    · split at h
      · cases h; rfl
      · cases h
    · obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp h
      exact Core.Ty.attr_decode ht'
  opName_isWord
    | .low _ => (by decide : isWord "bit.low")
    | .int => (by decide : isWord "bit.int")
  opAttrs_writable _ := trivial
  tyAttr_isType
    | .inl t, hv => Core.Ty.attr_isType t hv
    | .inr .bit, _ => (by decide : isWord "bit.bit")

instance : LawfulDialectText BitDialect := lawfulDialectText

/-- The bit dialect writes its ops and its type under the name `bit`. -/
instance : LawfulDialectName CoreDialect BitExt where
  opName_named
    | .low _ => (by decide : wordDialect "bit.low" = some "bit")
    | .int => (by decide : wordDialect "bit.int" = some "bit")
  opAttrs_mem _ _ h := nomatch h
  tyAttr_named | .bit, _ => (by decide : wordDialect "bit.bit" = some "bit")
  tyAttr_mem
    | .bit, _, x, h => by
      have : x = "bit" := by simpa [tyAttr, Attr.dialects, DialectText.tyAttr, wordDialect] using h
      subst this
      exact List.mem_singleton_self _
  kind_named _ h := nomatch h

/-! # The bit dialect is lawful -/

/-- `lowBit` keeps refinement. -/
theorem lowBit_mono {w : Nat} {a a' : PoisonOr (BitVec w)} (h : PoisonOr.IsRefinedBy a a') :
    PoisonOr.IsRefinedBy (lowBit w a) (lowBit w a') := by
  cases a <;> cases a' <;> simp_all [lowBit, PoisonOr.IsRefinedBy]

/-- `toInt` keeps refinement. -/
theorem toInt_mono {a a' : PoisonOr Bool} (h : PoisonOr.IsRefinedBy a a') :
    PoisonOr.IsRefinedBy (toInt a) (toInt a') := by
  cases a <;> cases a' <;> simp_all [toInt, PoisonOr.IsRefinedBy]

/-- Each bit op propagates poison: a poison operand gives a poison result,
and no bit op is UB. -/
theorem propagates (o : Op) : PropagatesPoison (d := BitDialect) o where
  poisonOut args hany _ hden := by
    cases o <;> match args, hany with
      | .cons a .nil, .inl h =>
        cases hden
        change a = .poison at h
        subst h
        exact ⟨rfl, trivial⟩
  ubByOwnRules args _ _ hden := by
    cases o <;> match args with
      | .cons _ .nil => exact nomatch hden

/-- Each bit op is monotone. -/
theorem monotone (o : Op) : OpMonotone (d := BitDialect) o := by
  intro args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  cases o <;> match args, args', h with
    | .cons a .nil, .cons a' .nil, ⟨ha, _⟩ =>
      intro e he
      subst he
      first
        | exact ⟨_, rfl, lowBit_mono ha, trivial⟩
        | exact ⟨_, rfl, toInt_mono ha, trivial⟩

/-- The bit dialect is lawful: each op propagates poison, returns a result
on a defined operand, and is total and monotone. -/
instance lawful : LawfulDialectPoison BitDialect where
  poison_isRefinedBy {t} := match t with
    | .inl _ => fun _ => Core.Ty.poison_isRefinedBy
    | .inr .bit => fun _ p _ hp => by
      change p = .poison at hp
      subst hp
      trivial
  propagates o _ _ := propagates o
  returnsOnDefined
    | .low _, _, _ => ⟨.cons (.value 0) .nil, (by rintro (h | h) <;> cases h), _, rfl⟩
    | .int, _, _ => ⟨.cons (.value true) .nil, (by rintro (h | h) <;> cases h), _, rfl⟩
  total
    | .low _, _, _ => fun | .cons _ .nil => ⟨fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩
    | .int, _, _ => fun | .cons _ .nil => ⟨fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩
  monotone o _ _ := monotone o

/-- The bit dialect is lawful in its effects: both ops are never UB, give a
defined result on a defined operand, are not terminators, and touch no
memory. -/
theorem lawfulDialectEffects : LawfulDialectEffects BitDialect where
  neverUB o _ _ _ := NeverUB.ofSetM fun args _ => by
    cases o <;> match args with
      | .cons _ .nil => exact ⟨fun _ h => (by cases h), fun h => nomatch h⟩
  makesNoPoison o _ _ _ := MakesNoPoison.ofSetM fun _ args hd _ hr => by
    cases o <;> match args, hd, hr with
      | .cons a .nil, hd, hr =>
        cases a with
        | poison => exact absurd (.inl rfl) hd
        | value x =>
          cases hr
          rintro (h | h) <;> cases h
  notControl _ _ := rfl
  writesNot := DialectMemDenote.ofSetM_writesNot
  readsNot := DialectMemDenote.ofSetM_readsNot
  allocatesNot := DialectMemDenote.ofSetM_allocatesNot

instance : LawfulDialectEffects BitDialect := lawfulDialectEffects

end Bit

end FirTest
