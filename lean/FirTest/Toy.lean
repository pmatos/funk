import FirTest.OverCore

/-!
A test-only dialect. It shows that a new dialect needs no change to the
interpreter, the parser or the printer (G0): it gives its op's signature,
text, validation rule and execution rule as instances of the spec's
classes, and nothing else.

It extends the core dialect: its one op works on the core dialect's
integers, which it names as its base's types, and it has no types of its
own: `%m: iN = toy.mask K %x` keeps the low `K` bits of `%x`
and clears the others. Its own rule asks `K ≤ N`, a rule beyond its
signature, so `toy.mask 9` at `i8` decodes and validation rejects it, as
`zext` from `i8` to `i8` decodes and validation rejects it. A poison operand
gives poison.

Its name is `toy` (ADR-2026-10-30-1146), so it writes its op as `toy.` and
a word, and in the sum of the core and the toy dialect each word goes to its
own side (ADR-2026-11-09-1543).
-/

namespace FirTest.Toy

/-- An op instance of the toy dialect: `mask w k` keeps the low `k` bits of
an `iN` with `N = w`. -/
inductive Op where
  | mask (w k : Nat)
  deriving Repr, DecidableEq

end FirTest.Toy

namespace FirTest

open Fir

/-- The toy dialect: its op, over the core dialect's types. -/
abbrev ToyDialect : Dialect := OverCore Toy.Op

namespace Toy

/-- The operand types of a toy op. -/
def Op.sig : Op → List (Core.Ty ⊕ Empty)
  | .mask w _ => [.inl (.int w)]

/-- The result types of a toy op. -/
def Op.returnTypes : Op → List (Core.Ty ⊕ Empty)
  | .mask w _ => [.inl (.int w)]

instance : DialectSignature ToyDialect where
  sig := Op.sig
  returnTypes := Op.returnTypes
  isTerminator _ := false
  succCount _ := 0

/-! # Text -/

/-- The name of a toy op. -/
def Op.name : Op → String
  | .mask .. => "toy.mask"

/-- The attributes of a toy op: the number of bits it keeps. -/
def Op.attrs : Op → List Attr
  | .mask _ k => [.int k]

/-- The toy op with this name and these attributes, at these operand and
result types. -/
def Op.decode (n : String) (as : List Attr) (ts rs : List (Core.Ty ⊕ Empty)) : Option Op :=
  if n = "toy.mask" then
    match as, ts, rs with
    | [.int k], [.inl (.int a)], [.inl (.int b)] => if 0 ≤ k ∧ a = b then some (.mask a k.toNat) else none
    | _, _, _ => none
  else none

/-- The toy dialect writes its types as the core dialect does: they are the
core dialect's. -/
instance : DialectText ToyDialect where
  opName := Op.name
  opAttrs := Op.attrs
  decodeOp := Op.decode
  tyAttr := OverCore.tyAttr
  decodeTy := OverCore.decodeTy

/-! # Validation -/

/-- The toy dialect's own rule: a mask keeps at most as many bits as its
type has. -/
def Op.Valid : Op → Prop
  | .mask w k => k ≤ w

instance : DialectValidation ToyDialect where
  validTy := OverCore.ValidTy
  symbolRefs _ := []
  validOp _ := Op.Valid
  validFunc _ _ _ := True

instance : DecidablePred Op.Valid := fun o => by
  cases o <;> unfold Op.Valid <;> infer_instance

instance : DecidableDialectValidation ToyDialect where
  decValidTy t := inferInstanceAs (Decidable (OverCore.ValidTy t))
  decValidOp _ o := inferInstanceAs (Decidable (Op.Valid o))
  decValidFunc _ _ _ := inferInstanceAs (Decidable True)

/-! # Execution -/

/-- `toy.mask` declares its effects through the effect class: it propagates
poison, as its rule does, and it is pure, since its rule gives a defined
result on a defined operand and is never UB. The toy dialect has no memory,
so its memories have no names. -/
instance : DialectEffects ToyDialect := ⟨Empty, fun _ => .propagates, fun _ => {}⟩

/-- `toy.mask w k`: the low `k` bits of a value, and poison of poison. -/
def maskValue (w k : Nat) : PoisonOr (BitVec w) → PoisonOr (BitVec w)
  | .value x => .value ((x.setWidth k).setWidth w)
  | .poison => .poison

#guard maskValue 8 3 (.value 0b11010110) == .value 0b110
#guard maskValue 8 0 (.value (-1)) == .value 0 && maskValue 8 8 (.value (-1)) == .value (-1)
#guard maskValue 8 3 .poison == .poison

/-- The rule of each toy op, in any monad. -/
def Op.denote {m : Type → Type} [Monad m] : (op : Op) →
    HVector toType (Fir.sig (d := ToyDialect) op) →
    m (HVector toType (Fir.returnTypes (d := ToyDialect) op))
  | .mask w k, .cons a .nil => pure (.cons (maskValue w k a) .nil)

/-- The toy dialect's semantics in the set monad. No toy op is a terminator,
so no toy op has an exit: its `exit` has no outcome, as a core op that is
not a terminator has none. -/
instance : DialectDenote ToyDialect SetM where
  denote := Op.denote
  exit _ _ := fun _ => False

/-- No toy op calls a function. -/
instance : DialectCall ToyDialect := ⟨fun _ => none⟩

/-- The toy dialect is lawful in its effects: `toy.mask` is pure, and it is
never UB, gives a defined result on a defined operand, and is not a
terminator. -/
theorem lawfulDialectEffects : LawfulDialectEffects ToyDialect where
  neverUB
    | .mask .., _, _, _ => fun
      | .cons _ .nil, _ => ⟨fun _ h => (by cases h), fun h => (nomatch h)⟩
  makesNoPoison
    | .mask w k, _, _, _ => fun _ args hd _ hr => match args, hd, hr with
      | .cons a .nil, hd, hr => by
        cases a with
        | poison => exact absurd (.inl rfl) hd
        | value x =>
          cases hr
          rintro (h | h) <;> cases h
  notControl _ _ := rfl

instance : LawfulDialectEffects ToyDialect := lawfulDialectEffects

/-! # The toy dialect's text is lawful -/

/-- Every toy op decodes from its name and attributes, at its operand and
result types. -/
theorem Op.decode_encode (o : Op) : Op.decode o.name o.attrs o.sig o.returnTypes = some o := by
  cases o
  simp [Op.decode, Op.name, Op.attrs, Op.sig, Op.returnTypes]

/-- A toy op decodes only from its own name, attributes, operand types and
result types. -/
theorem Op.encode_decode {n : String} {as : List Attr} {ts rs : List (Core.Ty ⊕ Empty)} {o : Op}
    (h : Op.decode n as ts rs = some o) :
    o.name = n ∧ o.attrs = as ∧ o.sig = ts ∧ o.returnTypes = rs := by
  unfold Op.decode at h
  split at h
  · rename_i hn
    subst hn
    split at h
    · split at h
      · rename_i k a b hk
        cases h
        obtain ⟨hk, rfl⟩ := hk
        exact ⟨rfl, by simp [Op.attrs, Int.toNat_of_nonneg hk], rfl, rfl⟩
      · cases h
    · cases h
  · cases h

/-- The toy dialect's text meets the seven laws. Its types are the core
dialect's, so their laws are the core dialect's. -/
theorem lawfulDialectText : LawfulDialectText ToyDialect where
  decodeOp_encode := Op.decode_encode
  encode_decodeOp _ _ _ _ _ h := Op.encode_decode h
  decodeTy_encode := OverCore.decodeTy_attr
  encode_decodeTy _ _ h := OverCore.attr_decodeTy h
  opName_isWord | .mask .. => (by decide : isWord "toy.mask")
  opAttrs_writable | .mask .. => ⟨trivial, trivial⟩
  tyAttr_isType := OverCore.attr_isType

instance : LawfulDialectText ToyDialect := lawfulDialectText

/-! # The toy dialect's words -/

/-- The toy dialect writes its op under its name, `toy`, its op's attribute
is a number, and it has no type of its own. -/
instance lawfulDialectName : LawfulDialectName CoreDialect (Ext Op) where
  opName_named | .mask .. => (by decide : wordDialect "toy.mask" = some "toy")
  opAttrs_mem | .mask .., _, h => by simp [opAttrs, Op.attrs, Attr.dialectsAll, Attr.dialects] at h
  tyAttr_named t := t.elim
  tyAttr_mem t := t.elim

/-! # The toy dialect is lawful -/

/-- `maskValue` keeps refinement. -/
theorem maskValue_mono {w k : Nat} {a a' : PoisonOr (BitVec w)} (h : PoisonOr.IsRefinedBy a a') :
    PoisonOr.IsRefinedBy (maskValue w k a) (maskValue w k a') := by
  cases a <;> cases a' <;> simp_all [maskValue, PoisonOr.IsRefinedBy]

/-- `toy.mask` is monotone. -/
theorem mask_monotone (w k : Nat) : OpMonotone (d := ToyDialect) (.mask w k) := by
  intro args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons _ .nil, .cons _ .nil, h =>
    intro e he
    subst he
    exact ⟨_, rfl, maskValue_mono h.1, trivial⟩

/-- The toy dialect is lawful: `toy.mask` propagates poison, returns a
result on a defined operand, and is total and monotone, at every
instance. -/
instance lawfulPoison : LawfulDialectPoison ToyDialect where
  poison_isRefinedBy {t} := match t with
    | .inl _ => fun _ => Core.Ty.poison_isRefinedBy
    | .inr t => t.elim
  propagates
    | .mask .., _, _ => {
        poisonOut := fun
          | .cons a .nil, .inl h, _, hden => by
            cases hden
            change a = .poison at h
            subst h
            exact ⟨rfl, trivial⟩
        ubByOwnRules := fun | .cons _ .nil, _, _, hden => nomatch hden }
  returnsOnDefined
    | .mask .., _, _ => ⟨.cons (.value 0) .nil, (by rintro (h | h) <;> cases h), _, rfl⟩
  total
    | .mask .., _, _ => fun | .cons _ .nil => ⟨fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩
  monotone | .mask w k, _, _ => mask_monotone w k

end Toy

end FirTest
