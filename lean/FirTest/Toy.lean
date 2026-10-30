import Fir

/-!
A test-only dialect. It shows that a new dialect needs no change to the
interpreter, the parser or the printer (G0): it gives its op's signature,
text, validation rule and execution rule as instances of the spec's
classes, and nothing else.

Its one op works on the core dialect's integers, so the toy dialect has no
types of its own: `%m: iN = toy.mask K %x` keeps the low `K` bits of `%x`
and clears the others. Its own rule asks `K ≤ N`, a rule beyond its
signature, so `toy.mask 9` at `i8` decodes and validation rejects it, as
`zext` from `i8` to `i8` decodes and validation rejects it. A poison operand
gives poison.

Test dialects name their ops `toy.` and a word (ADR-2026-10-30-1146), so a
toy op never has the name of a core op.
-/

namespace FirTest.Toy

open Fir

/-- An op instance of the toy dialect: `mask w k` keeps the low `k` bits of
an `iN` with `N = w`. -/
inductive Op where
  | mask (w k : Nat)
  deriving Repr, DecidableEq

end FirTest.Toy

namespace FirTest

open Fir

/-- The toy dialect: its op, over the core dialect's types. -/
abbrev ToyDialect : Dialect := ⟨Toy.Op, Core.Ty⟩

namespace Toy

/-- The operand types of a toy op. -/
def Op.sig : Op → List Core.Ty
  | .mask w _ => [.int w]

/-- The result types of a toy op. -/
def Op.returnTypes : Op → List Core.Ty
  | .mask w _ => [.int w]

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
def Op.decode (n : String) (as : List Attr) (ts rs : List Core.Ty) : Option Op :=
  if n = "toy.mask" then
    match as, ts, rs with
    | [.int k], [.int a], [.int b] => if 0 ≤ k ∧ a = b then some (.mask a k.toNat) else none
    | _, _, _ => none
  else none

/-- The toy dialect writes its types as the core dialect does: they are the
core dialect's. -/
instance : DialectText ToyDialect where
  opName := Op.name
  opAttrs := Op.attrs
  decodeOp := Op.decode
  tyAttr := Core.Ty.attr
  decodeTy := Core.Ty.decode

/-! # Validation -/

/-- The toy dialect's own rule: a mask keeps at most as many bits as its
type has. -/
def Op.Valid : Op → Prop
  | .mask w k => k ≤ w

instance : DialectValidation ToyDialect where
  validTy := Core.Ty.Valid
  symbolRefs _ := []
  validOp _ := Op.Valid

instance : DecidablePred Op.Valid := fun o => by
  cases o <;> unfold Op.Valid <;> infer_instance

instance : DecidableDialectValidation ToyDialect where
  decValidTy t := inferInstanceAs (Decidable (Core.Ty.Valid t))
  decValidOp _ o := inferInstanceAs (Decidable (Op.Valid o))

/-! # Execution -/

/-- `toy.mask` declares that it propagates poison, as its rule does: a
poison operand gives a poison result, and it is never UB. -/
instance : DialectPoison ToyDialect := ⟨fun _ => .propagates⟩

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

/-! # The toy dialect's text is lawful -/

/-- Every toy op decodes from its name and attributes, at its operand and
result types. -/
theorem Op.decode_encode (o : Op) : Op.decode o.name o.attrs o.sig o.returnTypes = some o := by
  cases o
  simp [Op.decode, Op.name, Op.attrs, Op.sig, Op.returnTypes]

/-- A toy op decodes only from its own name, attributes, operand types and
result types. -/
theorem Op.encode_decode {n : String} {as : List Attr} {ts rs : List Core.Ty} {o : Op}
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
  decodeTy_encode := Core.Ty.decode_attr
  encode_decodeTy _ _ h := Core.Ty.attr_decode h
  opName_isWord | .mask .. => (by decide : isWord "toy.mask")
  opAttrs_writable | .mask .. => ⟨trivial, trivial⟩
  tyAttr_isType := Core.Ty.attr_isType

instance : LawfulDialectText ToyDialect := lawfulDialectText

end Toy

end FirTest
