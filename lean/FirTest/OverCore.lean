import Fir

/-!
What the test dialects over the core share. Each one is an extension of the
core dialect with the name `toy` (ADR-2026-10-30-1146) and no types of its
own: its ops are used at the core's integers, which it names as its base's
types, `.inl t` (ADR-2026-11-09-1543). It writes, reads and accepts those
types as the core does, through the helpers below.
-/

namespace FirTest

open Fir

/-- An extension of the core dialect with these ops and no types of its
own. -/
abbrev Ext (Op : Type) : Dialect := ⟨Op, Empty⟩

/-- The extension `Ext Op` over the core: its ops, at the core's types. -/
abbrev OverCore (Op : Type) : Dialect := CoreDialect.over (Ext Op)

/-- The sum of the core and the extension `Ext Op`. -/
abbrev CoreSum (Op : Type) : Dialect := CoreDialect ⊞ Ext Op

/-- A test dialect's name. -/
instance (Op : Type) : DialectName (Ext Op) := ⟨"toy"⟩

namespace OverCore

/-- An extension over the core writes the core's types as the core does. -/
def tyAttr : Core.Ty ⊕ Empty → Attr
  | .inl t => t.attr
  | .inr e => e.elim

/-- An extension over the core reads the core's types as the core does. -/
def decodeTy (a : Attr) : Option (Core.Ty ⊕ Empty) := (Core.Ty.decode a).map .inl

/-- An extension over the core accepts the core's valid types. -/
def ValidTy : Core.Ty ⊕ Empty → Prop
  | .inl t => t.Valid
  | .inr e => e.elim

instance : DecidablePred ValidTy
  | .inl t => inferInstanceAs (Decidable t.Valid)
  | .inr e => e.elim

theorem decodeTy_attr (t : Core.Ty ⊕ Empty) (h : ValidTy t) : decodeTy (tyAttr t) = some t := by
  cases t with
  | inl t => simp [decodeTy, tyAttr, Core.Ty.decode_attr t h]
  | inr e => exact e.elim

theorem attr_decodeTy {a : Attr} {t : Core.Ty ⊕ Empty} (h : decodeTy a = some t) :
    tyAttr t = a := by
  obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp h
  exact Core.Ty.attr_decode ht'

theorem attr_isType (t : Core.Ty ⊕ Empty) (h : ValidTy t) : (tyAttr t).IsType := by
  cases t with
  | inl t => exact Core.Ty.attr_isType t h
  | inr e => exact e.elim

/-- The core's types name no dialect, as the core writes them. -/
theorem tyAttr_dialects (t : Core.Ty ⊕ Empty) : (tyAttr t).dialects = [] := by
  cases t with
  | inl t => exact Core.tyAttr_bare t
  | inr e => exact e.elim

/-- A core type names no dialect, so a dialect over the core reads it as
the core's. -/
theorem core_dialect? (t : Core.Ty) : t.attr.dialect? = none := by
  cases h : t.attr.dialect? with
  | none => rfl
  | some x =>
    have := Attr.dialect?_mem h
    rw [show t.attr = Fir.tyAttr (d := CoreDialect) t from rfl, Core.tyAttr_bare] at this
    cases this

end OverCore

end FirTest
