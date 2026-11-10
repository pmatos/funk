import Fir.Sum.Names
import Fir.Core.Text
import Fir.Core.Validation

/-!
The core dialect writes bare words: no name of a core op, no word of a core
op's attributes and no core type holds a `.` (ADR-2026-11-09-1543). So its
words name no dialect, and its dialect set is empty. Every sum is built on
the core, and its words name only dialects of the sum's set.
-/

namespace Fir

/-- A word that holds no `.` names no dialect. -/
theorem wordDialect_eq_none {w : String} (h : '.' ∉ w.toList) : wordDialect w = none := by
  simp [wordDialect, h]

namespace Core

/-- The core dialect's set is empty: its words are bare. -/
instance instDialectSet : DialectSet CoreDialect := ⟨[]⟩

/-- Every dialect's name is new to the core, whose set is empty: any
dialect can be added to the core. -/
theorem name_new (e : Dialect) [DialectName e] : name e ∉ names CoreDialect :=
  List.not_mem_nil

/-- The name of a core op names no dialect. -/
theorem opName_bare (o : Op) : wordDialect (opName (d := CoreDialect) o) = none := by
  apply wordDialect_eq_none
  cases o <;> simp only [opName, Op.name] <;> decide

/-- No word of a core op's attributes names a dialect. -/
theorem opAttrs_bare (o : Op) : Attr.dialectsAll (opAttrs (d := CoreDialect) o) = [] := by
  have hp (p : Pred) : wordDialect p.name = none := by
    apply wordDialect_eq_none
    cases p <;> decide
  have hw (f : WrapFlags) : Attr.dialectsAll f.attrs = [] := by
    rcases f with ⟨_ | _, _ | _⟩ <;>
      simp [WrapFlags.attrs, Attr.dialectsAll, Attr.dialects, wordDialect]
  cases o with
  | const w v =>
    simp only [opAttrs, Op.attrs, Attr.dialectsAll, List.append_nil]
    unfold constAttr
    split
    · split <;> simp [Attr.dialects, wordDialect]
    · simp [Attr.dialects]
  | icmp p w => simp [opAttrs, Op.attrs, Attr.dialectsAll, Attr.dialects, hp]
  | add _ f | sub _ f | mul _ f => exact hw f
  | sdiv _ e | udiv _ e =>
    cases e <;> simp [opAttrs, Op.attrs, Attr.dialectsAll, Attr.dialects, wordDialect]
  | call => simp [opAttrs, Op.attrs, Attr.dialectsAll, Attr.dialects]
  | _ => rfl

/-- No core type names a dialect. -/
theorem tyAttr_bare (t : Ty) : (tyAttr (d := CoreDialect) t).dialects = [] := by
  cases t with
  | int w =>
    simp only [tyAttr, Ty.attr, Attr.dialects, Option.toList_eq_nil_iff]
    apply wordDialect_eq_none
    intro h
    simp only [String.toList_append, List.mem_append] at h
    rcases h with h | h
    · exact absurd h (by decide)
    · simp only [toString, Nat.repr, String.toList_ofList] at h
      exact absurd (Nat.isDigit_of_mem_toDigits (by decide) (by decide) h) (by decide)
  | ptr => simp [tyAttr, Ty.attr, Attr.dialects, wordDialect]

/-- The core dialect's words name no dialect. -/
theorem lawfulDialectSet : LawfulDialectSet CoreDialect where
  opName_mem o x h := by simp [opName_bare o] at h
  opAttrs_mem o x h := by simp [opAttrs_bare o] at h
  tyAttr_mem t _ x h := by simp [tyAttr_bare t] at h
  kind_mem _ h := nomatch h

instance instLawfulDialectSet : LawfulDialectSet CoreDialect := lawfulDialectSet

end Core

end Fir
