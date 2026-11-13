import Fir.Core.Text

/-!
# The float ops read back from their spelling

Each float op of arithmetic, each bit cast and each conversion decodes
only from its own name, its attributes and its operand and result types:
`fadd` and the other ops of two operands, `fneg`, `fabs` and `sqrt`,
`fma`, `bitcast` in either direction, `sitofp` and `uitofp`, `fpext`,
`fptrunc`, `fptosi` and `fptoui`. The proof that the core dialect's text
is lawful, in the next section, uses these facts op by op; they are kept
here, beside how the float ops are written, so that each section stays
one that a reader takes in whole.
-/

namespace Fir.Core

/-- `fadd`, `fsub`, `fmul`, `fdiv`, `frem` and `fmod` decode only from
their own name, attributes, operand types and result type. -/
theorem decodeFBin_eq {o : FBin} {as : List Attr} {ts rs : List Ty} {op : Op}
    (h : decodeFBin o as ts rs = some op) :
    op.name = o.name ∧ op.attrs = as ∧ op.sig = ts ∧ op.returnTypes = rs := by
  unfold decodeFBin at h
  split at h
  · rename_i hok
    obtain ⟨⟨e, m⟩, hf, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨rfl, rfl⟩ := floatOpFormat_eq hf
    exact ⟨rfl, FBin.attrs_of_attrsOk hok, rfl, rfl⟩
  · cases h

/-- `fneg`, `fabs` and `sqrt` decode only from their own name, attributes,
operand type and result type. -/
theorem decodeFUnary_eq {o : FUnary} {as : List Attr} {ts rs : List Ty} {op : Op}
    (h : decodeFUnary o as ts rs = some op) :
    op.name = o.name ∧ op.attrs = as ∧ op.sig = ts ∧ op.returnTypes = rs := by
  unfold decodeFUnary at h
  split at h
  · rename_i hok
    obtain ⟨⟨e, m⟩, hf, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨rfl, rfl⟩ := floatOpFormat_eq hf
    exact ⟨rfl, FUnary.attrs_of_attrsOk hok, rfl, rfl⟩
  · cases h

/-- `fma` decodes only from its own name, attributes, operand types and
result type. -/
theorem decodeFma_eq {as : List Attr} {ts rs : List Ty} {op : Op}
    (h : decodeFma as ts rs = some op) :
    op.name = "fma" ∧ op.attrs = as ∧ op.sig = ts ∧ op.returnTypes = rs := by
  unfold decodeFma at h
  split at h
  · rename_i hr
    obtain ⟨⟨e, m⟩, hf, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨rfl, rfl⟩ := floatOpFormat_eq hf
    exact ⟨rfl, (eq_of_isRoundAttrs hr).symm, rfl, rfl⟩
  · cases h

/-- `bitcast` decodes only from its own name, attributes, operand type and
result type, in either direction. -/
theorem decodeBitcast_eq {as : List Attr} {ts rs : List Ty} {op : Op}
    (h : decodeBitcast as ts rs = some op) :
    op.name = "bitcast" ∧ op.attrs = as ∧ op.sig = ts ∧ op.returnTypes = rs := by
  unfold decodeBitcast at h
  split at h <;> (try cases h)
  all_goals
    split at h
    · rename_i hw
      obtain ⟨ha, rfl⟩ := hw
      cases h
      exact ⟨rfl, (List.isEmpty_iff.mp ha).symm, rfl, rfl⟩
    · cases h

/-- `sitofp` and `uitofp` decode only from their own name, attributes,
operand type and result type. -/
theorem decodeIntToFloat_eq {signed : Bool} {as : List Attr} {ts rs : List Ty} {op : Op}
    (h : decodeIntToFloat signed as ts rs = some op) :
    op.name = (if signed then "sitofp" else "uitofp") ∧ op.attrs = as ∧ op.sig = ts ∧
      op.returnTypes = rs := by
  unfold decodeIntToFloat at h
  split at h
  · split at h
    · rename_i hr
      cases h
      cases signed <;> exact ⟨rfl, (eq_of_isRoundAttrs hr).symm, rfl, rfl⟩
    · cases h
  · cases h

/-- `fpext` decodes only from its own name, attributes, operand type and
result type. -/
theorem decodeFpext_eq {as : List Attr} {ts rs : List Ty} {op : Op}
    (h : decodeFpext as ts rs = some op) :
    op.name = "fpext" ∧ op.attrs = as ∧ op.sig = ts ∧ op.returnTypes = rs := by
  unfold decodeFpext at h
  split at h
  · split at h
    · rename_i ha
      cases h
      exact ⟨rfl, (List.isEmpty_iff.mp ha).symm, rfl, rfl⟩
    · cases h
  · cases h

/-- `fptrunc` decodes only from its own name, attributes, operand type and
result type. -/
theorem decodeFptrunc_eq {as : List Attr} {ts rs : List Ty} {op : Op}
    (h : decodeFptrunc as ts rs = some op) :
    op.name = "fptrunc" ∧ op.attrs = as ∧ op.sig = ts ∧ op.returnTypes = rs := by
  unfold decodeFptrunc at h
  split at h
  · split at h
    · rename_i hr
      cases h
      exact ⟨rfl, (eq_of_isRoundAttrs hr).symm, rfl, rfl⟩
    · cases h
  · cases h

/-- `fptosi` and `fptoui` decode only from their own name, attributes,
operand type and result type. -/
theorem decodeFloatToInt_eq {signed : Bool} {as : List Attr} {ts rs : List Ty} {op : Op}
    (h : decodeFloatToInt signed as ts rs = some op) :
    op.name = (if signed then "fptosi" else "fptoui") ∧ op.attrs = as ∧ op.sig = ts ∧
      op.returnTypes = rs := by
  unfold decodeFloatToInt at h
  split at h
  · split at h
    · rename_i ha
      cases h
      cases signed <;> exact ⟨rfl, (List.isEmpty_iff.mp ha).symm, rfl, rfl⟩
    · cases h
  · cases h

end Fir.Core
