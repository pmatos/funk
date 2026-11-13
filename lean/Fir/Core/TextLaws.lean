import Std.Data.String.ToNat
import Fir.Core.Text
import Fir.Core.Validation
import Fir.Text.RoundTrip
import Fir.Core.TypeTextLaws
import Fir.Core.FloatTextLaws
import Fir.Core.FloatOpTextLaws

/-!
The core dialect's text is lawful: it meets the seven laws of a lawful
text, for all 40 of its ops and every type. The laws are proved for every
op instance, valid or not: every width, `0` included, every predicate, every
combination of flags, `true` and `false` at `i1`, every float constant at
every format, and `ret` and `call` with any number of operands and results. A type reads back from how it is
written, and is written as a type, for every valid type, `i1` to
`i16777215` and every valid float format, by its alias or as
`float(e, m)`, as the laws ask; and every type that reads back is written
as it was read.

With the laws, every valid core module is well formed, by the last theorem
of the previous section, so it can be written and read back. With the round
trip, proved later in this chapter, it follows that two different valid
core modules never print the same text.

The round trip covers every dialect whose text is lawful at once, and uses
nothing of a dialect but these laws. So a change to the core op set, such as
a new op or a new flag, extends the proofs below, case by case, and does not
rework the proof of the round trip; the part "What a new dialect or a new core
op needs" of the section "The round trip, proved", later in this chapter,
says how the round trip extends.

This section proves, in order: facts about attributes; that each op instance
reads back from its spelling, and only from it; that ops are written as
tokens; and the laws. The section before it proves the same of types.
-/

namespace Fir.Core

/-! # Attributes -/

/-- Decoding the flags of `add`, `sub` or `mul` gives them back. -/
theorem decodeWrap_attrs (f : WrapFlags) : decodeWrap f.attrs = some f := by
  obtain ⟨nuw, nsw⟩ := f
  cases nuw <;> cases nsw <;> rfl

/-- Flags decode only from their own spelling. -/
theorem attrs_of_decodeWrap {as : List Attr} {f : WrapFlags} (h : decodeWrap as = some f) :
    f.attrs = as := by
  unfold decodeWrap at h
  split at h <;> (try cases h) <;> rfl

/-- The flag of `sdiv` or `udiv` decodes only from its own spelling. -/
theorem attrs_of_decodeExact {as : List Attr} {e : Bool} (h : decodeExact as = some e) :
    (if e then [Attr.word "exact"] else []) = as := by
  unfold decodeExact at h
  split at h <;> (try cases h) <;> rfl

/-- Each predicate is found by its name. -/
theorem find_pred_name (p : Pred) : Pred.all.find? (·.name == p.name) = some p := by
  cases p <;> rfl

/-- A predicate found by a name has that name. -/
theorem name_of_find_pred {s : String} {p : Pred} (h : Pred.all.find? (·.name == s) = some p) :
    p.name = s := by
  simpa using List.find?_some h

/-- Each float predicate is found by its name. -/
theorem find_fpred_name (p : FPred) : FPred.all.find? (·.name == p.name) = some p := by
  cases p <;> rfl

/-- A float predicate found by a name has that name. -/
theorem name_of_find_fpred {s : String} {p : FPred} (h : FPred.all.find? (·.name == s) = some p) :
    p.name = s := by
  simpa using List.find?_some h

/-- At every width but 1, a constant is written as a signed integer. -/
theorem constAttr_of_ne_one {w : Nat} (v : BitVec w) (h : w ≠ 1) :
    constAttr w v = .int v.toInt := by
  match w, h with
  | 0, _ => rfl
  | _ + 2, _ => rfl

/-- An `i1` constant is `1` or `0`. The proof checks both values with
`decide` (`docs/decisions/semantics-interpreter.md#bit-vector-proofs`). -/
theorem bitVec_one_cases (v : BitVec 1) : v = 1 ∨ v = 0 := by revert v; decide

/-! # Decoding what was encoded -/

/-- The width of a binary op is found only at two `iN` operands and one
`iN` result. -/
theorem binWidth_eq {ts rs : List Ty} {w : Nat} (h : binWidth ts rs = some w) :
    ts = [.int w, .int w] ∧ rs = [.int w] := by
  unfold binWidth at h
  split at h
  · split at h
    · cases h
      rename_i hw
      obtain ⟨rfl, rfl⟩ := hw
      exact ⟨rfl, rfl⟩
    · cases h
  · cases h

/-- A binary op with flags decodes only at two `iN` operands and one `iN`
result, from attributes that its flags decode from. -/
theorem binOp_eq {α : Type} {dec : List Attr → Option α} {mk : Nat → α → Op}
    {as : List Attr} {ts rs : List Ty} {o : Op}
    (h : (do pure (mk (← binWidth ts rs) (← dec as))) = some o) :
    ∃ w f, ts = [.int w, .int w] ∧ rs = [.int w] ∧ dec as = some f ∧ o = mk w f := by
  obtain ⟨w, hw, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨f, hf, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  obtain ⟨rfl, rfl⟩ := binWidth_eq hw
  exact ⟨w, f, rfl, rfl, hf, rfl⟩

/-- An op without attributes decodes only from none. -/
theorem bare_eq {as : List Attr} {op : Option Op} {o : Op} (h : bare as op = some o) :
    as = [] ∧ op = some o := by
  unfold bare at h
  split at h
  · rename_i ha
    exact ⟨List.isEmpty_iff.mp ha, h⟩
  · cases h

/-- A width change decodes only from one `iM` operand and one `iN` result,
without attributes. -/
theorem decodeCast_eq {mk : Nat → Nat → Op} {as : List Attr} {ts rs : List Ty} {o : Op}
    (h : decodeCast mk as ts rs = some o) :
    ∃ m n, as = [] ∧ ts = [.int m] ∧ rs = [.int n] ∧ o = mk m n := by
  unfold decodeCast at h
  split at h
  · obtain ⟨rfl, h⟩ := bare_eq h
    cases h
    exact ⟨_, _, rfl, rfl, rfl, rfl⟩
  · cases h

/-- Each op found in `plainBinOps` has the name it was found by, no
attributes, two `iN` operands and one `iN` result. -/
theorem plainBinOps_lookup {n : String} {mk : Nat → Op} (h : plainBinOps.lookup n = some mk)
    (w : Nat) : (mk w).name = n ∧ (mk w).attrs = [] ∧ (mk w).sig = [i w, i w] ∧
      (mk w).returnTypes = [i w] := by
  simp only [plainBinOps, List.lookup] at h
  repeat (split at h; (cases h; rename_i hn; cases beq_iff_eq.mp hn; exact ⟨rfl, rfl, rfl, rfl⟩))
  cases h

/-- `ptradd` decodes only from its own name, no attributes, a pointer and
an integer, and a pointer of the same memory. -/
theorem decodePtrAdd_eq {as : List Attr} {ts rs : List Ty} {op : Op}
    (h : decodePtrAdd as ts rs = some op) :
    op.name = "ptradd" ∧ op.attrs = as ∧ op.sig = ts ∧ op.returnTypes = rs := by
  unfold decodePtrAdd at h
  split at h
  · split at h
    · rename_i hn
      subst hn
      obtain ⟨rfl, h⟩ := bare_eq h
      cases h
      exact ⟨rfl, rfl, rfl, rfl⟩
    · cases h
  · cases h

/-- Every core op decodes from its name and attributes, at its operand and
result types. -/
theorem Op.decode_encode (o : Op) : Op.decode o.name o.attrs o.sig o.returnTypes = some o := by
  cases o with
  | const w v =>
    by_cases h : w = 1
    · subst h
      rcases bitVec_one_cases v with rfl | rfl <;> rfl
    · simp [Op.name, Op.attrs, Op.sig, Op.returnTypes, Op.decode, constAttr_of_ne_one v h, h]
  | fconst e m v => simp [Op.name, Op.attrs, Op.sig, Op.returnTypes, Op.decode, decodeFloatLit_floatLit]
  | fcmp p e m => simp [Op.name, Op.attrs, Op.sig, Op.returnTypes, Op.decode, find_fpred_name]
  | fbin o e m =>
    cases o <;> simp [Op.name, FBin.name, Op.attrs, FBin.attrs, Op.sig, Op.returnTypes, Op.decode,
      decodeFBin, FBin.attrsOk, roundAttr, isRoundAttrs, floatOpFormat]
  | funary o e m =>
    cases o <;> simp [Op.name, FUnary.name, Op.attrs, FUnary.attrs, Op.sig, Op.returnTypes,
      Op.decode, decodeFUnary, FUnary.attrsOk, roundAttr, isRoundAttrs, floatOpFormat]
  | fma e m =>
    simp [Op.name, Op.attrs, Op.sig, Op.returnTypes, Op.decode, decodeFma, roundAttr,
      isRoundAttrs, floatOpFormat]
  | sdiv _ e | udiv _ e =>
    cases e <;> simp [Op.name, Op.attrs, Op.sig, Op.returnTypes, Op.decode, binWidth, decodeExact, i]
  | toBits e m | ofBits e m => simp [Op.name, Op.attrs, Op.sig, Op.returnTypes, Op.decode, decodeBitcast, i]
  | sitofp n e m | uitofp n e m =>
    simp [Op.name, Op.attrs, Op.sig, Op.returnTypes, Op.decode, decodeIntToFloat, roundAttr,
      isRoundAttrs, i]
  | fpext e m e' m' => simp [Op.name, Op.attrs, Op.sig, Op.returnTypes, Op.decode, decodeFpext]
  | fptrunc e m e' m' =>
    simp [Op.name, Op.attrs, Op.sig, Op.returnTypes, Op.decode, decodeFptrunc, roundAttr,
      isRoundAttrs]
  | ptradd n w => simp [Op.name, Op.attrs, Op.sig, Op.returnTypes, Op.decode, decodePtrAdd, bare, i]
  | fptosi e m n | fptoui e m n =>
    simp [Op.name, Op.attrs, Op.sig, Op.returnTypes, Op.decode, decodeFloatToInt, i]
  | _ =>
    simp [Op.name, Op.attrs, Op.sig, Op.returnTypes, Op.decode, binWidth, decodeWrap_attrs, bare,
      decodeCast, plainBinOps, find_pred_name, i, List.lookup]

/-- A core op decodes only from its own name, attributes, operand types and
result types. -/
theorem Op.encode_decode {n : String} {as : List Attr} {ts rs : List Ty} {o : Op}
    (h : Op.decode n as ts rs = some o) :
    o.name = n ∧ o.attrs = as ∧ o.sig = ts ∧ o.returnTypes = rs := by
  unfold Op.decode at h
  split at h
  · -- const
    split at h <;> (try cases h)
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · split at h
      · cases h
        rename_i hw
        exact ⟨rfl, by simp [Op.attrs, constAttr_of_ne_one _ hw.1, hw.2], rfl, rfl⟩
      · cases h
    · obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨rfl, by simp [Op.attrs, floatLit_of_decode hb], rfl, rfl⟩
  · -- icmp
    split at h <;> (try cases h)
    rename_i p _ _
    cases hp : Pred.all.find? (·.name == p) with
    | none => simp [hp] at h
    | some pr =>
      simp only [hp] at h
      split at h
      · cases h
        rename_i hab
        subst hab
        exact ⟨rfl, by simp [Op.attrs, name_of_find_pred hp], rfl, rfl⟩
      · cases h
  · -- fcmp
    split at h <;> (try cases h)
    rename_i p _ _ _ _
    cases hp : FPred.all.find? (·.name == p) with
    | none => simp [hp] at h
    | some pr =>
      simp only [hp] at h
      split at h
      · cases h
        rename_i hab
        obtain ⟨rfl, rfl⟩ := hab
        exact ⟨rfl, by simp [Op.attrs, name_of_find_fpred hp], rfl, rfl⟩
      · cases h
  · exact decodeFBin_eq h -- fadd
  · exact decodeFBin_eq h -- fsub
  · exact decodeFBin_eq h -- fmul
  · exact decodeFBin_eq h -- fdiv
  · exact decodeFBin_eq h -- frem
  · exact decodeFBin_eq h -- fmod
  · exact decodeFUnary_eq h -- fneg
  · exact decodeFUnary_eq h -- fabs
  · exact decodeFUnary_eq h -- sqrt
  · exact decodeFma_eq h -- fma
  · -- add
    obtain ⟨_, _, rfl, rfl, hf, rfl⟩ := binOp_eq h
    exact ⟨rfl, attrs_of_decodeWrap hf, rfl, rfl⟩
  · -- sub
    obtain ⟨_, _, rfl, rfl, hf, rfl⟩ := binOp_eq h
    exact ⟨rfl, attrs_of_decodeWrap hf, rfl, rfl⟩
  · -- mul
    obtain ⟨_, _, rfl, rfl, hf, rfl⟩ := binOp_eq h
    exact ⟨rfl, attrs_of_decodeWrap hf, rfl, rfl⟩
  · -- sdiv
    obtain ⟨_, _, rfl, rfl, hf, rfl⟩ := binOp_eq h
    exact ⟨rfl, attrs_of_decodeExact hf, rfl, rfl⟩
  · -- udiv
    obtain ⟨_, _, rfl, rfl, hf, rfl⟩ := binOp_eq h
    exact ⟨rfl, attrs_of_decodeExact hf, rfl, rfl⟩
  · -- select
    split at h <;> (try cases h)
    split at h
    · rename_i hab
      obtain ⟨rfl, rfl⟩ := hab
      obtain ⟨rfl, h⟩ := bare_eq h
      cases h
      exact ⟨rfl, rfl, rfl, rfl⟩
    · cases h
  · -- zext
    obtain ⟨_, _, rfl, rfl, rfl, rfl⟩ := decodeCast_eq h
    exact ⟨rfl, rfl, rfl, rfl⟩
  · -- sext
    obtain ⟨_, _, rfl, rfl, rfl, rfl⟩ := decodeCast_eq h
    exact ⟨rfl, rfl, rfl, rfl⟩
  · -- trunc
    obtain ⟨_, _, rfl, rfl, rfl, rfl⟩ := decodeCast_eq h
    exact ⟨rfl, rfl, rfl, rfl⟩
  · exact decodeBitcast_eq h -- bitcast
  · -- freeze
    split at h <;> (try cases h)
    split at h
    · rename_i hab
      subst hab
      obtain ⟨rfl, h⟩ := bare_eq h
      cases h
      exact ⟨rfl, rfl, rfl, rfl⟩
    · cases h
  · -- br
    split at h
    · rename_i ht
      obtain ⟨rfl, h⟩ := bare_eq h
      cases h
      exact ⟨rfl, rfl, (List.isEmpty_iff.mp ht.1).symm, (List.isEmpty_iff.mp ht.2).symm⟩
    · cases h
  · -- cond_br
    split at h
    · rename_i ht
      obtain ⟨rfl, hr⟩ := ht
      obtain ⟨rfl, h⟩ := bare_eq h
      cases h
      exact ⟨rfl, rfl, rfl, (List.isEmpty_iff.mp hr).symm⟩
    · cases h
  · -- ret
    split at h
    · rename_i hr
      obtain ⟨rfl, h⟩ := bare_eq h
      cases h
      exact ⟨rfl, rfl, rfl, (List.isEmpty_iff.mp hr).symm⟩
    · cases h
  · -- unreachable
    split at h
    · rename_i ht
      obtain ⟨rfl, h⟩ := bare_eq h
      cases h
      exact ⟨rfl, rfl, (List.isEmpty_iff.mp ht.1).symm, (List.isEmpty_iff.mp ht.2).symm⟩
    · cases h
  · -- call
    split at h <;> cases h
    exact ⟨rfl, rfl, rfl, rfl⟩
  · -- poison
    split at h <;> (try cases h)
    obtain ⟨rfl, h⟩ := bare_eq h
    cases h
    exact ⟨rfl, rfl, rfl, rfl⟩
  · exact decodeIntToFloat_eq (signed := true) h -- sitofp
  · exact decodeIntToFloat_eq (signed := false) h -- uitofp
  · exact decodeFpext_eq h -- fpext
  · exact decodeFptrunc_eq h -- fptrunc
  · exact decodePtrAdd_eq h -- ptradd
  · exact decodeFloatToInt_eq (signed := true) h -- fptosi
  · exact decodeFloatToInt_eq (signed := false) h -- fptoui
  · -- srem, urem, and, or, xor, shl, lshr and ashr
    split at h
    · rename_i mk hmk
      obtain ⟨rfl, h⟩ := bare_eq h
      obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨rfl, rfl⟩ := binWidth_eq hw
      exact plainBinOps_lookup hmk w
    · cases h

/-! # Writing ops and types as tokens -/

/-- Every core op's name is a word. -/
theorem Op.name_isWord (o : Op) : isWord o.name := by
  cases o <;> first
    | (simp only [Op.name]; decide)
    | (rename_i o _ _; cases o <;> simp only [Op.name, FBin.name, FUnary.name] <;> decide)

/-- Every predicate's name is a word. -/
theorem Pred.name_isWord (p : Pred) : isWord p.name := by
  cases p <;> decide

/-- Every float predicate's name is a word. -/
theorem FPred.name_isWord (p : FPred) : isWord p.name := by
  cases p <;> decide

/-- Every core op's attributes can be written. -/
theorem Op.attrs_writable (o : Op) : Attr.AllWritable o.attrs := by
  cases o with
  | const w v =>
    by_cases h : w = 1
    · subst h
      refine ⟨?_, trivial⟩
      show isWord (if v = 1 then "true" else "false")
      split <;> decide
    · simp [Op.attrs, constAttr_of_ne_one v h, Attr.AllWritable, Attr.Writable]
  | icmp p _ => exact ⟨p.name_isWord, trivial⟩
  | fconst e m v => simp [Op.attrs, Attr.AllWritable, Attr.Writable, floatLit_valid]
  | fcmp p => exact ⟨p.name_isWord, trivial⟩
  | fbin o =>
    cases o <;> simp [Op.attrs, FBin.attrs, roundAttr, Attr.AllWritable, Attr.Writable] <;> decide
  | fma | sitofp | uitofp | fptrunc => simp [Op.attrs, roundAttr, Attr.AllWritable, Attr.Writable] <;> decide
  | funary o =>
    cases o <;> simp [Op.attrs, FUnary.attrs, roundAttr, Attr.AllWritable, Attr.Writable] <;> decide
  | add _ f | sub _ f | mul _ f =>
    obtain ⟨nuw, nsw⟩ := f
    cases nuw <;> cases nsw <;>
      simp [Op.attrs, WrapFlags.attrs, Attr.AllWritable, Attr.Writable] <;> decide
  | sdiv _ e | udiv _ e =>
    cases e <;> simp [Op.attrs, Attr.AllWritable, Attr.Writable] <;> decide
  | call => exact ⟨trivial, trivial⟩
  | _ => trivial

end Fir.Core

namespace Fir

/-! # The laws -/

/-- The core dialect's text meets the seven laws, for all 40 core ops and
every core type. -/
theorem Core.lawfulDialectText : LawfulDialectText CoreDialect where
  decodeOp_encode := Core.Op.decode_encode
  encode_decodeOp _ _ _ _ _ h := Core.Op.encode_decode h
  decodeTy_encode := Core.Ty.decode_attr
  encode_decodeTy _ _ h := Core.Ty.attr_decode h
  opName_isWord := Core.Op.name_isWord
  opAttrs_writable := Core.Op.attrs_writable
  tyAttr_isType := Core.Ty.attr_isType

instance : LawfulDialectText CoreDialect := Core.lawfulDialectText

/-- Every valid module of the core dialect is well formed. -/
theorem Core.validIsWellFormed : ValidIsWellFormed (d := CoreDialect) := Fir.validIsWellFormed

end Fir
