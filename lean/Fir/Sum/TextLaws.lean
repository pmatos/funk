import Fir.Sum.Dialect
import Fir.Text.ParseWellFormed

/-!
# When the text of a sum is lawful

The sum of two dialects with lawful text has lawful text exactly when every
word goes to its own side (`Dialect.sum.lawful_iff`): no op name and no
valid type of the base names `e`, and every op name and every valid type of
`e`'s own names `e`. Reading back must reach the side that wrote the word,
and the reader decides the side by the word alone.

Names make this hold for every sum. When the base's words name only
dialects of its set, `e`'s name is not in that set, and `e` writes its own
words under its name, every word goes to its own side
(`Dialect.sum.routes_of_names`), and every region kind goes to the rule of
the side that registers it (`Dialect.sum.validRegion_ext`). So adding a dialect of a new name to a
dialect with lawful text and a lawful set gives a dialect with lawful text
and a lawful set, and adding any number of them, one at a time, does too.

The round trip and the well-formedness of valid and of parsed modules are
proved for every dialect with lawful text, so they hold for each such sum
with no further assumption: `printThenParse`, `validIsWellFormed` and
`parse_wellFormed` apply to it as they are, as the last theorems of this
section restate.
-/

namespace Fir

namespace Dialect.sum

variable {base e : Dialect}

/-- Reading back the base's types from the sum's gives them. -/
theorem mapM_getLeft_map {A B : Type} (ts : List A) :
    (ts.map (Sum.inl (β := B))).mapM Sum.getLeft? = some ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [List.mapM_cons, ih]

/-- The sum's types that read back as the base's are the base's. -/
theorem eq_map_of_mapM_getLeft {A B : Type} {ts : List (A ⊕ B)} {ts' : List A}
    (h : ts.mapM Sum.getLeft? = some ts') : ts = ts'.map .inl := by
  induction ts generalizing ts' with
  | nil => simp at h; simp [h]
  | cons t ts ih =>
    cases t with
    | inl a =>
      simp only [List.mapM_cons, Sum.getLeft?_inl, Option.bind_eq_bind, Option.bind_some,
        Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨rest, hr, rfl⟩ := h
      simp [ih hr]
    | inr b => simp [List.mapM_cons] at h

variable [DialectName e] [DialectText base] [DialectText (base.over e)]

/-- A name of `e`'s goes to `e`. -/
theorem decodeOp_ext {n : String} {as : List Attr} {ts rs : List (base.Ty ⊕ e.Ty)}
    (h : wordDialect n = some (name e)) :
    decodeOp n as ts rs = (Fir.decodeOp (d := base.over e) n as ts rs).map .inr := by
  unfold decodeOp
  exact ite_eq_left h

/-- Every other name goes to the base, at the base's types. -/
theorem decodeOp_base {n : String} {as : List Attr} {ts rs : List (base.Ty ⊕ e.Ty)}
    (h : ¬ wordDialect n = some (name e)) :
    decodeOp n as ts rs = (ts.mapM Sum.getLeft?).bind fun ts' => (rs.mapM Sum.getLeft?).bind
      fun rs' => (Fir.decodeOp (d := base) n as ts' rs').map .inl := by
  unfold decodeOp
  exact ite_eq_right h

/-- A type of `e`'s name goes to `e`. -/
theorem decodeTy_ext {a : Attr} (h : a.dialect? = some (name e)) :
    decodeTy (base := base) (e := e) a = match Fir.decodeTy (d := base.over e) a with
      | some (.inr t) => some (.inr t)
      | _ => none := by
  unfold decodeTy
  exact ite_eq_left h

/-- Every other type goes to the base. -/
theorem decodeTy_base {a : Attr} (h : ¬ a.dialect? = some (name e)) :
    decodeTy (base := base) (e := e) a = (Fir.decodeTy (d := base) a).map .inl := by
  unfold decodeTy
  exact ite_eq_right h

variable [DialectSignature base] [DialectSignature (base.over e)]
  [DialectValidation base] [DialectValidation (base.over e)]

variable (base e) in
/-- Every word goes to its own side: no op name and no valid type of the
base names `e`, and every op name and every valid own type of `e` does. -/
def Routes : Prop :=
  (∀ o : base.Op, wordDialect (opName o) ≠ some (name e)) ∧
  (∀ o : e.Op, wordDialect (opName (d := base.over e) o) = some (name e)) ∧
  (∀ t : base.Ty, validTy t → (tyAttr t).dialect? ≠ some (name e)) ∧
  ∀ t : e.Ty, validTy (d := base.over e) (.inr t) →
    (tyAttr (d := base.over e) (.inr t)).dialect? = some (name e)

/-- If the sum's text is lawful, every word goes to its own side: reading a
word back must reach the side that wrote it. -/
theorem routes_of_lawful [LawfulDialectText (base ⊞ e)] : Routes base e := by
  refine ⟨fun o h => ?_, fun o => ?_, fun t ht h => ?_, fun t ht => ?_⟩
  · have hd : decodeOp (opName o) (opAttrs o) ((sig o).map .inl) ((returnTypes o).map .inl) =
        some (.inl o) := LawfulDialectText.decodeOp_encode (d := base ⊞ e) (.inl o)
    rw [decodeOp_ext h] at hd
    obtain ⟨_, _, h'⟩ := Option.map_eq_some_iff.mp hd
    cases h'
  · have hd : decodeOp (opName (d := base.over e) o) (opAttrs (d := base.over e) o)
        (sig (d := base.over e) o) (returnTypes (d := base.over e) o) = some (.inr o) :=
      LawfulDialectText.decodeOp_encode (d := base ⊞ e) (.inr o)
    by_cases h : wordDialect (opName (d := base.over e) o) = some (name e)
    · exact h
    · rw [decodeOp_base h, Option.bind_eq_some_iff] at hd
      obtain ⟨_, _, hd⟩ := hd
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨_, _, hd⟩ := hd
      obtain ⟨_, _, h'⟩ := Option.map_eq_some_iff.mp hd
      cases h'
  · have hd : decodeTy (base := base) (e := e) (tyAttr t) = some (.inl t) :=
      LawfulDialectText.decodeTy_encode (d := base ⊞ e) (.inl t) ht
    rw [decodeTy_ext h] at hd
    split at hd <;> cases hd
  · have hd : decodeTy (base := base) (e := e) (tyAttr (d := base.over e) (.inr t)) =
        some (.inr t) := LawfulDialectText.decodeTy_encode (d := base ⊞ e) (.inr t) ht
    by_cases h : (tyAttr (d := base.over e) (.inr t)).dialect? = some (name e)
    · exact h
    · rw [decodeTy_base h] at hd
      obtain ⟨_, _, h'⟩ := Option.map_eq_some_iff.mp hd
      cases h'

variable [LawfulDialectText base] [LawfulDialectText (base.over e)]

/-- Two dialects with lawful text whose words each go to their own side
make a sum with lawful text. -/
theorem lawful (h : Routes base e) : LawfulDialectText (base ⊞ e) where
  decodeOp_encode
    | .inl o => by
      have hd : decodeOp (e := e) (opName o) (opAttrs o) ((sig o).map .inl)
          ((returnTypes o).map .inl) = some (.inl o) := by
        rw [decodeOp_base (h.1 o), mapM_getLeft_map, mapM_getLeft_map]
        simp [LawfulDialectText.decodeOp_encode]
      exact hd
    | .inr o => by
      have hd : decodeOp (opName (d := base.over e) o) (opAttrs (d := base.over e) o)
          (sig (d := base.over e) o) (returnTypes (d := base.over e) o) = some (.inr o) := by
        rw [decodeOp_ext (h.2.1 o)]
        simp [LawfulDialectText.decodeOp_encode]
      exact hd
  encode_decodeOp n as ts rs op hd := by
    change decodeOp n as ts rs = some op at hd
    by_cases hn : wordDialect n = some (name e)
    · replace hd := (decodeOp_ext hn).symm.trans hd
      obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp hd
      exact LawfulDialectText.encode_decodeOp (d := base.over e) n as ts rs o ho
    · replace hd := (decodeOp_base hn).symm.trans hd
      obtain ⟨ts', hts, hd⟩ := Option.bind_eq_some_iff.mp hd
      obtain ⟨rs', hrs, hd⟩ := Option.bind_eq_some_iff.mp hd
      obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp hd
      obtain ⟨h₁, h₂, h₃, h₄⟩ := LawfulDialectText.encode_decodeOp (d := base) n as ts' rs' o ho
      refine ⟨h₁, h₂, ?_, ?_⟩
      · change (sig o).map Sum.inl = ts
        rw [h₃, eq_map_of_mapM_getLeft hts]
      · change (returnTypes o).map Sum.inl = rs
        rw [h₄, eq_map_of_mapM_getLeft hrs]
  decodeTy_encode
    | .inl t, hv => by
      have hd : decodeTy (base := base) (e := e) (tyAttr t) = some (.inl t) := by
        rw [decodeTy_base (h.2.2.1 t hv), LawfulDialectText.decodeTy_encode t hv]
        rfl
      exact hd
    | .inr t, hv => by
      have hd : decodeTy (base := base) (e := e) (tyAttr (d := base.over e) (.inr t)) =
          some (.inr t) := by
        rw [decodeTy_ext (h.2.2.2 t hv), LawfulDialectText.decodeTy_encode (d := base.over e) _ hv]
      exact hd
  encode_decodeTy a t hd := by
    change decodeTy a = some t at hd
    unfold decodeTy at hd
    split at hd
    · split at hd
      · rename_i t' ht'
        cases hd
        exact LawfulDialectText.encode_decodeTy (d := base.over e) a _ ht'
      · cases hd
    · obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp hd
      exact LawfulDialectText.encode_decodeTy (d := base) a t' ht'
  opName_isWord
    | .inl o => LawfulDialectText.opName_isWord (d := base) o
    | .inr o => LawfulDialectText.opName_isWord (d := base.over e) o
  opAttrs_writable
    | .inl o => LawfulDialectText.opAttrs_writable (d := base) o
    | .inr o => LawfulDialectText.opAttrs_writable (d := base.over e) o
  tyAttr_isType
    | .inl t, hv => LawfulDialectText.tyAttr_isType (d := base) t hv
    | .inr t, hv => LawfulDialectText.tyAttr_isType (d := base.over e) (.inr t) hv

/-- Given two dialects with lawful text, the sum's text is lawful exactly
when every word goes to its own side. -/
theorem lawful_iff : LawfulDialectText (base ⊞ e) ↔ Routes base e :=
  ⟨fun _ => routes_of_lawful, lawful⟩

omit [LawfulDialectText base] [LawfulDialectText (base.over e)] in
/-- The sum's text is lawful only when no op name belongs to both of its
sides. -/
theorem names_disjoint [LawfulDialectText (base ⊞ e)] (o₁ : base.Op) (o₂ : e.Op) :
    opName o₁ ≠ opName (d := base.over e) o₂ := fun h =>
  (routes_of_lawful (base := base) (e := e)).1 o₁ (h ▸ (routes_of_lawful (base := base)).2.1 o₂)

/-!
# Names route every word
-/

variable (base e) in
/-- `e` writes its own words under its name, and names only dialects of
its base's set besides its own: each op name and each valid type of its
own and each region kind that it registers names `e`, and every word of
its ops' attributes and of its valid types names the base's dialects or
`e`. -/
class _root_.Fir.LawfulDialectName [DialectSet base] : Prop where
  opName_named : ∀ o : e.Op, wordDialect (opName (d := base.over e) o) = some (name e)
  opAttrs_mem : ∀ o : e.Op, ∀ x ∈ Attr.dialectsAll (opAttrs (d := base.over e) o),
    x ∈ names base ++ [name e]
  tyAttr_named : ∀ t : e.Ty, validTy (d := base.over e) (.inr t) →
    (tyAttr (d := base.over e) (.inr t)).dialect? = some (name e)
  tyAttr_mem : ∀ t : e.Ty, validTy (d := base.over e) (.inr t) →
    ∀ x ∈ (tyAttr (d := base.over e) (.inr t)).dialects, x ∈ names base ++ [name e]
  kind_named : ∀ k ∈ regionKindNames (d := base.over e), wordDialect k = some (name e)

omit [DialectSignature base] [DialectSignature (base.over e)] [LawfulDialectText base]
    [LawfulDialectText (base.over e)] in
/-- When the base's words name only dialects of its set, `e`'s name is not
in that set, and `e` writes its own words under its name, every word goes
to its own side. -/
theorem routes_of_names [DialectSet base] [LawfulDialectSet base] [LawfulDialectName base e]
    (hn : name e ∉ names base) : Routes base e :=
  ⟨fun o h => hn (LawfulDialectSet.opName_mem o _ h),
    LawfulDialectName.opName_named,
    fun t ht h => hn (LawfulDialectSet.tyAttr_mem t ht _ (Attr.dialect?_mem h)),
    LawfulDialectName.tyAttr_named⟩

omit [DialectSignature base] [DialectSignature (base.over e)] [LawfulDialectText base]
    [LawfulDialectText (base.over e)] in
/-- The words of the sum name only dialects of its set, when the base's do
and `e` writes its own words under its name. -/
instance lawfulSet [DialectSet base] [LawfulDialectSet base] [LawfulDialectName base e] :
    LawfulDialectSet (base ⊞ e) where
  opName_mem
    | .inl o, x, h => List.mem_append_left _ (LawfulDialectSet.opName_mem o x h)
    | .inr o, x, h => by
      rw [show x = name e from Option.some.inj (h.symm.trans (LawfulDialectName.opName_named o))]
      exact List.mem_append_right _ (List.mem_singleton_self _)
  opAttrs_mem
    | .inl o, x, h => List.mem_append_left _ (LawfulDialectSet.opAttrs_mem o x h)
    | .inr o, x, h => LawfulDialectName.opAttrs_mem o x h
  tyAttr_mem
    | .inl t, hv, x, h => List.mem_append_left _ (LawfulDialectSet.tyAttr_mem t hv x h)
    | .inr t, hv, x, h => LawfulDialectName.tyAttr_mem t hv x h
  kind_mem k hk x h := by
    rcases List.mem_append.mp hk with hk | hk
    · exact List.mem_append_left _ (LawfulDialectSet.kind_mem k hk x h)
    · rw [show x = name e from Option.some.inj (h.symm.trans (LawfulDialectName.kind_named k hk))]
      exact List.mem_append_right _ (List.mem_singleton_self _)

omit [DialectSignature base] [DialectSignature (base.over e)] [LawfulDialectText base]
    [LawfulDialectText (base.over e)] in
/-- A region of a kind that `e` registers obeys `e`'s rule in the sum, when
the base's words name only dialects of its set, `e`'s name is new to it, and
`e` writes its kinds under its name. -/
theorem validRegion_ext [DialectSet base] [LawfulDialectSet base] [LawfulDialectName base e]
    (hn : name e ∉ names base) {host : Dialect} (v : DialectView (base ⊞ e) host) {k : Name}
    (hk : k ∈ regionKindNames (d := base.over e)) (ctx : FuncContext host) (f : Func host)
    (r : Region host) :
    validRegion (d := base ⊞ e) v k ctx f r ↔
      validRegion (d := base.over e) (extView v) k ctx f r := by
  have hb : k ∉ regionKindNames (d := base) := fun hb =>
    hn (LawfulDialectSet.kind_mem k hb _ (LawfulDialectName.kind_named k hk))
  show ValidRegion v k ctx f r ↔ _
  simp [ValidRegion, hb]

/-!
# The round trip over sums
-/

variable [DialectSet base] [LawfulDialectSet base] [LawfulDialectName base e]

/-- The sum's text is lawful when `e`'s name is new to its base. -/
theorem lawful_of_names (hn : name e ∉ names base) : LawfulDialectText (base ⊞ e) :=
  lawful (routes_of_names hn)

/-- Every valid module of a sum is well formed, when `e`'s name is new to
its base. -/
theorem validIsWellFormed (hn : name e ∉ names base) : ValidIsWellFormed (d := base ⊞ e) :=
  have := lawful_of_names hn
  Fir.validIsWellFormed

/-- `parse(print(m)) == m` for every well-formed module of a sum, when
`e`'s name is new to its base. -/
theorem printThenParse (hn : name e ∉ names base) : PrintThenParse (d := base ⊞ e) Fir.parse :=
  have := lawful_of_names hn
  Fir.printThenParse

/-- Every module of a sum that the parser gives is well formed, when `e`'s
name is new to its base. -/
theorem parse_wellFormed (hn : name e ∉ names base) {t : String} {m : Module (base ⊞ e)}
    (h : Fir.parse t = .ok m) : m.WellFormed :=
  have := lawful_of_names hn
  Fir.parse_wellFormed h

end Dialect.sum

end Fir
