import Fir.Sum.Lift
import Fir.Sum.TextLaws

/-!
# The text of a lift

The lift of an extension `e` with lawful text has lawful text over `big`
(`Dialect.lift.lawfulText`) when `big`'s text is lawful, `big`'s words name
only dialects of its set, `e` writes its own words under its name, and `e`'s
name is new to `big`. Then no valid type of `big` names `e`, so every type
goes back to the side that wrote it, and reading an op projects its types
back to those that `e` wrote.

The lift writes its words under `e`'s name, and names only dialects of
`big`'s set besides its own, when `dep`'s set is in `big`'s
(`Dialect.lift.lawfulName`). So the sum `big ⊞ e.lift dep ι` has lawful
text under the same conditions as a sum of `big` and an extension written
over it, and the round trip and well-formedness hold for it: the last
theorems of this section restate them.
-/

namespace Fir

namespace Dialect.lift

variable {e dep big : Dialect} [TyDenote dep.Ty] [TyDenote big.Ty] [TyDenote e.Ty]
  {ι : TyIncl dep.Ty big.Ty}
  [DialectName e] [DialectText big] [DialectText (dep.over e)]
  [DialectSignature big] [DialectSignature (dep.over e)]
  [DialectValidation big] [DialectValidation (dep.over e)]

omit [DialectSignature big] [DialectSignature (dep.over e)] in
/-- The words of the lift name `e` where `e`'s do, and only dialects of
`big`'s set besides, when `dep`'s set is in `big`'s. -/
theorem lawfulName [DialectSet dep] [DialectSet big] [LawfulDialectName dep e]
    (hsub : ∀ x ∈ names dep, x ∈ names big) : LawfulDialectName big (e.lift dep ι) where
  opName_named o := LawfulDialectName.opName_named (base := dep) (e := e) o
  opAttrs_mem o x h := by
    have hx := LawfulDialectName.opAttrs_mem (base := dep) (e := e) o x h
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (hsub x hx)
    · exact List.mem_append_right _ hx
  tyAttr_named t hv := LawfulDialectName.tyAttr_named (base := dep) (e := e) t hv
  tyAttr_mem t hv x h := by
    have hx := LawfulDialectName.tyAttr_mem (base := dep) (e := e) t hv x h
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (hsub x hx)
    · exact List.mem_append_right _ hx

variable [LawfulDialectText big] [LawfulDialectText (dep.over e)]

/-- The lift of an extension with lawful text has lawful text over `big`,
when `big`'s words name only dialects of its set, `e` writes its own words
under its name, and `e`'s name is new to `big`. -/
theorem lawfulText [DialectSet dep] [DialectSet big] [LawfulDialectSet big]
    [LawfulDialectName dep e] (hn : name e ∉ names big) :
    LawfulDialectText (big.over (e.lift dep ι)) where
  decodeOp_encode o := by
    change decodeOp (e := e) ι _ _ ((sig (d := dep.over e) o).map (incl e ι).incl)
      ((returnTypes (d := dep.over e) o).map (incl e ι).incl) = some o
    rw [decodeOp, TyIncl.mapM_proj_map (incl e ι), Option.bind_some,
      TyIncl.mapM_proj_map (incl e ι), Option.bind_some]
    exact LawfulDialectText.decodeOp_encode (d := dep.over e) o
  encode_decodeOp n as ts rs o hd := by
    change decodeOp (e := e) ι n as ts rs = some o at hd
    obtain ⟨ts', hts, hd⟩ := Option.bind_eq_some_iff.mp hd
    obtain ⟨rs', hrs, hd⟩ := Option.bind_eq_some_iff.mp hd
    obtain ⟨h₁, h₂, h₃, h₄⟩ := LawfulDialectText.encode_decodeOp (d := dep.over e) n as ts' rs' o hd
    refine ⟨h₁, h₂, ?_, ?_⟩
    · change (sig (d := dep.over e) o).map (incl e ι).incl = ts
      rw [h₃, (incl e ι).eq_map_of_mapM_proj hts]
    · change (returnTypes (d := dep.over e) o).map (incl e ι).incl = rs
      rw [h₄, (incl e ι).eq_map_of_mapM_proj hrs]
  decodeTy_encode
    | .inl t, hv => by
      change decodeTy (e := e) dep (Fir.tyAttr t) = some (.inl t)
      have hne : (Fir.tyAttr t).dialect? ≠ some (name e) := fun h =>
        hn (LawfulDialectSet.tyAttr_mem t hv _ (Attr.dialect?_mem h))
      rw [decodeTy, ite_eq_right hne, LawfulDialectText.decodeTy_encode t hv]
      rfl
    | .inr t, hv => by
      change decodeTy (e := e) dep (Fir.tyAttr (d := dep.over e) (.inr t)) = some (.inr t)
      rw [decodeTy, ite_eq_left (LawfulDialectName.tyAttr_named (base := dep) (e := e) t hv),
        LawfulDialectText.decodeTy_encode (d := dep.over e) _ hv]
  encode_decodeTy a t hd := by
    change decodeTy (e := e) dep a = some t at hd
    unfold decodeTy at hd
    split at hd
    · split at hd
      · rename_i t' ht'
        cases hd
        exact LawfulDialectText.encode_decodeTy (d := dep.over e) a _ ht'
      · cases hd
    · obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp hd
      exact LawfulDialectText.encode_decodeTy (d := big) a t' ht'
  opName_isWord o := LawfulDialectText.opName_isWord (d := dep.over e) o
  opAttrs_writable o := LawfulDialectText.opAttrs_writable (d := dep.over e) o
  tyAttr_isType
    | .inl t, hv => LawfulDialectText.tyAttr_isType (d := big) t hv
    | .inr t, hv => LawfulDialectText.tyAttr_isType (d := dep.over e) (.inr t) hv

/-!
# The round trip over a sum with a lift
-/

variable [DialectSet dep] [DialectSet big] [LawfulDialectSet big] [LawfulDialectName dep e]

/-- The sum of `big` and a lift into it has lawful text, when `e`'s name
is new to `big` and `dep`'s set is in `big`'s. -/
theorem sum_lawfulText (hn : name e ∉ names big) (hsub : ∀ x ∈ names dep, x ∈ names big) :
    LawfulDialectText (big ⊞ e.lift dep ι) :=
  have := lawfulText (e := e) (dep := dep) (ι := ι) hn
  have := lawfulName (e := e) (ι := ι) hsub
  Dialect.sum.lawful_of_names hn

/-- Every valid module of the sum of `big` and a lift into it is well
formed. -/
theorem sum_validIsWellFormed (hn : name e ∉ names big) (hsub : ∀ x ∈ names dep, x ∈ names big) :
    ValidIsWellFormed (d := big ⊞ e.lift dep ι) :=
  have := sum_lawfulText (e := e) (dep := dep) (ι := ι) hn hsub
  Fir.validIsWellFormed

/-- `parse(print(m)) == m` for every well-formed module of the sum of `big`
and a lift into it. -/
theorem sum_printThenParse (hn : name e ∉ names big) (hsub : ∀ x ∈ names dep, x ∈ names big) :
    PrintThenParse (d := big ⊞ e.lift dep ι) Fir.parse :=
  have := sum_lawfulText (e := e) (dep := dep) (ι := ι) hn hsub
  Fir.printThenParse

end Dialect.lift

end Fir
