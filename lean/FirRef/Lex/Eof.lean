import FirRef.Lex.Cursor

/-!
The lexer reads `eof` only at the end of the text: every token that
`nextTokP` reads before the end is another (`nextTokP_ne_eof`). So when the
tokens that a lexer's state gives, up to its first error, hold `eof`, the
text has no lexer error from there (`lexRest_of_eof_mem`). `FirRef.readText`
uses this to read a text in one pass and to look for a lexer error only
when the readers fail.
-/

namespace FirRef

open Fir Fir.Text

variable {s : String}

theorem punctOf_ne_eof (c : Char) : punctOf c ≠ some .eof := by
  unfold punctOf
  split <;> simp

theorem lexIntP_ne_eof {neg : Bool} {d : Char} {i j : s.Pos} {p q : TextPos}
    (h : lexIntP neg d i p = .ok (.eof, j, q)) : False := by
  unfold lexIntP at h
  split at h <;> cases h

theorem lexAtP_ne_eof {i j : s.Pos} {p q : TextPos} (h : lexAtP i p = .ok (.eof, j, q)) : False := by
  unfold lexAtP at h
  dsimp only at h
  repeat' split at h
  all_goals first | cases h | simp [errorAt] at h

theorem lexFloatP_ne_eof {neg : Bool} {d : Char} {i j : s.Pos} {p q : TextPos}
    (h : lexFloatP neg d i p = some (.ok (.eof, j, q))) : False := by
  unfold lexFloatP at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | skip
  all_goals simp only [Option.some.injEq] at h
  · unfold lexFractionP at h
    split at h <;> cases h
  · unfold lexHexP at h
    dsimp only at h
    split at h
    · cases h
    · rename_i hx
      generalize lexEndP _ p = r at h
      cases r <;> cases h

theorem lexNumberP_ne_eof {neg : Bool} {d : Char} {i j : s.Pos} {p q : TextPos}
    (h : lexNumberP neg d i p = .ok (.eof, j, q)) : False := by
  unfold lexNumberP at h
  split at h
  · rename_i hx
    subst h
    exact lexFloatP_ne_eof hx
  · exact lexIntP_ne_eof h

theorem lexMinusZeroP_ne_eof {i j : s.Pos} {p q : TextPos}
    (h : (match lexFloatP true '0' i p with
      | some r => r
      | none => errorAt p "-0 is not an integer") = .ok (.eof, j, q)) : False := by
  split at h
  · rename_i hx
    subst h
    exact lexFloatP_ne_eof hx
  · cases h

theorem lexTokenP_ne_eof {c : Char} {i j : s.Pos} {p q : TextPos} {t : Tok}
    (h : lexTokenP c i p = .ok (t, j, q)) : t ≠ .eof := by
  rintro rfl
  unfold lexTokenP at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (simp at h; done)
    | exact lexAtP_ne_eof h
    | exact lexNumberP_ne_eof h
    | exact lexMinusZeroP_ne_eof h
    | (cases h; rename_i hf; exact lexFloatP_ne_eof hf)
    | (cases h; simp_all [punctOf_ne_eof])

/-- A step of the lexer that does not end the text reads a token other
than `eof`. -/
theorem nextTokP_ne_eof (i : s.Pos) (p : TextPos) :
    ∀ {t : Token} {j : s.Pos} {q : TextPos}, nextTokP i p = .ok (t, some (j, q)) →
      t.tok ≠ .eof := by
  fun_induction nextTokP i p with
  | case1 => intro t j q hn; cases hn
  | case2 i p c i₁ h hc ih | case3 i p i₁ h hc ih => exact ih
  | case4 => intro t j q hn; cases hn
  | case5 i p i₁ i₂ h₁ n j hc h hws hnl ih => exact ih
  | case6 i p c i₁ h hws hnl i₂ h₁ hs t j q hx | case8 i p c i₁ h hws hnl t j q hx =>
    intro t' j' q' hn
    cases hn
    exact lexTokenP_ne_eof hx
  | case7 | case9 => intro t j q hn; cases hn

/-- Lexing from a state succeeds when the tokens it gives up to its first
error hold `eof`. -/
theorem lexRest_of_eof_mem (st : Option (s.Pos × TextPos)) :
    ∀ t ∈ lexToks st, t.tok = .eof → ∃ ts, lexRest st = .ok ts := by
  fun_induction lexToks st with
  | case1 => intro t ht; cases ht
  | case2 i p t st h ih =>
    intro u hu he
    rcases List.mem_cons.1 hu with rfl | hu
    · rcases st with _ | ⟨j, q⟩
      · refine ⟨[u], ?_⟩
        rw [lexRest_some, h]
        dsimp only
        rw [lexRest_none]
        rfl
      · exact absurd he (nextTokP_ne_eof i p h)
    · obtain ⟨ts, hts⟩ := ih u hu he
      refine ⟨t :: ts, ?_⟩
      rw [lexRest_some, h]
      dsimp only
      rw [hts]
      rfl
  | case3 i p e h => intro t ht; cases ht

end FirRef
