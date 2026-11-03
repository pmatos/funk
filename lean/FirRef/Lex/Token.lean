import FirRef.Lex.Parts

/-!
A string, a symbol after `@`, an integer and a token, over positions, each
proved to give what the spec's lexer gives on the characters from its
position.
-/

namespace FirRef

open Fir Fir.Text

variable {s : String}

theorem lexStringP_eq (cs₀ : List Char) (i : s.Pos) (p start : TextPos) (acc : List Char) :
    ∀ h : (chars i).length ≤ cs₀.length,
      (lexStringP i p start acc).map (fun x => (x.1, chars x.2.1, x.2.2)) =
        (lexStringFrom cs₀ (chars i) h p start acc).map (fun x => (x.1, x.2.1.1, x.2.2)) := by
  fun_induction lexStringP i p start acc with
  | case1 i p acc hp =>
    rw [chars_of_peekP_none hp]
    intro h
    rw [lexStringFrom]
    try rfl
  | case2 i p acc i₁ hp =>
    rw [chars_of_peekP hp]
    intro h
    rw [lexStringFrom]
    try rfl
  | case3 i p acc i₁ hp c w i₂ he ih =>
    rw [chars_of_peekP hp]
    intro h
    rw [lexStringFrom]
    rcases map_agree (lexEscapeP_eq i₁ p) with ⟨e, hx, hy⟩ | ⟨a, ⟨c', w', r, hr⟩, hx, hy, hxy⟩
    · rw [he] at hx
      cases hx
    · rw [he] at hx
      cases hx
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨rfl, rfl, rfl⟩ := hxy
      rw [hy]
      exact ih _
  | case4 i p acc i₁ hp e he =>
    rw [chars_of_peekP hp]
    intro h
    rw [lexStringFrom]
    rcases map_agree (lexEscapeP_eq i₁ p) with ⟨e', hx, hy⟩ | ⟨a, b, hx, hy, hxy⟩
    · rw [he] at hx
      cases hx
      rw [hy]
      rfl
    · rw [he] at hx
      cases hx
  | case5 i p acc c i₁ hq hb hp hesc =>
    rw [chars_of_peekP hp]
    intro h
    rw [lexStringFrom]
    · split
      · rfl
      · contradiction
    all_goals (intros; simp_all)
  | case6 i p acc c i₁ hq hb hp hesc ih =>
    rw [chars_of_peekP hp]
    intro h
    rw [lexStringFrom]
    · split
      · contradiction
      · exact ih _
    all_goals (intros; simp_all)

theorem lexStringP_nil_eq (i : s.Pos) (p start : TextPos) :
    (lexStringP i p start []).map (fun x => (x.1, chars x.2.1, x.2.2)) =
      (lexString (chars i) p start).map (fun x => (x.1, x.2.1.1, x.2.2)) :=
  lexStringP_eq (chars i) i p start [] (Nat.le_refl _)

/-- `lexAt`, over positions. -/
def lexAtP (i : s.Pos) (p : TextPos) : Except ParseError (Tok × s.Pos × TextPos) :=
  match peekP i with
  | some (c, i₁) =>
    if c.isDigit then
      let q := p.advance 1
      match lexDigitsP c i₁ q with
      | .ok (ds, j) =>
        let n := digitsValue ds
        if n < Location.limit then .ok (.locRef n, j, q.advance ds.length)
        else errorAt q s!"location reference @{n} is out of range: it must be below 2^32"
      | .error e => .error e
    else if isWordStart c then
      let w := takeWhileP isNameChar i₁ []
      .ok (.sym (String.ofList (c :: w)), skipWhileP isNameChar i₁, p.advance (2 + w.length))
    else if c = '"' then
      match lexStringP i₁ (p.advance 2) (p.advance 1) [] with
      | .ok (str, j, q) =>
        if isWord str then errorAt p ("the symbol @\"" ++ str ++ "\" is written @" ++ str)
        else .ok (.sym str, j, q)
      | .error e => .error e
    else errorAt p "@ must be followed by a symbol or a location reference"
  | none => errorAt p "@ must be followed by a symbol or a location reference"

theorem lexAtP_eq (i : s.Pos) (p : TextPos) :
    (lexAtP i p).map (fun x => (x.1, chars x.2.1, x.2.2)) =
      (lexAt (chars i) p).map (fun x => (x.1, x.2.1.1, x.2.2)) := by
  unfold lexAtP lexAt
  rcases hp : peekP i with _ | ⟨c, i₁⟩
  · rw [chars_of_peekP_none hp]
    rfl
  rw [chars_of_peekP hp]
  simp only
  split
  · rcases map_agree (lexDigitsP_eq c i₁ (p.advance 1)) with
      ⟨e, hx, hy⟩ | ⟨⟨ds, j⟩, ⟨ds', r, hr⟩, hx, hy, hxy⟩
    · rw [hx, hy]
      rfl
    · rw [hx, hy]
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨rfl, rfl⟩ := hxy
      simp only [okBind]
      split <;> rfl
  split
  · simp [takeWhileP_eq, chars_skipWhileP]
  split
  · rcases map_agree (lexStringP_nil_eq i₁ (p.advance 2) (p.advance 1)) with
      ⟨e, hx, hy⟩ | ⟨⟨str, j, q⟩, ⟨str', ⟨r, hr⟩, q'⟩, hx, hy, hxy⟩
    · rw [hx, hy]
      rfl
    · rw [hx, hy]
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨rfl, rfl, rfl⟩ := hxy
      simp only [okBind]
      split <;> rfl
  · rfl

/-- `lexInt`, over positions. -/
def lexIntP (neg : Bool) (d : Char) (i : s.Pos) (p : TextPos) :
    Except ParseError (Tok × s.Pos × TextPos) :=
  match lexDigitsP d i p with
  | .ok (ds, j) =>
    let n : Int := digitsValue ds
    .ok (.int (if neg then -n else n), j, p.advance ((if neg then 1 else 0) + ds.length))
  | .error e => .error e

theorem lexIntP_eq (neg : Bool) (d : Char) (i : s.Pos) (p : TextPos) :
    (lexIntP neg d i p).map (fun x => (x.1, chars x.2.1, x.2.2)) =
      (lexInt neg d (chars i) p).map (fun x => (x.1, x.2.1.1, x.2.2)) := by
  unfold lexIntP lexInt
  rcases map_agree (lexDigitsP_eq d i p) with ⟨e, hx, hy⟩ | ⟨⟨ds, j⟩, ⟨ds', r, hr⟩, hx, hy, hxy⟩
  · rw [hx, hy]
    rfl
  · rw [hx, hy]
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨rfl, rfl⟩ := hxy
    rfl

end FirRef
