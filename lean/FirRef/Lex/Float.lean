import FirRef.Lex.Token

/-!
A float literal and a number, over positions (ADR-2026-11-11-1438): the end
of a number, an exponent, hexadecimal digits, a fraction, a float literal
and a number, each proved to give what the spec's function gives on the
characters from its position.
-/

namespace FirRef

open Fir Fir.Text

variable {s : String}

/-- `lexEnd`, over positions. -/
def lexEndP (i : s.Pos) (p : TextPos) : Except ParseError Unit :=
  match peekP i with
  | some (c, _) => if isNameChar c then errorAt p (runsInto c) else .ok ()
  | none => .ok ()

theorem lexEndP_eq (i : s.Pos) (p : TextPos) : lexEndP i p = lexEnd (chars i) p := by
  unfold lexEndP lexEnd
  rcases hp : peekP i with _ | ⟨c, j⟩
  · rw [chars_of_peekP_none hp]
  · rw [chars_of_peekP hp]

/-- `lexExponent`, over positions. -/
def lexExponentP (i : s.Pos) (p : TextPos) : Except ParseError (Option Int × s.Pos) :=
  match peekP i with
  | some ('e', i₁) =>
    match peekP i₁ with
    | some ('-', i₂) =>
      match peekP i₂ with
      | some (x, i₃) =>
        if x = '0' then errorAt p "-0 is not an exponent"
        else if x.isDigit then
          (lexDigitsP x i₃ p).map fun (ds, j) => (some (-(digitsValue ds : Int)), j)
        else errorAt p (runsInto 'e')
      | none => errorAt p (runsInto 'e')
    | some (x, i₂) =>
      if x.isDigit then (lexDigitsP x i₂ p).map fun (ds, j) => (some (digitsValue ds : Int), j)
      else errorAt p (runsInto 'e')
    | none => errorAt p (runsInto 'e')
  | _ => (lexEndP i p).map fun _ => (none, i)

theorem lexExponentP_eq (i : s.Pos) (p : TextPos) :
    (lexExponentP i p).map (fun x => (x.1, chars x.2)) =
      (lexExponent (chars i) p).map (fun x => (x.1, x.2.1)) := by
  have hend : ∀ (cs : List Char) (h₁ : ∀ x r, cs = 'e' :: '-' :: x :: r → False)
      (h₂ : ∀ x r, cs = 'e' :: x :: r → False), chars i = cs →
      ((lexEndP i p).map fun _ => ((none : Option Int), i)).map (fun x => (x.1, chars x.2)) =
        (lexExponent cs p).map (fun x => (x.1, x.2.1)) := by
    intro cs h₁ h₂ hc
    rw [lexExponent.eq_3 _ _ h₁ h₂, lexEndP_eq, hc]
    cases lexEnd cs p <;> simp [hc]
  unfold lexExponentP
  rcases hp : peekP i with _ | ⟨c, i₁⟩
  · rw [chars_of_peekP_none hp]
    exact hend [] (by simp) (by simp) (chars_of_peekP_none hp)
  have hc := chars_of_peekP hp
  by_cases he : c = 'e'
  · subst he
    rcases hp₁ : peekP i₁ with _ | ⟨c₁, i₂⟩
    · simp only [hp₁]
      rw [hc, chars_of_peekP_none hp₁, lexExponent.eq_3 _ _ (by simp) (by simp)]
      simp (config := { decide := true }) [lexEnd]
      rfl
    have hc₁ := chars_of_peekP hp₁
    by_cases hm : c₁ = '-'
    · subst hm
      simp only [hp₁]
      rcases hp₂ : peekP i₂ with _ | ⟨x, i₃⟩
      · rw [hc, hc₁, chars_of_peekP_none hp₂, lexExponent.eq_2 _ _ _ (by simp)]
        simp (config := { decide := true })
        rfl
      rw [hc, hc₁, chars_of_peekP hp₂, lexExponent.eq_1]
      dsimp only
      split
      · rfl
      split
      · rcases map_agree (lexDigitsP_eq x i₃ p) with
          ⟨e, hx, hy⟩ | ⟨⟨ds, j⟩, ⟨ds', r, hr⟩, hx, hy, hxy⟩
        · rw [hx, hy]; rfl
        · rw [hx, hy]
          simp only [Prod.mk.injEq] at hxy
          obtain ⟨rfl, rfl⟩ := hxy
          rfl
      · rfl
    · rw [hc, hc₁, lexExponent.eq_2 _ _ _ (fun _ _ h _ => hm h)]
      simp only [hp₁]
      split
      · rcases map_agree (lexDigitsP_eq c₁ i₂ p) with
          ⟨e, hx, hy⟩ | ⟨⟨ds, j⟩, ⟨ds', r, hr⟩, hx, hy, hxy⟩
        · rw [hx, hy]; rfl
        · rw [hx, hy]
          simp only [Prod.mk.injEq] at hxy
          obtain ⟨rfl, rfl⟩ := hxy
          rfl
      · rfl
  · have : (match some (c, i₁) with
        | some ('e', i₁) =>
          match peekP i₁ with
          | some ('-', i₂) =>
            match peekP i₂ with
            | some (x, i₃) =>
              if x = '0' then errorAt p "-0 is not an exponent"
              else if x.isDigit then
                (lexDigitsP x i₃ p).map fun (ds, j) => (some (-(digitsValue ds : Int)), j)
              else errorAt p (runsInto 'e')
            | none => errorAt p (runsInto 'e')
          | some (x, i₂) =>
            if x.isDigit then (lexDigitsP x i₂ p).map fun (ds, j) => (some (digitsValue ds : Int), j)
            else errorAt p (runsInto 'e')
          | none => errorAt p (runsInto 'e')
        | _ => (lexEndP i p).map fun _ => (none, i) : Except ParseError (Option Int × s.Pos)) =
        (lexEndP i p).map fun _ => (none, i) := by
      split
      · rename_i heq; simp at heq; exact absurd heq.1 he
      · rfl
    rw [this, hc]
    exact hend _ (fun _ _ h => by simp at h; exact he h.1) (fun _ _ h => by simp at h; exact he h.1) hc

/-- `lexHex`, over positions. -/
def lexHexP (i : s.Pos) (p : TextPos) : Except ParseError (Tok × s.Pos × TextPos) :=
  let ds := takeWhileP isHexDigit i []
  if ds.isEmpty then errorAt p "0x must be followed by lowercase hexadecimal digits"
  else
    (lexEndP (skipWhileP isHexDigit i) p).map fun _ =>
      (.float (.hex ds), skipWhileP isHexDigit i, p.advance (2 + ds.length))

theorem lexHexP_eq (i : s.Pos) (p : TextPos) :
    (lexHexP i p).map (fun x => (x.1, chars x.2.1, x.2.2)) =
      (lexHex (chars i) p).map (fun x => (x.1, x.2.1.1, x.2.2)) := by
  unfold lexHexP lexHex
  simp only [takeWhileP_eq, List.reverse_nil, List.nil_append]
  split
  · rfl
  · rw [lexEndP_eq, chars_skipWhileP]
    cases lexEnd ((chars i).dropWhile isHexDigit) p <;> simp [chars_skipWhileP]

/-- `lexFraction`, over positions. -/
def lexFractionP (neg : Bool) (whole : Nat) (c : Char) (i : s.Pos) (p : TextPos) :
    Except ParseError (Tok × s.Pos × TextPos) :=
  match lexExponentP (skipWhileP Char.isDigit i) p with
  | .ok (exp, j) =>
    let l := FloatLit.dec neg whole (c :: takeWhileP Char.isDigit i []) exp
    .ok (.float l, j, p.advance l.print.length)
  | .error e => .error e

theorem lexFractionP_eq (neg : Bool) (whole : Nat) (c : Char) (i : s.Pos) (p : TextPos) :
    (lexFractionP neg whole c i p).map (fun x => (x.1, chars x.2.1, x.2.2)) =
      (lexFraction neg whole c (chars i) p).map (fun x => (x.1, x.2.1.1, x.2.2)) := by
  unfold lexFractionP lexFraction
  have h := lexExponentP_eq (skipWhileP Char.isDigit i) p
  rw [chars_skipWhileP] at h
  rcases map_agree h with ⟨e, hx, hy⟩ | ⟨⟨exp, j⟩, ⟨exp', r, hr⟩, hx, hy, hxy⟩
  · rw [hx, hy]; rfl
  · rw [hx, hy]
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨rfl, rfl⟩ := hxy
    simp [takeWhileP_eq]

/-- What follows the whole part of a number, over positions. -/
def afterWholeP (d : Char) (i : s.Pos) : s.Pos := if d = '0' then i else skipWhileP Char.isDigit i

theorem chars_afterWholeP (d : Char) (i : s.Pos) : chars (afterWholeP d i) = afterWhole d (chars i) := by
  unfold afterWholeP afterWhole
  split <;> simp [chars_skipWhileP]

/-- The value of the whole part of a number, over positions. -/
def wholeValueP (d : Char) (i : s.Pos) : Nat :=
  if d = '0' then 0 else digitsValue (d :: takeWhileP Char.isDigit i [])

theorem wholeValueP_eq (d : Char) (i : s.Pos) : wholeValueP d i = wholeValue d (chars i) := by
  simp [wholeValueP, wholeValue, takeWhileP_eq]

/-- `lexFloat`, over positions. -/
def lexFloatP (neg : Bool) (d : Char) (i : s.Pos) (p : TextPos) :
    Option (Except ParseError (Tok × s.Pos × TextPos)) :=
  match peekP (afterWholeP d i) with
  | some ('.', j₁) =>
    match peekP j₁ with
    | some (c, j₂) => if c.isDigit then some (lexFractionP neg (wholeValueP d i) c j₂ p) else none
    | none => none
  | some ('x', j₁) => if d = '0' ∧ neg = false then some (lexHexP j₁ p) else none
  | _ => none

theorem lexFloatP_eq (neg : Bool) (d : Char) (i : s.Pos) (p : TextPos) :
    (lexFloatP neg d i p).map (·.map fun x => (x.1, chars x.2.1, x.2.2)) =
      (lexFloat neg d (chars i) p).map (·.map fun x => (x.1, x.2.1.1, x.2.2)) := by
  unfold lexFloatP lexFloat
  have ha := chars_afterWholeP d i
  rcases hp : peekP (afterWholeP d i) with _ | ⟨c₀, j₁⟩
  · rw [chars_of_peekP_none hp] at ha
    simp only [Option.map_none]
    split
    · rename_i heq; rw [← ha] at heq; cases heq
    · rename_i heq; rw [← ha] at heq; cases heq
    · rfl
  rw [chars_of_peekP hp] at ha
  by_cases hd : c₀ = '.'
  · subst hd
    rcases hp₁ : peekP j₁ with _ | ⟨c, j₂⟩
    · rw [chars_of_peekP_none hp₁] at ha
      simp only [hp₁, Option.map_none]
      split
      · rename_i heq; rw [← ha] at heq; simp at heq
      · rename_i heq; rw [← ha] at heq; simp at heq
      · rfl
    rw [chars_of_peekP hp₁] at ha
    simp only [hp₁]
    by_cases hcd : c.isDigit = true
    · simp only [hcd, ite_true, Option.map_some]
      split
      · rename_i c' r heq
        rw [← ha] at heq
        simp only [List.cons.injEq, true_and] at heq
        obtain ⟨rfl, rfl⟩ := heq
        simp only [hcd, ite_true, Option.map_some, Option.some.injEq, wholeValueP_eq]
        rcases map_agree (lexFractionP_eq neg (wholeValue d (chars i)) c j₂ p) with
          ⟨e, hx, hy⟩ | ⟨⟨t, j, q⟩, ⟨t', ⟨r, hr⟩, q'⟩, hx, hy, hxy⟩
        · rw [hx, hy]; rfl
        · rw [hx, hy]
          simp only [Prod.mk.injEq] at hxy
          obtain ⟨rfl, rfl, rfl⟩ := hxy
          rfl
      · rename_i heq; rw [← ha] at heq; simp at heq
      · rename_i hn _
        rw [← ha] at hn
        exact absurd rfl (hn c (chars j₂))
    · simp only [hcd, Bool.false_eq_true, ite_false, Option.map_none]
      split
      · rename_i c' r heq
        rw [← ha] at heq
        simp only [List.cons.injEq, true_and] at heq
        obtain ⟨rfl, rfl⟩ := heq
        simp [hcd]
      · rename_i heq; rw [← ha] at heq; simp at heq
      · rfl
  by_cases hx : c₀ = 'x'
  · subst hx
    by_cases hz : d = '0' ∧ neg = false
    · simp only [hz, and_self, ite_true, Option.map_some]
      split
      · rename_i heq; rw [← ha] at heq; simp at heq
      · rename_i r heq
        rw [← ha] at heq
        simp only [List.cons.injEq, true_and] at heq
        subst heq
        simp only [Option.map_some, Option.some.injEq]
        rcases map_agree (lexHexP_eq j₁ p) with
          ⟨e, hx, hy⟩ | ⟨⟨t, j, q⟩, ⟨t', ⟨r, hr⟩, q'⟩, hx, hy, hxy⟩
        · rw [hx, hy]; rfl
        · rw [hx, hy]
          simp only [Prod.mk.injEq] at hxy
          obtain ⟨rfl, rfl, rfl⟩ := hxy
          rfl
      · rename_i _ hn
        exact absurd ha.symm (hn _)
    · simp only [hz, ite_false, Option.map_none]
      split
      · rename_i heq; rw [← ha] at heq; simp at heq
      · rename_i r heq
        rw [← ha] at heq
        simp only [List.cons.injEq, true_and] at heq
        subst heq
        simp_all
      · rfl
  · have : (match some (c₀, j₁) with
        | some ('.', j₁) =>
          match peekP j₁ with
          | some (c, j₂) =>
            if c.isDigit then some (lexFractionP neg (wholeValueP d i) c j₂ p) else none
          | none => none
        | some ('x', j₁) => if d = '0' ∧ neg = false then some (lexHexP j₁ p) else none
        | _ => none : Option (Except ParseError (Tok × s.Pos × TextPos))) = none := by
      split
      · rename_i heq; simp at heq; exact absurd heq.1 hd
      · rename_i heq; simp at heq; exact absurd heq.1 hx
      · rfl
    rw [this]
    split
    · rename_i heq; rw [← ha] at heq; simp at heq; exact absurd heq.1 hd
    · rename_i heq; rw [← ha] at heq; simp at heq; exact absurd heq.1 hx
    · rfl

/-- `lexNumber`, over positions. -/
def lexNumberP (neg : Bool) (d : Char) (i : s.Pos) (p : TextPos) :
    Except ParseError (Tok × s.Pos × TextPos) :=
  match lexFloatP neg d i p with
  | some r => r
  | none => lexIntP neg d i p

theorem lexNumberP_eq (neg : Bool) (d : Char) (i : s.Pos) (p : TextPos) :
    (lexNumberP neg d i p).map (fun x => (x.1, chars x.2.1, x.2.2)) =
      (lexNumber neg d (chars i) p).map (fun x => (x.1, x.2.1.1, x.2.2)) := by
  unfold lexNumberP lexNumber
  have h := lexFloatP_eq neg d i p
  rcases hx : lexFloatP neg d i p with _ | r <;> rcases hy : lexFloat neg d (chars i) p with _ | r' <;>
    rw [hx, hy] at h <;> simp only [Option.map_none, Option.map_some, reduceCtorEq,
      Option.some.injEq] at h
  · exact lexIntP_eq neg d i p
  · exact h

end FirRef
