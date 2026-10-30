import Fir

/-!
The sum of two dialects, for the Lean tests. A module that mixes the ops of
two dialects needs one dialect that holds both. `SumDialect Ty Op₁ Op₂` holds
the ops of the dialects `⟨Op₁, Ty⟩` and `⟨Op₂, Ty⟩`, which share their types:
the second adds ops over the first's types, as the toy dialect adds an op
over the core dialect's integers. Each class of a dialect is lifted to the
sum. An op of either side has the signature, the text, the rules, the poison
class and the semantics that its own dialect gives it, and the types have the
text and the validity that the first dialect gives them. The classes of the
types themselves, such as `TyDenote`, are the shared types' own, so the sum
needs no instance of them. Two dialects whose ops meet the poison
obligations make a sum whose ops meet them (`SumDialect.lawfulPoison`).

Reading an op sends its name to one side, by the name alone, and that side
decodes it: `SumRoute` says which names go to the second dialect. Given two
dialects with lawful text, the sum's text is lawful exactly when every op
name goes to its own side (`SumDialect.lawful_iff`), so only when no op name
belongs to both sides (`SumDialect.names_disjoint`).

The sum lives with the tests. How real dialects name their ops and are
combined is H4, which is not decided. The rule by which test dialects route
their names is ADR-2026-10-30-2040.
-/

namespace FirTest

open Fir

/-- The dialect that holds the ops of two dialects over the types `Ty`. -/
abbrev SumDialect (Ty Op₁ Op₂ : Type) : Dialect := ⟨Op₁ ⊕ Op₂, Ty⟩

/-- Which op names a sum of two dialects sends to its second dialect:
`second n` says that the name `n` is read as an op of the second, and every
other name as an op of the first. -/
class SumRoute (Op₁ Op₂ : Type) where
  second : String → Bool

namespace SumDialect

variable {Ty Op₁ Op₂ : Type}

/-- The context of an op of the sum, as one of its dialects sees it: the
same symbol table, and the same result types. -/
def sideContext (Op : Type) (ctx : OpContext (SumDialect Ty Op₁ Op₂)) : OpContext ⟨Op, Ty⟩ :=
  ⟨fun s => (ctx.symbols s).map fun t => ⟨t.params, t.results⟩, ctx.results⟩

instance [DialectSignature ⟨Op₁, Ty⟩] [DialectSignature ⟨Op₂, Ty⟩] :
    DialectSignature (SumDialect Ty Op₁ Op₂) where
  sig
    | .inl o => sig (d := ⟨Op₁, Ty⟩) o
    | .inr o => sig (d := ⟨Op₂, Ty⟩) o
  returnTypes
    | .inl o => returnTypes (d := ⟨Op₁, Ty⟩) o
    | .inr o => returnTypes (d := ⟨Op₂, Ty⟩) o
  isTerminator
    | .inl o => isTerminator (d := ⟨Op₁, Ty⟩) o
    | .inr o => isTerminator (d := ⟨Op₂, Ty⟩) o
  succCount
    | .inl o => succCount (d := ⟨Op₁, Ty⟩) o
    | .inr o => succCount (d := ⟨Op₂, Ty⟩) o

instance [DialectValidation ⟨Op₁, Ty⟩] [DialectValidation ⟨Op₂, Ty⟩] :
    DialectValidation (SumDialect Ty Op₁ Op₂) where
  validTy := validTy (d := ⟨Op₁, Ty⟩)
  symbolRefs
    | .inl o => symbolRefs (d := ⟨Op₁, Ty⟩) o
    | .inr o => symbolRefs (d := ⟨Op₂, Ty⟩) o
  validOp ctx
    | .inl o => validOp (sideContext Op₁ ctx) o
    | .inr o => validOp (sideContext Op₂ ctx) o

instance [DialectValidation ⟨Op₁, Ty⟩] [DialectValidation ⟨Op₂, Ty⟩]
    [DecidableDialectValidation ⟨Op₁, Ty⟩] [DecidableDialectValidation ⟨Op₂, Ty⟩] :
    DecidableDialectValidation (SumDialect Ty Op₁ Op₂) where
  decValidTy t := inferInstanceAs (Decidable (validTy (d := ⟨Op₁, Ty⟩) t))
  decValidOp ctx
    | .inl o => inferInstanceAs (Decidable (validOp (sideContext Op₁ ctx) o))
    | .inr o => inferInstanceAs (Decidable (validOp (sideContext Op₂ ctx) o))

instance [DialectPoison ⟨Op₁, Ty⟩] [DialectPoison ⟨Op₂, Ty⟩] :
    DialectPoison (SumDialect Ty Op₁ Op₂) where
  poisonClass
    | .inl o => poisonClass (d := ⟨Op₁, Ty⟩) o
    | .inr o => poisonClass (d := ⟨Op₂, Ty⟩) o

instance [TyDenote Ty] [DialectSignature ⟨Op₁, Ty⟩] [DialectSignature ⟨Op₂, Ty⟩]
    {m : Type → Type} [DialectDenote ⟨Op₁, Ty⟩ m] [DialectDenote ⟨Op₂, Ty⟩ m] :
    DialectDenote (SumDialect Ty Op₁ Op₂) m where
  denote
    | .inl o, args => DialectDenote.denote (d := ⟨Op₁, Ty⟩) o args
    | .inr o, args => DialectDenote.denote (d := ⟨Op₂, Ty⟩) o args
  exit
    | .inl o, args => DialectDenote.exit (d := ⟨Op₁, Ty⟩) o args
    | .inr o, args => DialectDenote.exit (d := ⟨Op₂, Ty⟩) o args

/-- Two dialects whose ops meet the poison obligations make a sum whose ops
meet them: each op meets them as its own dialect's op. -/
instance lawfulPoison [TyDenote Ty] [TyPoison Ty] [TyRefinement Ty]
    [DialectSignature ⟨Op₁, Ty⟩] [DialectSignature ⟨Op₂, Ty⟩]
    [DialectPoison ⟨Op₁, Ty⟩] [DialectPoison ⟨Op₂, Ty⟩]
    [DialectDenote ⟨Op₁, Ty⟩ SetM] [DialectDenote ⟨Op₂, Ty⟩ SetM]
    [h₁ : LawfulDialectPoison ⟨Op₁, Ty⟩] [h₂ : LawfulDialectPoison ⟨Op₂, Ty⟩] :
    LawfulDialectPoison (SumDialect Ty Op₁ Op₂) where
  poison_isRefinedBy := h₁.poison_isRefinedBy
  propagates
    | .inl o, hc => ⟨(h₁.propagates o hc).1, (h₁.propagates o hc).2⟩
    | .inr o, hc => ⟨(h₂.propagates o hc).1, (h₂.propagates o hc).2⟩
  returnsOnDefined
    | .inl o, hc => h₁.returnsOnDefined o hc
    | .inr o, hc => h₂.returnsOnDefined o hc
  total
    | .inl o => h₁.total o
    | .inr o => h₂.total o
  monotone
    | .inl o => h₁.monotone o
    | .inr o => h₂.monotone o

variable [SumRoute Op₁ Op₂] [DialectText ⟨Op₁, Ty⟩] [DialectText ⟨Op₂, Ty⟩]

/-- Reads an op of the sum: its name goes to one side, which decodes it. -/
def decodeOp (n : String) (as : List Attr) (ts rs : List Ty) : Option (Op₁ ⊕ Op₂) :=
  if SumRoute.second (Op₁ := Op₁) (Op₂ := Op₂) n then
    (Fir.decodeOp (d := ⟨Op₂, Ty⟩) n as ts rs).map .inr
  else (Fir.decodeOp (d := ⟨Op₁, Ty⟩) n as ts rs).map .inl

instance : DialectText (SumDialect Ty Op₁ Op₂) where
  opName
    | .inl o => opName (d := ⟨Op₁, Ty⟩) o
    | .inr o => opName (d := ⟨Op₂, Ty⟩) o
  opAttrs
    | .inl o => opAttrs (d := ⟨Op₁, Ty⟩) o
    | .inr o => opAttrs (d := ⟨Op₂, Ty⟩) o
  decodeOp := decodeOp
  tyAttr := tyAttr (d := ⟨Op₁, Ty⟩)
  decodeTy := decodeTy (d := ⟨Op₁, Ty⟩)

/-- Decoding an op of the sum gives an op of the side its name goes to,
which that side decodes. -/
theorem decodeOp_eq_some {n : String} {as : List Attr} {ts rs : List Ty} {op : Op₁ ⊕ Op₂}
    (h : decodeOp n as ts rs = some op) :
    match op with
    | .inl o => Fir.decodeOp (d := ⟨Op₁, Ty⟩) n as ts rs = some o
    | .inr o => Fir.decodeOp (d := ⟨Op₂, Ty⟩) n as ts rs = some o := by
  unfold decodeOp at h
  split at h <;> obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp h <;> exact ho

/-!
# When the sum's text is lawful
-/

variable (Ty Op₁ Op₂) in
/-- Every op name goes to its own side: no name of the first dialect goes to
the second, and every name of the second does. -/
def Routes : Prop :=
  (∀ o : Op₁, SumRoute.second (Op₁ := Op₁) (Op₂ := Op₂) (opName (d := ⟨Op₁, Ty⟩) o) = false) ∧
  ∀ o : Op₂, SumRoute.second (Op₁ := Op₁) (Op₂ := Op₂) (opName (d := ⟨Op₂, Ty⟩) o) = true

variable [DialectSignature ⟨Op₁, Ty⟩] [DialectSignature ⟨Op₂, Ty⟩]
  [DialectValidation ⟨Op₁, Ty⟩] [DialectValidation ⟨Op₂, Ty⟩]

/-- If the sum's text is lawful, every op name goes to its own side: reading
an op back must reach the side that wrote it. -/
theorem routes_of_lawful [LawfulDialectText (SumDialect Ty Op₁ Op₂)] : Routes Ty Op₁ Op₂ := by
  refine ⟨fun o => ?_, fun o => ?_⟩
  · have h := LawfulDialectText.decodeOp_encode (d := SumDialect Ty Op₁ Op₂) (.inl o)
    change decodeOp (opName (d := ⟨Op₁, Ty⟩) o) _ _ _ = _ at h
    cases hs : SumRoute.second (Op₁ := Op₁) (Op₂ := Op₂) (opName (d := ⟨Op₁, Ty⟩) o)
    · rfl
    · simp [decodeOp, hs] at h
  · have h := LawfulDialectText.decodeOp_encode (d := SumDialect Ty Op₁ Op₂) (.inr o)
    change decodeOp (opName (d := ⟨Op₂, Ty⟩) o) _ _ _ = _ at h
    cases hs : SumRoute.second (Op₁ := Op₁) (Op₂ := Op₂) (opName (d := ⟨Op₂, Ty⟩) o)
    · simp [decodeOp, hs] at h
    · rfl

/-- The sum's text is lawful only when no op name belongs to both of its
dialects. -/
theorem names_disjoint [LawfulDialectText (SumDialect Ty Op₁ Op₂)] (o₁ : Op₁) (o₂ : Op₂) :
    opName (d := ⟨Op₁, Ty⟩) o₁ ≠ opName (d := ⟨Op₂, Ty⟩) o₂ := by
  intro h
  have h₁ := (routes_of_lawful (Ty := Ty) (Op₁ := Op₁) (Op₂ := Op₂)).1 o₁
  rw [h, (routes_of_lawful (Ty := Ty) (Op₁ := Op₁) (Op₂ := Op₂)).2 o₂] at h₁
  cases h₁

variable [LawfulDialectText ⟨Op₁, Ty⟩] [LawfulDialectText ⟨Op₂, Ty⟩]

/-- Two dialects with lawful text whose op names each go to their own side
make a sum with lawful text. -/
theorem lawful (h : Routes Ty Op₁ Op₂) : LawfulDialectText (SumDialect Ty Op₁ Op₂) where
  decodeOp_encode
    | .inl o => by
      change decodeOp (opName (d := ⟨Op₁, Ty⟩) o) (opAttrs (d := ⟨Op₁, Ty⟩) o)
        (sig (d := ⟨Op₁, Ty⟩) o) (returnTypes (d := ⟨Op₁, Ty⟩) o) = some (.inl o)
      simp [decodeOp, h.1 o, LawfulDialectText.decodeOp_encode]
    | .inr o => by
      change decodeOp (opName (d := ⟨Op₂, Ty⟩) o) (opAttrs (d := ⟨Op₂, Ty⟩) o)
        (sig (d := ⟨Op₂, Ty⟩) o) (returnTypes (d := ⟨Op₂, Ty⟩) o) = some (.inr o)
      simp [decodeOp, h.2 o, LawfulDialectText.decodeOp_encode]
  encode_decodeOp n as ts rs
    | .inl o, hd => LawfulDialectText.encode_decodeOp (d := ⟨Op₁, Ty⟩) n as ts rs o
        (decodeOp_eq_some hd)
    | .inr o, hd => LawfulDialectText.encode_decodeOp (d := ⟨Op₂, Ty⟩) n as ts rs o
        (decodeOp_eq_some hd)
  decodeTy_encode := LawfulDialectText.decodeTy_encode (d := ⟨Op₁, Ty⟩)
  encode_decodeTy := LawfulDialectText.encode_decodeTy (d := ⟨Op₁, Ty⟩)
  opName_isWord
    | .inl o => LawfulDialectText.opName_isWord (d := ⟨Op₁, Ty⟩) o
    | .inr o => LawfulDialectText.opName_isWord (d := ⟨Op₂, Ty⟩) o
  opAttrs_writable
    | .inl o => LawfulDialectText.opAttrs_writable (d := ⟨Op₁, Ty⟩) o
    | .inr o => LawfulDialectText.opAttrs_writable (d := ⟨Op₂, Ty⟩) o
  tyAttr_isType := LawfulDialectText.tyAttr_isType (d := ⟨Op₁, Ty⟩)

/-- Given two dialects with lawful text, the sum's text is lawful exactly
when every op name goes to its own side. -/
theorem lawful_iff : LawfulDialectText (SumDialect Ty Op₁ Op₂) ↔ Routes Ty Op₁ Op₂ :=
  ⟨fun _ => routes_of_lawful, lawful⟩

end SumDialect

end FirTest
