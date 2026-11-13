import Fir
import FirRef

/-!
G0's check on the Lean side, for the poison obligations with memory
(ADR-2026-11-03-0600,
`docs/decisions/semantics-poison.md#the-obligations-with-memory`), split from
`FirTest.G0` by subject. Each statement below is made of an arbitrary
dialect `d`, or an arbitrary base and extension, with the spec's own proof,
so it builds only while those stay parameterized over the dialect.
`scripts/check_g0.py` checks this file as it checks the other files of
`FirTest/G0/`, outside its `#guard` commands.

They restate the class: every lawful dialect that lifts the set monad meets
it, the poison obligations hold of such a dialect exactly when it and
totality and monotonicity with memory do, and sums and lifts keep it with
no semantics in the set monad.
-/

namespace FirTest.G0

open Fir

/-- Every lawful dialect that lifts the set monad is lawful in its poison
with memory. -/
theorem lawfulMemPoison_ofLawful (d : Dialect) [TyDenote d.Ty] [TyPoison d.Ty] [TyRefinement d.Ty]
    [DialectSignature d] [DialectEffects d] [DialectCall d] [DialectValidation d]
    [DialectDenote d SetM] [DialectMemDenote d] [LiftsSetM d] [LawfulDialectPoison d] :
    LawfulDialectMemPoison d :=
  LawfulDialectMemPoison.ofLawful

/-- A dialect that lifts the set monad is lawful exactly when it is lawful
in its poison, its totality and its monotonicity with memory. -/
theorem lawfulPoison_iff_mem (d : Dialect) [TyDenote d.Ty] [TyPoison d.Ty] [TyRefinement d.Ty]
    [DialectSignature d] [DialectEffects d] [DialectCall d] [DialectValidation d]
    [DialectDenote d SetM] [DialectMemDenote d] [LiftsSetM d] :
    LawfulDialectPoison d ↔
      LawfulDialectMemPoison d ∧ LawfulDialectTotal d ∧ LawfulDialectMonotone d :=
  LawfulDialectPoison.iff_mem

/-- Every sum of two dialects lawful in their poison with memory is lawful
in its poison with memory, when the extension accepts the base's valid
types. Neither side needs a semantics in the set monad. -/
theorem sum_lawfulMemPoison (base e : Dialect) [TyDenote base.Ty] [TyDenote e.Ty]
    [TyPoison base.Ty] [TyPoison e.Ty] [TyRefinement base.Ty] [TyRefinement e.Ty]
    [DialectSignature base] [DialectSignature (base.over e)] [DialectEffects base]
    [DialectEffects (base.over e)] [DialectMemOver base e] [DialectMemDenote base]
    [DialectMemDenote (base.over e)] [DialectValidation base] [DialectValidation (base.over e)]
    [LawfulDialectMemPoison base] [LawfulDialectMemPoison (base.over e)]
    (hty : ∀ t : base.Ty, validTy t → validTy (d := base.over e) (.inl t)) :
    LawfulDialectMemPoison (base ⊞ e) :=
  Dialect.sum.lawfulMemPoison hty

end FirTest.G0
