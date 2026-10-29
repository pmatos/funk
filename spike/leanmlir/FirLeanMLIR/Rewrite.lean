import FirLeanMLIR.Examples

/-!
# What LeanMLIR's rewriter gives fir

A `PeepholeRewrite` is a pair of pure terms with a proof that they denote the
same function. `rewritePeepholeAt` applies it anywhere, and
`denote_rewritePeepholeAt` proves that the result means the same: rewrites are
verified once, and applied for free.
-/

namespace FirLeanMLIR.Rewrite

open FirLeanMLIR.Examples

/-- `add %x, %y` to `add %y, %x`, without flags. -/
def addComm : PeepholeRewrite Fir [.int 32, .int 32] [.int 32] where
  lhs := .var (add 32 false ⟨0, rfl⟩ ⟨1, rfl⟩) (.rets [⟨0, rfl⟩]ₕ)
  rhs := .var (add 32 false ⟨1, rfl⟩ ⟨0, rfl⟩) (.rets [⟨0, rfl⟩]ₕ)
  correct := by
    funext V
    simp_peephole
    simp [add, Sem.add, HVector.map]
    generalize V _ = a, V _ = b
    cases a using PoisonOr.casesOn' <;> cases b using PoisonOr.casesOn' <;>
      simp [BitVec.add_comm]

/-- The entry block of `twoBlocks`. -/
def entry : Com Fir (.ofList (ints [32, 32])) .impure [.ctl] :=
  .var (add 32 false ⟨0, rfl⟩ ⟨1, rfl⟩) <|
  .var (br 1 [32, 32] [⟨0, rfl⟩, ⟨1, rfl⟩]ₕ) done

-- The rewrite fires on the block's first op...
#guard rewritePeepholeAt addComm 0 entry != entry

/-- ...and LeanMLIR proves, once for all rewrites, that the block keeps its
meaning. -/
theorem entry_rewritten :
    (rewritePeepholeAt addComm 0 entry).denote = entry.denote :=
  denote_rewritePeepholeAt _ _ _

/-- Rewrites must be pure, and `freeze` is not: a rewrite that involves
`freeze` cannot be stated as a `PeepholeRewrite`, because no proof of
`impure ≤ pure` exists. Refinement (`⊑`), not equality, is the relation such
rewrites need, and `PeepholeRewrite` takes equality only. -/
example : ¬ (EffectKind.impure ≤ EffectKind.pure) := EffectKind.not_impure_le_pure

end FirLeanMLIR.Rewrite
