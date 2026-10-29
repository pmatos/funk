import Fir.Core.Signature
import Fir.Execution.Values

/-!
The values of the core dialect. A value of `iN` is poison or an `N`-bit
vector: `⟦iN⟧ = PoisonOr (BitVec N)`. Lean's `BitVec N` exists for every `N`,
so the semantics treats every width alike (S2, ADR-2026-10-29-2007).

`ptr` has no values in M0: validation rejects every value of type `ptr`,
because their meaning waits for the memory model (S3). Its denotation is the
empty type until then.
-/

namespace Fir

/-- `⟦iN⟧` is `PoisonOr (BitVec N)`; `⟦ptr⟧` is empty in M0. -/
def Core.Ty.toType : Core.Ty → Type
  | .int w => PoisonOr (BitVec w)
  | .ptr => Empty

instance : TyDenote Core.Ty := ⟨Core.Ty.toType⟩

/-- Core values refine as `PoisonOr` values: poison is refined by any value. -/
def Core.Ty.IsRefinedBy : {t : Core.Ty} → ⟦t⟧ → ⟦t⟧ → Prop
  | .int _, a, b => PoisonOr.IsRefinedBy a b
  | .ptr, a, _ => nomatch (a : Empty)

instance : TyRefinement Core.Ty := ⟨Core.Ty.IsRefinedBy⟩

/--
The observation of a run of a core function: the values it returns. A
returned list is refined by a list of the same types whose values refine it
one by one.
-/
abbrev Core.Obs := List (DVal CoreDialect)

end Fir
