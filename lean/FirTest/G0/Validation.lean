import Fir
import FirRef

/-!
G0's check on the Lean side, for validation (ADR-2026-11-03-0600): each
statement below is made of an arbitrary dialect `d`, with the spec's own
proof, as in `FirTest.G0`. It builds only while validation stays
parameterized over the dialect, and `scripts/check_g0.py` checks that no
statement here is narrowed to the core dialect. It covers the check of a
module, its dialect sets, the rule over a whole function, and the kinds of
item that a dialect registers, with their rules (ADR-2026-11-10-2224).
-/

namespace FirTest.G0

open Fir


/-- The validation check decides validity for every dialect whose rules
are decidable. -/
theorem problems_eq_nil_iff (d : Dialect) [DialectSignature d] [DialectValidation d]
    [DecidableEq d.Ty] [DecidableDialectValidation d] (m : Module d) :
    m.problems = [] ↔ m.Valid :=
  m.problems_eq_nil_iff

/-- The check of a module's dialect set decides its rule, for every dialect
with a text and a dialect set: the set names dialects of the dialect's own
set, and every word of the module names the core or a dialect of its set. -/
theorem setProblems_eq_nil_iff (d : Dialect) [DialectText d] [DialectSet d] (m : Module d) :
    m.setProblems = [] ↔ m.InDialectSet :=
  m.setProblems_eq_nil_iff

/-- `fir-ref`'s check of a module's dialect set is the spec's, for every
dialect. -/
theorem firRef_setProblems (d : Dialect) [DialectText d] [DialectSet d] (m : Module d) :
    FirRef.moduleSetProblems m = m.setProblems := by
  rw [FirRef.setProblems_eq_moduleSetProblems]

/-- A valid function obeys its dialect's own rule over a whole function, for
every dialect. -/
theorem validFunc_of_valid (d : Dialect) [DialectSignature d] [DialectValidation d]
    {ctx : ModuleContext d} {f : Func d} (h : f.Valid ctx) :
    validFunc (DialectView.id d) ⟨ctx.symbols⟩ f :=
  h.dialect

/-- A valid item of a dialect's kind obeys its dialect's rule for its kind,
for every dialect (ADR-2026-11-10-2224). -/
theorem validItem_of_valid (d : Dialect) [DialectValidation d] {ctx : FuncContext d}
    {i : DialectItem d} (h : i.Valid ctx) : validItem (DialectView.id d) ctx i :=
  h.dialect

/-- The check of an item of a dialect's kind decides its validity, for every
dialect whose rules are decidable. -/
theorem dialectItemProblems_eq_nil_iff (d : Dialect) [DialectValidation d]
    [DecidableDialectValidation d] (ctx : FuncContext d) (i : DialectItem d) :
    i.problems ctx = [] ↔ i.Valid ctx :=
  i.problems_eq_nil_iff ctx

/-- `fir-ref`'s check of an item of a dialect's kind is the spec's, for
every dialect. -/
theorem firRef_dialectItemProblems (d : Dialect) [DialectValidation d]
    [DecidableDialectValidation d] (ctx : FuncContext d) (i : DialectItem d) :
    FirRef.dialectItemProblems ctx i = i.problems ctx := by
  rw [FirRef.problems_eq_dialectItemProblems]

/-- In a sum, an item of a kind that the extension registers obeys the
extension's rule, for every base whose words name only dialects of its set
and every extension that writes its kinds under its own name, new to the
base. -/
theorem validItem_ext (base e : Dialect) [TyDenote base.Ty] [TyDenote e.Ty] [DialectName e]
    [DialectText base] [DialectText (base.over e)] [DialectValidation base]
    [DialectValidation (base.over e)] [DialectSet base] [LawfulDialectSet base]
    [LawfulDialectName base e] (hn : name e ∉ names base) {host : Dialect}
    (v : DialectView (base ⊞ e) host) (ctx : FuncContext host) {i : DialectItem host}
    (hk : i.kind ∈ itemKindNames (d := base.over e)) :
    validItem (d := base ⊞ e) v ctx i ↔ validItem (d := base.over e) (Dialect.sum.extView v) ctx i :=
  Dialect.sum.validItem_ext hn v ctx hk

end FirTest.G0
