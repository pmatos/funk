import Fir
import FirRef

/-!
G0's check on the Lean side, for region kinds that a dialect registers
(ADR-2026-11-03-0600, ADR-2026-11-10-1941), split from `FirTest.G0` by
subject. Each statement below is made of an arbitrary dialect `d`,
or an arbitrary base and extension, with the spec's own proof, so it builds
only while those stay parameterized over the dialect. `scripts/check_g0.py`
checks this file as it checks the other files of `FirTest/G0/`, outside its
`#guard` commands.

They restate, for dialects with region kinds of their own, the validation
results: a valid op's regions obey the rules of their kinds, which the
check decides and `fir-ref` runs unchanged, and no valid op owns a region of
the core's kind, the only kind the interpreter runs; and the round-trip
results: a sum whose extension registers kinds keeps its text lawful, so
its well-formed modules round-trip. `lean/FirTest/RegionKindCases.lean`
instantiates them with a toy kind whose ops are unordered.
-/

namespace FirTest.G0

open Fir

/-! # Validation -/

/-- In a valid function of every dialect, each region of an op of its body
is of a kind that the dialect registers, and obeys the rule of that kind. -/
theorem regionValid_of_valid (d : Dialect) [DialectSignature d] [DialectValidation d]
    {ctx : ModuleContext d} {f : Func d} (h : f.Valid ctx) {b : Block d} (hb : b ∈ f.blocks)
    {i : Nat} {o : Operation d} (ho : b.body[i]? = some o) {r : Region d} (hr : r ∈ o.regions)
    {k : Name} (hk : r.kind = some k) :
    k ∈ regionKindNames (d := d) ∧ validRegion (DialectView.id d) k ⟨ctx.symbols⟩ f r :=
  ((h.ops b hb i o ho).1.2 r hr k hk).2

/-- In a valid function of every dialect, each region of an op inside a
region, at any depth, is of a kind that the dialect registers, and obeys
the rule of that kind. -/
theorem innerRegionValid_of_valid (d : Dialect) [DialectSignature d] [DialectValidation d]
    {ctx : ModuleContext d} {f : Func d} (h : f.Valid ctx) {b : Block d} (hb : b ∈ f.allBlocks)
    {o : Operation d} (ho : o ∈ b.body) {o' : Operation d} (ho' : o' ∈ o.innerOps)
    {r : Region d} (hr : r ∈ o'.regions) {k : Name} (hk : r.kind = some k) :
    k ∈ regionKindNames (d := d) ∧ validRegion (DialectView.id d) k ⟨ctx.symbols⟩ f r :=
  ((h.inner b hb o ho o' ho').1.2 r hr k hk).2

/-- In a valid function of every dialect, no op of its body owns a region of
the core's kind: the interpreter runs only that kind, a function's body, and
leaves a region of a dialect's kind to its dialect's semantics. -/
theorem noCoreRegion_of_valid (d : Dialect) [DialectSignature d] [DialectValidation d]
    {ctx : ModuleContext d} {f : Func d} (h : f.Valid ctx) {b : Block d} (hb : b ∈ f.blocks)
    {i : Nat} {o : Operation d} (ho : b.body[i]? = some o) : o.ownsCoreRegion = false :=
  (h.ops b hb i o ho).1.noCoreRegion

/-- In a valid function of every dialect, no op inside a region, at any
depth, owns a region of the core's kind either. -/
theorem innerNoCoreRegion_of_valid (d : Dialect) [DialectSignature d] [DialectValidation d]
    {ctx : ModuleContext d} {f : Func d} (h : f.Valid ctx) {b : Block d} (hb : b ∈ f.allBlocks)
    {o : Operation d} (ho : o ∈ b.body) {o' : Operation d} (ho' : o' ∈ o.innerOps) :
    o'.ownsCoreRegion = false :=
  (h.inner b hb o ho o' ho').1.noCoreRegion

/-- The check of an op's regions decides their validity, for every dialect
whose rules are decidable. -/
theorem regionProblems_eq_nil (d : Dialect) [DialectSignature d] [DialectValidation d]
    [DecidableDialectValidation d] {lk : Lookup d} {ctx : ModuleContext d} (h : lk.Agrees ctx)
    (f : Func d) (at_ : String → Problem) (o : Operation d) :
    regionProblems lk f at_ o = [] ↔ f.RegionsValid ctx o :=
  Fir.regionProblems_eq_nil h

/-- `fir-ref`'s check of a function, regions and their kinds included, is
the spec's, for every dialect. -/
theorem firRef_problemsIn (d : Dialect) [DialectSignature d] [DialectValidation d]
    [DecidableEq d.Ty] [DecidableDialectValidation d] (lk : Lookup d) (f : Func d)
    (all : List (Block d)) : FirRef.problemsIn lk f all = f.problemsIn lk all := by
  rw [FirRef.problemsIn_eq_problemsIn]

/-- In a sum, a region of a kind that the extension registers obeys the
extension's rule, for every base whose words name only dialects of its set
and every extension that writes its kinds under its own name, new to the
base. -/
theorem validRegion_ext (base e : Dialect) [TyDenote base.Ty] [TyDenote e.Ty] [DialectName e]
    [DialectText base] [DialectText (base.over e)] [DialectValidation base]
    [DialectValidation (base.over e)] [DialectSet base] [LawfulDialectSet base]
    [LawfulDialectName base e] (hn : name e ∉ names base) {host : Dialect}
    (v : DialectView (base ⊞ e) host) {k : Name} (hk : k ∈ regionKindNames (d := base.over e))
    (ctx : FuncContext host) (f : Func host) (r : Region host) :
    validRegion (d := base ⊞ e) v k ctx f r ↔
      validRegion (d := base.over e) (Dialect.sum.extView v) k ctx f r :=
  Dialect.sum.validRegion_ext hn v hk ctx f r

/-! # The round trip -/

/-- `parse(print(m)) == m` for every well-formed module of a sum, for every
base and every extension whose text is lawful and that writes its words and
its region kinds under its own name, new to the base. -/
theorem sum_printThenParse (base e : Dialect) [TyDenote base.Ty] [TyDenote e.Ty] [DialectName e]
    [DialectSignature base] [DialectSignature (base.over e)] [DialectText base]
    [DialectText (base.over e)] [DialectValidation base] [DialectValidation (base.over e)]
    [LawfulDialectText base] [LawfulDialectText (base.over e)] [DialectSet base]
    [LawfulDialectSet base] [LawfulDialectName base e] (hn : name e ∉ names base) :
    PrintThenParse (d := base ⊞ e) Fir.parse :=
  Dialect.sum.printThenParse hn

/-- Every valid module of such a sum is well formed. -/
theorem sum_validIsWellFormed (base e : Dialect) [TyDenote base.Ty] [TyDenote e.Ty]
    [DialectName e] [DialectSignature base] [DialectSignature (base.over e)] [DialectText base]
    [DialectText (base.over e)] [DialectValidation base] [DialectValidation (base.over e)]
    [LawfulDialectText base] [LawfulDialectText (base.over e)] [DialectSet base]
    [LawfulDialectSet base] [LawfulDialectName base e] (hn : name e ∉ names base) :
    ValidIsWellFormed (d := base ⊞ e) :=
  Dialect.sum.validIsWellFormed hn

end FirTest.G0
