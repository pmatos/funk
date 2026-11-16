import FirTest.G0
import FirTest.G0Effects

/-!
G0's generic results restated for a dialect set that includes `gpu`
(ADR-2026-11-09-1545, stage 4 of the stage plan on #212): the round trip,
validation, region kinds and the obligations of effects, for the sum of
the core and `gpu`, `CoreGpu`, and for the core as a base with `gpu`'s
extension, `GpuExt`. Each statement applies the theorem of `FirTest.G0`
that states the result for every dialect, so it builds only while that
theorem stays generic and the sum meets its hypotheses with no assumption
of its own. `scripts/check_g0.py` keeps `CoreGpu` out of the generic tests,
so its instances live here, in a test of the dialect's own.
`FirTest.GpuG0Runs` restates the results about runs, refinement and
congruence.

The results with memory hold at every work-item. A statement that applies
to a function does so for the functions of each symbol table of a valid
module, nested at any depth, run in the module of that table
(`Module.nest`): a device module's kernels are among them.
-/

namespace FirTest.GpuG0

open Fir Fir.Gpu

/-! # The text format -/

/-- `fir-ref`'s parser is the spec's for the sum. -/
theorem firRef_parse (t : String) : FirRef.parse (d := CoreGpu) t = Fir.parse t :=
  G0.firRef_parse CoreGpu t

/-- `fir-ref`'s printer is the spec's for the sum. -/
theorem firRef_print (m : Module CoreGpu) : FirRef.printModule m = m.print :=
  G0.firRef_print CoreGpu m

/-- `parse(print(m)) == m` for every well-formed module of the sum. -/
theorem printThenParse : PrintThenParse (d := CoreGpu) Fir.parse :=
  G0.printThenParse CoreGpu

/-- `print(parse(t)) == t` for every text printed from a well-formed module
of the sum. -/
theorem parseThenPrint : ParseThenPrint (d := CoreGpu) Fir.parse :=
  G0.parseThenPrint CoreGpu

/-- What the parser reads in the sum is well formed. -/
theorem parse_wellFormed {t : String} {m : Module CoreGpu} (h : Fir.parse t = .ok m) :
    m.WellFormed :=
  G0.parse_wellFormed CoreGpu h

/-- Every valid module of the sum is well formed. -/
theorem validIsWellFormed : ValidIsWellFormed (d := CoreGpu) :=
  G0.validIsWellFormed CoreGpu

/-- The round trip of a sum, at the core and `gpu`: `gpu` writes its words
and its region kinds under its own name, new to the core. -/
theorem sum_printThenParse : PrintThenParse (d := CoreDialect ⊞ GpuExt) Fir.parse :=
  G0.sum_printThenParse CoreDialect GpuExt Gpu.name_new

/-- Every valid module of the sum of the core and `gpu` is well formed. -/
theorem sum_validIsWellFormed : ValidIsWellFormed (d := CoreDialect ⊞ GpuExt) :=
  G0.sum_validIsWellFormed CoreDialect GpuExt Gpu.name_new

/-! # Validation -/

/-- The check decides validity in the sum. -/
theorem problems_eq_nil_iff (m : Module CoreGpu) : m.problems = [] ↔ m.Valid :=
  G0.problems_eq_nil_iff CoreGpu m

/-- The check of a module's dialect set decides its rule in the sum. -/
theorem setProblems_eq_nil_iff (m : Module CoreGpu) : m.setProblems = [] ↔ m.InDialectSet :=
  G0.setProblems_eq_nil_iff CoreGpu m

/-- `fir-ref`'s check of a dialect set is the spec's for the sum. -/
theorem firRef_setProblems (m : Module CoreGpu) : FirRef.moduleSetProblems m = m.setProblems :=
  G0.firRef_setProblems CoreGpu m

/-- A valid function of the sum obeys the sum's rule over a whole
function. -/
theorem validFunc_of_valid {ctx : ModuleContext CoreGpu} {f : Func CoreGpu} (h : f.Valid ctx) :
    validFunc (DialectView.id CoreGpu) ⟨ctx.symbols⟩ f :=
  G0.validFunc_of_valid CoreGpu h

/-- A valid item of a kind of the sum obeys the rule for its kind. -/
theorem validItem_of_valid {ctx : FuncContext CoreGpu} {i : DialectItem CoreGpu}
    (h : i.Valid ctx) : validItem (DialectView.id CoreGpu) ctx i :=
  G0.validItem_of_valid CoreGpu h

/-- The check of an item of a kind of the sum decides its validity. -/
theorem dialectItemProblems_eq_nil_iff (ctx : FuncContext CoreGpu) (i : DialectItem CoreGpu) :
    i.problems ctx = [] ↔ i.Valid ctx :=
  G0.dialectItemProblems_eq_nil_iff CoreGpu ctx i

/-- `fir-ref`'s check of an item of a kind of the sum is the spec's. -/
theorem firRef_dialectItemProblems (ctx : FuncContext CoreGpu) (i : DialectItem CoreGpu) :
    FirRef.dialectItemProblems ctx i = i.problems ctx :=
  G0.firRef_dialectItemProblems CoreGpu ctx i

/-- An item of a kind that `gpu` registers obeys `gpu`'s rule in the sum. -/
theorem validItem_ext {host : Dialect} (v : DialectView (CoreDialect ⊞ GpuExt) host)
    (ctx : FuncContext host) {i : DialectItem host}
    (hk : i.kind ∈ itemKindNames (d := CoreDialect.over GpuExt)) :
    validItem (d := CoreDialect ⊞ GpuExt) v ctx i ↔
      validItem (d := CoreDialect.over GpuExt) (Dialect.sum.extView v) ctx i :=
  G0.validItem_ext CoreDialect GpuExt Gpu.name_new v ctx hk

/-! # Region kinds -/

/-- In a valid function of the sum, each region of an op of its body is of a
kind that the sum registers, and obeys its rule. -/
theorem regionValid_of_valid {ctx : ModuleContext CoreGpu} {f : Func CoreGpu} (h : f.Valid ctx)
    {b : Block CoreGpu} (hb : b ∈ f.blocks) {i : Nat} {o : Operation CoreGpu}
    (ho : b.body[i]? = some o) {r : Region CoreGpu} (hr : r ∈ o.regions) {k : Name}
    (hk : r.kind = some k) :
    k ∈ regionKindNames (d := CoreGpu) ∧ validRegion (DialectView.id CoreGpu) k ⟨ctx.symbols⟩ f r :=
  G0.regionValid_of_valid CoreGpu h hb ho hr hk

/-- So too for each region of an op inside a region, at any depth. -/
theorem innerRegionValid_of_valid {ctx : ModuleContext CoreGpu} {f : Func CoreGpu}
    (h : f.Valid ctx) {b : Block CoreGpu} (hb : b ∈ f.allBlocks) {o : Operation CoreGpu}
    (ho : o ∈ b.body) {o' : Operation CoreGpu} (ho' : o' ∈ o.innerOps) {r : Region CoreGpu}
    (hr : r ∈ o'.regions) {k : Name} (hk : r.kind = some k) :
    k ∈ regionKindNames (d := CoreGpu) ∧ validRegion (DialectView.id CoreGpu) k ⟨ctx.symbols⟩ f r :=
  G0.innerRegionValid_of_valid CoreGpu h hb ho ho' hr hk

/-- In a valid function of the sum, no op of its body owns a region of the
core's kind. -/
theorem noCoreRegion_of_valid {ctx : ModuleContext CoreGpu} {f : Func CoreGpu} (h : f.Valid ctx)
    {b : Block CoreGpu} (hb : b ∈ f.blocks) {i : Nat} {o : Operation CoreGpu}
    (ho : b.body[i]? = some o) : o.ownsCoreRegion = false :=
  G0.noCoreRegion_of_valid CoreGpu h hb ho

/-- Nor does an op inside a region, at any depth. -/
theorem innerNoCoreRegion_of_valid {ctx : ModuleContext CoreGpu} {f : Func CoreGpu}
    (h : f.Valid ctx) {b : Block CoreGpu} (hb : b ∈ f.allBlocks) {o : Operation CoreGpu}
    (ho : o ∈ b.body) {o' : Operation CoreGpu} (ho' : o' ∈ o.innerOps) :
    o'.ownsCoreRegion = false :=
  G0.innerNoCoreRegion_of_valid CoreGpu h hb ho ho'

/-- The check of an op's regions decides their validity in the sum. -/
theorem regionProblems_eq_nil {lk : Lookup CoreGpu} {ctx : ModuleContext CoreGpu}
    (h : lk.Agrees ctx) (f : Func CoreGpu) (at_ : String → Problem) (o : Operation CoreGpu) :
    regionProblems lk f at_ o = [] ↔ f.RegionsValid ctx o :=
  G0.regionProblems_eq_nil CoreGpu h f at_ o

/-- `fir-ref`'s check of a function of the sum is the spec's. -/
theorem firRef_problemsIn (lk : Lookup CoreGpu) (f : Func CoreGpu) (all : List (Block CoreGpu)) :
    FirRef.problemsIn lk f all = f.problemsIn lk all :=
  G0.firRef_problemsIn CoreGpu lk f all

/-- A region of a kind that `gpu` registers obeys `gpu`'s rule in the
sum. -/
theorem validRegion_ext {host : Dialect} (v : DialectView (CoreDialect ⊞ GpuExt) host) {k : Name}
    (hk : k ∈ regionKindNames (d := CoreDialect.over GpuExt)) (ctx : FuncContext host)
    (f : Func host) (r : Region host) :
    validRegion (d := CoreDialect ⊞ GpuExt) v k ctx f r ↔
      validRegion (d := CoreDialect.over GpuExt) (Dialect.sum.extView v) k ctx f r :=
  G0.validRegion_ext CoreDialect GpuExt Gpu.name_new v hk ctx f r

end FirTest.GpuG0
