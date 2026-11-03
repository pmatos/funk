import FirTest.ValidSum
import FirTest.RunsCalls
import FirTest.Mixed

/-!
Tests of #11's round trip, `printThenParse`, and of what follows from it,
applied to concrete modules. The spec's example module and the module of
`@fact`, `@even` and `@odd` are valid, so each reads back from its printed
text, and no other valid module prints the same text. A module that is well
formed but not valid reads back too: its `add` owns a region, which no core
op may, and the region's block defines values that the first pass of
decoding reads between the results of the ops around it. A module of the
sum of the core dialect and a test dialect reads back from the laws of the
sum's text alone, and so does every well-formed module of the test dialect
by itself. The `#guard`s run the parser on the same modules. The last
checks pin the axioms of the theorems to Lean's standard ones.
-/

namespace FirTest

open Fir Core Example

/-! # Valid modules -/

/-- The spec's example module reads back from its printed text. -/
theorem sumModule_parse_print : Fir.parse sumModule.print = .ok sumModule :=
  sumModule_valid.parse_print

/-- The module of `@fact`, `@even` and `@odd` reads back from its printed
text. -/
theorem recModule_parse_print : Fir.parse recModule.print = .ok recModule :=
  recModule_valid.parse_print

/-- Whatever reads from the example module's text prints as that text. -/
theorem sumModule_reprint (m : Module CoreDialect) (h : Fir.parse sumModule.print = .ok m) :
    m.print = sumModule.print :=
  Core.parseThenPrint sumModule (Core.validIsWellFormed _ sumModule_valid) m h

/-- No other valid module prints as the example module does. -/
theorem sumModule_print_unique {m : Module CoreDialect} (h : m.Valid)
    (he : m.print = sumModule.print) : m = sumModule :=
  Core.print_injective h sumModule_valid he

#guard match Fir.parse (d := CoreDialect) recModule.print with
  | .ok m => m.print == recModule.print
  | .error _ => false

/-! # A module that is well formed but not valid -/

/-- `@f`, whose first `add` owns a region. The region's block defines `%y`
and `%b`, which the first pass reads after `%a` and before `%c`, while
`Func.defs` lists `%c` before them. -/
def regionFn : Func CoreDialect where
  name := "f"
  params := [("x", i 8)]
  results := [i 8]
  body := ⟨[⟨"entry", [], [
    { op [("a", i 8)] (.add 8 {}) ["x", "x"] with
      regions := [⟨[⟨"in", [("y", i 8)], [
        op [("b", i 8)] (.add 8 { nsw := true }) ["y", "a"],
        op [] (.ret [i 8]) ["b"]]⟩]⟩] },
    op [("c", i 8)] (.add 8 {}) ["a", "a"],
    op [] (.ret [i 8]) ["c"]]⟩]⟩

/-- The module of `@f`. -/
def regionModule : Module CoreDialect := ⟨[.func regionFn], [(0, .unknown)]⟩

/-- `@f` is well formed: its names are unique and can be written, its types
are valid, and each op's operands have the types of its signature. -/
theorem regionFn_wellFormed : regionFn.WellFormed where
  namesUnique := by decide +kernel
  names x hx := Text.isName_iff.2 (by revert x; decide +kernel)
  labels b hb := Text.isName_iff.2 (by revert b; decide +kernel)
  types t ht :=
    have hv : validTy t := by revert t; decide +kernel
    ⟨LawfulDialectText.tyAttr_isType t hv, LawfulDialectText.decodeTy_encode t hv⟩
  ops o ho := by
    have h : o.operands.map regionFn.typeOf = (sig o.op).map some ∧
        o.results.map (·.2) = returnTypes o.op ∧ o.succs = [] ∧ o.loc < Location.limit := by
      revert o; decide +kernel
    refine ⟨LawfulDialectText.opName_isWord _, LawfulDialectText.opAttrs_writable _, h.1,
      h.2.1, ?_, h.2.2.2⟩
    rw [h.2.2.1]
    exact fun s hs => nomatch hs

/-- The module of `@f` is well formed. -/
theorem regionModule_wellFormed : regionModule.WellFormed where
  funcs f hf := by
    simp only [regionModule, Module.funcs, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hf
    subst hf
    exact regionFn_wellFormed
  locs := by unfold LocTable.InLimits; decide +kernel

/-- The module of `@f` reads back from its printed text, although it is not
valid. -/
theorem regionModule_parse_print : Fir.parse regionModule.print = .ok regionModule :=
  regionModule_wellFormed.parse_print

-- The module is not valid, and the parser reads its text back.
#guard !regionModule.problems.isEmpty
#guard match Fir.parse (d := CoreDialect) regionModule.print with
  | .ok m => m.print == regionModule.print
  | .error _ => false

/-! # Another dialect -/

/-- The round trip of the toy dialect, from its own laws. -/
theorem toy_printThenParse : PrintThenParse (d := ToyDialect) Fir.parse := printThenParse

/-- The round trip of the sum of the core and the toy dialect, from the
laws of the sum's text. -/
theorem coreToy_printThenParse : PrintThenParse (d := CoreToy) Fir.parse := printThenParse

/-- The function of `FirTest.Mixed`'s mixed module, as abstract syntax: a
toy op whose result a core op uses. -/
def mixedFn : Func CoreToy :=
  ⟨"f", [("a", i 8)], [i 8, i 8], ⟨[⟨"entry", [], [
    ⟨[("m", i 8)], .inr (.mask 8 3), ["a"], [], [], 1⟩,
    ⟨[("s", i 8)], .inl (.add 8 {}), ["m", "a"], [], [], 0⟩,
    ⟨[], .inl (.ret [i 8, i 8]), ["m", "s"], [], [], 0⟩]⟩]⟩⟩

/-- The mixed module, as abstract syntax. -/
def mixedModule : Module CoreToy := ⟨[.func mixedFn], [(0, .unknown), (1, .name "mask")]⟩

#guard mixedModule.print == mixed

/-- The mixed module's function is well formed. -/
theorem mixedFn_wellFormed : mixedFn.WellFormed where
  namesUnique := by decide +kernel
  names x hx := Text.isName_iff.2 (by revert x; decide +kernel)
  labels b hb := Text.isName_iff.2 (by revert b; decide +kernel)
  types t ht :=
    have hv : validTy t := by revert t; decide +kernel
    ⟨LawfulDialectText.tyAttr_isType t hv, LawfulDialectText.decodeTy_encode t hv⟩
  ops o ho := by
    have h : o.operands.map mixedFn.typeOf = (sig o.op).map some ∧
        o.results.map (·.2) = returnTypes o.op ∧ o.succs = [] ∧ o.loc < Location.limit := by
      revert o; decide +kernel
    refine ⟨LawfulDialectText.opName_isWord _, LawfulDialectText.opAttrs_writable _, h.1,
      h.2.1, ?_, h.2.2.2⟩
    rw [h.2.2.1]
    exact fun s hs => nomatch hs

/-- The mixed module is well formed. -/
theorem mixedModule_wellFormed : mixedModule.WellFormed where
  funcs f hf := by
    simp only [mixedModule, Module.funcs, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hf
    subst hf
    exact mixedFn_wellFormed
  locs := by unfold LocTable.InLimits; decide +kernel

/-- The mixed module reads back from its printed text, `FirTest.Mixed`'s
`mixed`. -/
theorem mixedModule_parse_print : Fir.parse mixedModule.print = .ok mixedModule :=
  mixedModule_wellFormed.parse_print

/-! # The theorems' axioms -/

/--
info: 'Fir.Module.WellFormed.decodeModule_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fir.Module.WellFormed.decodeModule_eq

/-- info: 'Fir.printThenParse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.printThenParse

/-- info: 'Fir.parseThenPrint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.parseThenPrint

/--
info: 'Fir.Module.WellFormed.parse_print' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fir.Module.WellFormed.parse_print

/--
info: 'Fir.Module.WellFormed.print_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fir.Module.WellFormed.print_injective

/--
info: 'Fir.Module.WellFormed.print_inj' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fir.Module.WellFormed.print_inj

/-- info: 'Fir.Module.Valid.parse_print' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Module.Valid.parse_print

/--
info: 'Fir.Module.Valid.print_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fir.Module.Valid.print_injective

/-- info: 'Fir.Core.printThenParse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.printThenParse

/-- info: 'Fir.Core.parseThenPrint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.parseThenPrint

/-- info: 'Fir.Core.print_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.print_injective

end FirTest
