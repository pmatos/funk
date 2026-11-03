import Fir
import FirRef

/-!
G0's check on the Lean side (ADR-2026-11-03-0600). fir's spec is written
once for every dialect: its parser and printer, its validation and its
interpreter take the dialect as a parameter, and see a dialect's ops only
through the dialect's classes, so the dialect's `decodeOp` and `opAttrs`
hold its text. Each statement below is made of an arbitrary dialect `d`,
with the spec's own proof or definition. It builds only while those stay
parameterized over the dialect: narrowing one of them to the core dialect
breaks this file. `scripts/check_g0.py` checks the other half, that the
code of the spec's chapters for every dialect names nothing of the core
dialect and writes none of its words. It checks this file too, outside its
`#guard` commands, so a statement below cannot be narrowed to the core
dialect.

The last section checks that every core op declares its poison class.
-/

namespace FirTest.G0

open Fir

/-! # The text format -/

/-- The parser reads a module of any dialect. -/
example (d : Dialect) [DialectText d] : Parser d := Fir.parse

/-- The printer writes a module of any dialect. -/
example (d : Dialect) [DialectText d] : Module d → String := Module.print

/-- `fir-ref` reads the bytes of a file as a module of any dialect. -/
example (d : Dialect) [DialectText d] : ByteArray → Except ParseError (Module d) :=
  FirRef.parseBytes

/-- `fir-ref`'s parser is the spec's, for every dialect. -/
theorem firRef_parse (d : Dialect) [DialectText d] (t : String) :
    FirRef.parse (d := d) t = Fir.parse t := by
  rw [FirRef.parse_eq_parse]

/-- `fir-ref`'s printer is the spec's, for every dialect. -/
theorem firRef_print (d : Dialect) [DialectText d] (m : Module d) :
    FirRef.printModule m = m.print := by
  rw [FirRef.print_eq_printModule]

/-- `parse(print(m)) == m` for every well-formed module of every dialect
whose text is lawful. -/
theorem printThenParse (d : Dialect) [DialectSignature d] [DialectValidation d] [DialectText d]
    [LawfulDialectText d] : PrintThenParse (d := d) Fir.parse :=
  Fir.printThenParse

/-- `print(parse(t)) == t` for every text printed from a well-formed module
of every dialect whose text is lawful. -/
theorem parseThenPrint (d : Dialect) [DialectSignature d] [DialectValidation d] [DialectText d]
    [LawfulDialectText d] : ParseThenPrint (d := d) Fir.parse :=
  Fir.parseThenPrint

/-- What the parser reads is well formed, for every dialect whose text is
lawful. -/
theorem parse_wellFormed (d : Dialect) [DialectSignature d] [DialectValidation d] [DialectText d]
    [LawfulDialectText d] {t : String} {m : Module d} (h : Fir.parse t = .ok m) : m.WellFormed :=
  Fir.parse_wellFormed h

/-- Every valid module of every dialect whose text is lawful is well
formed. -/
theorem validIsWellFormed (d : Dialect) [DialectSignature d] [DialectValidation d] [DialectText d]
    [LawfulDialectText d] : ValidIsWellFormed (d := d) :=
  Fir.validIsWellFormed

/-! # Validation -/

/-- The validation check decides validity for every dialect whose rules
are decidable. -/
theorem problems_eq_nil_iff (d : Dialect) [DialectSignature d] [DialectValidation d]
    [DecidableEq d.Ty] [DecidableDialectValidation d] (m : Module d) :
    m.problems = [] ↔ m.Valid :=
  m.problems_eq_nil_iff

/-! # Execution -/

/-- The interpreter runs a function of any dialect, in any monad that has
the dialect's semantics. -/
example (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
    (m : Type → Type) [Monad m] [DialectDenote d m] (M : Module d) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) :
    ExceptT Stuck m (Result (List (DVal d))) :=
  f.run M args fuel

/-- More fuel never changes how a run ends, for every function of every
dialect. -/
theorem fuelMonotone (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
    [DialectCall d] [DialectDenote d SetM] (M : Module d) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) : FuelMonotone (f.runs M args) :=
  Func.fuelMonotone M f args

/-- No path of a run is stuck, for every function of every dialect whose
module's functions are valid and run within the module. -/
theorem neverStuck (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
    [DialectCall d] [DialectDenote d SetM] [DialectValidation d] {ctx : ModuleContext d}
    {M : Module d} (hv : ∀ g ∈ M.funcs, g.Valid ctx) (hm : ∀ g ∈ M.funcs, g.InModule M)
    {f : Func d} (hf : f ∈ M.funcs) (args : HVector toType (f.params.map (·.2))) :
    NeverStuck (f.runs M args) :=
  Func.neverStuck_of_inModule hv hm hf args

/-- A run has an outcome at every budget, for every function of every
dialect whose ops meet the poison obligations, when its module's functions
are valid and run within the module. -/
theorem progress (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty] [TyPoison d.Ty]
    [TyRefinement d.Ty] [DialectSignature d] [DialectValidation d] [DialectPoison d]
    [DialectCall d] [DialectDenote d SetM] [LawfulDialectPoison d] {ctx : ModuleContext d}
    {M : Module d} (hv : ∀ g ∈ M.funcs, g.Valid ctx) (hm : ∀ g ∈ M.funcs, g.InModule M)
    {f : Func d} (hf : f ∈ M.funcs) (args : HVector toType (f.params.map (·.2))) :
    Progress (f.runs M args) :=
  Func.progress_of_lawful hv hm hf args

/-! # Poison classes -/

/-- Every op of every dialect has a poison class, the dialect's own. -/
example (d : Dialect) [DialectPoison d] : d.Op → PoisonClass := poisonClass

/-- In every lawful dialect, a valid op whose class says it propagates
poison does. -/
theorem propagates (d : Dialect) [TyDenote d.Ty] [TyPoison d.Ty] [TyRefinement d.Ty]
    [DialectSignature d] [DialectPoison d] [DialectDenote d SetM] [DialectCall d]
    [DialectValidation d] [LawfulDialectPoison d] (op : d.Op) (hv : TypesValid op)
    (h : poisonClass op = .propagates) : PropagatesPoison op :=
  LawfulDialectPoison.propagates op hv h

/-!
The core dialect declares a class for each of its ops, case by case:
`Core.Op.poisonClass` has no case for the rest, so a new core op does not
build until it has one, and `scripts/check_g0.py` fails if a case for the
rest comes back. Nineteen ops propagate poison and six are
exceptions (ADR-2026-10-30-0818, ADR-2026-11-03-1615). The samples of the
core ops name all 25, and the checks below pin the split on them.
-/

#guard (Core.samples.map Core.Op.name).eraseDups.length == 25
#guard ((Core.samples.filter (Core.Op.poisonClass · == .propagates)).map Core.Op.name).eraseDups ==
  ["const", "add", "sub", "mul", "sdiv", "udiv", "srem", "urem", "and", "or", "xor", "shl", "lshr",
   "ashr", "zext", "sext", "trunc", "poison", "icmp"]
#guard ((Core.samples.filter (Core.Op.poisonClass · == .exception)).map Core.Op.name).eraseDups ==
  ["select", "freeze", "br", "cond_br", "ret", "call"]

end FirTest.G0
