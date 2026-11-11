import Fir

/-!
G0's check on the Lean side, for poison classes, effects and function
summaries (ADR-2026-11-03-0600), split from `lean/FirTest/G0.lean` by
responsibility. Each statement below is made of an arbitrary dialect `d`,
with the spec's own proof or definition, so it builds only while those stay
parameterized over the dialect. `scripts/check_g0.py` checks this file as it
checks `G0.lean`, outside its `#guard` commands. The last section checks
that every core op declares its poison class and its effects.
-/

namespace FirTest.G0

open Fir

/-! # Poison classes and effects -/

/-- Every op of every dialect has a poison class, the dialect's own. -/
example (d : Dialect) [DialectEffects d] : d.Op → PoisonClass := poisonClass

/-- Every op of every dialect has a set of effects, on the dialect's own
memories. -/
example (d : Dialect) [h : DialectEffects d] : d.Op → Effects h.Mem := effects

/-- In every lawful dialect, a valid op whose class says it propagates
poison does. -/
theorem propagates (d : Dialect) [TyDenote d.Ty] [TyPoison d.Ty] [TyRefinement d.Ty]
    [DialectSignature d] [DialectEffects d] [DialectDenote d SetM] [DialectCall d]
    [DialectValidation d] [LawfulDialectPoison d] (op : d.Op) (hv : TypesValid op)
    (h : poisonClass op = .propagates) : PropagatesPoison op :=
  LawfulDialectPoison.propagates op hv h

/-- In every dialect lawful in its effects, a valid op that runs by its own
rule and does not declare may-UB never ends in UB. -/
theorem neverUB (d : Dialect) [TyDenote d.Ty] [TyPoison d.Ty] [DialectSignature d]
    [DialectEffects d] [DialectDenote d SetM] [DialectCall d] [DialectValidation d]
    [LawfulDialectEffects d] (op : d.Op) (hv : TypesValid op)
    (hc : isTerminator op = true ∨ callee? op = none) (h : (effects op).mayUB = false) :
    NeverUB op :=
  LawfulDialectEffects.neverUB op hv hc h

/-- In every dialect lawful in its effects, a valid op that runs by its own
rule and does not declare that it may produce poison makes none. -/
theorem makesNoPoison (d : Dialect) [TyDenote d.Ty] [TyPoison d.Ty] [DialectSignature d]
    [DialectEffects d] [DialectDenote d SetM] [DialectCall d] [DialectValidation d]
    [LawfulDialectEffects d] (op : d.Op) (hv : TypesValid op)
    (hc : isTerminator op = true ∨ callee? op = none) (h : (effects op).mayPoison = false) :
    MakesNoPoison op :=
  LawfulDialectEffects.makesNoPoison op hv hc h

/-- In every dialect lawful in its effects, an op that does not declare
control is not a terminator. -/
theorem notControl (d : Dialect) [TyDenote d.Ty] [TyPoison d.Ty] [DialectSignature d]
    [DialectEffects d] [DialectDenote d SetM] [DialectCall d] [DialectValidation d]
    [LawfulDialectEffects d] (op : d.Op) (h : (effects op).control = false) :
    isTerminator op = false :=
  LawfulDialectEffects.notControl op h

/-- Every function of a symbol table of every dialect has a summary, on the
dialect's own memories. -/
example (d : Dialect) [DialectSignature d] [DialectCall d] [h : DialectEffects d] :
    SymbolTable d → Name → Effects h.Mem := SymbolTable.summary

/-- In every dialect, the summary is the least assignment closed under the
calls of a table. -/
theorem summary_least (d : Dialect) [DialectSignature d] [DialectCall d] [h : DialectEffects d]
    (t : SymbolTable d) : t.Closed t.summary ∧
      ∀ T : Name → Effects h.Mem, t.Closed T → ∀ s, t.summary s ≤ T s :=
  ⟨SymbolTable.summary_closed, fun _ hT s => SymbolTable.summary_le hT s⟩

/-- In every dialect lawful in its effects, a function of a module of valid
functions whose summary leaves out may-UB never ends in UB. -/
theorem summary_neverUB (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty] [TyPoison d.Ty]
    [DialectSignature d] [DialectEffects d] [DialectDenote d SetM] [DialectCall d]
    [DialectValidation d] [LawfulDialectEffects d] {ctx : ModuleContext d} {M : Module d}
    (hv : ∀ g ∈ M.funcs, g.Valid ctx) {s : Name} {f : Func d} (hf : M.func? s = some f)
    (hs : (M.table.summary s).mayUB = false) (args : HVector toType (f.params.map (·.2)))
    (fuel : Nat) (r : String) : ¬ (f.run (m := SetM) M args fuel).run (.ub r) :=
  Module.summary_neverUB hv hf hs args fuel r

/-- In every dialect lawful in its effects, a function of a module of valid
functions whose summary leaves out may produce poison returns no poison on
arguments with none. -/
theorem summary_noPoison (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty] [TyPoison d.Ty]
    [DialectSignature d] [DialectEffects d] [DialectDenote d SetM] [DialectCall d]
    [DialectValidation d] [LawfulDialectEffects d] {ctx : ModuleContext d} {M : Module d}
    (hv : ∀ g ∈ M.funcs, g.Valid ctx) {s : Name} {f : Func d} (hf : M.func? s = some f)
    (hs : (M.table.summary s).mayPoison = false) (args : HVector toType (f.params.map (·.2)))
    (hargs : ¬ args.Any TyPoison.IsPoison) (fuel : Nat) (vs : List (DVal d)) :
    (f.run (m := SetM) M args fuel).run (.ok (.ok (.ret vs))) → DVals.Clean vs :=
  Module.summary_noPoison hv hf hs args hargs fuel vs

/-!
The core dialect declares a class and a set of effects for each of its ops,
case by case: `Core.Op.poisonClass` and `Core.Op.effects` have no case for
the rest, so a new core op does not build until it has both, and
`scripts/check_g0.py` fails if a case for the rest comes back. Nineteen ops
propagate poison and seven are exceptions (ADR-2026-10-30-0818,
ADR-2026-11-03-1615). The samples of the core ops name all 26, and the
checks below pin both on them. No core op touches memory or is observable,
since the core dialect has neither memory nor a trace yet
(ADR-2026-11-09-1541).
-/

#guard (Core.samples.map Core.Op.name).eraseDups.length == 26
#guard ((Core.samples.filter (Core.Op.poisonClass · == .propagates)).map Core.Op.name).eraseDups ==
  ["const", "add", "sub", "mul", "sdiv", "udiv", "srem", "urem", "and", "or", "xor", "shl", "lshr",
   "ashr", "zext", "sext", "trunc", "poison", "icmp"]
#guard ((Core.samples.filter (Core.Op.poisonClass · == .exception)).map Core.Op.name).eraseDups ==
  ["select", "freeze", "br", "cond_br", "ret", "unreachable", "call"]
#guard ((Core.samples.filter (Core.Op.effects · == {})).map Core.Op.name).eraseDups ==
  ["const", "add", "and", "or", "xor", "select", "zext", "sext", "trunc", "freeze", "call", "icmp"]
#guard ((Core.samples.filter (·.effects.mayUB)).map Core.Op.name).eraseDups ==
  ["sdiv", "udiv", "srem", "urem", "cond_br", "unreachable"]
#guard ((Core.samples.filter (·.effects.mayPoison)).map Core.Op.name).eraseDups ==
  ["add", "sub", "mul", "sdiv", "shl", "lshr", "ashr", "poison"]
#guard ((Core.samples.filter (·.effects.control)).map Core.Op.name).eraseDups ==
  ["br", "cond_br", "ret", "unreachable"]
-- The sets that depend on an attribute, at each value of it.
#guard [Core.Op.add 8 {}, .sub 8 {}, .mul 8 {}].all (·.effects == {})
#guard (Core.WrapFlags.all.filter (· != {})).all fun f =>
  [Core.Op.add 8 f, .sub 8 f, .mul 8 f].all (·.effects == { mayPoison := true })
#guard [Core.Op.sdiv 8 false, .udiv 8 false, .srem 8, .urem 8].all (·.effects == { mayUB := true })
#guard [Core.Op.sdiv 8 true, .udiv 8 true].all (·.effects == { mayUB := true, mayPoison := true })
#guard Core.samples.all fun o => o.effects.reads == .these [] && o.effects.writes == .these [] &&
  o.effects.allocates == .these [] && !o.effects.observable

end FirTest.G0
