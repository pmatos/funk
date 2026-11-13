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
    [DialectEffects d] [DialectCall d] [DialectValidation d]
    [DialectMemDenote d] [LawfulDialectEffects d] (op : d.Op) (hv : TypesValid op)
    (hc : isTerminator op = true ∨ callee? op = none) (h : (effects op).mayUB = false) :
    NeverUB op :=
  LawfulDialectEffects.neverUB op hv hc h

/-- In every dialect lawful in its effects, a valid op that runs by its own
rule and does not declare that it may produce poison makes none. -/
theorem makesNoPoison (d : Dialect) [TyDenote d.Ty] [TyPoison d.Ty] [DialectSignature d]
    [DialectEffects d] [DialectCall d] [DialectValidation d]
    [DialectMemDenote d] [LawfulDialectEffects d] (op : d.Op) (hv : TypesValid op)
    (hc : isTerminator op = true ∨ callee? op = none) (h : (effects op).mayPoison = false) :
    MakesNoPoison op :=
  LawfulDialectEffects.makesNoPoison op hv hc h

/-- In every dialect lawful in its effects, an op that does not declare
control is not a terminator. -/
theorem notControl (d : Dialect) [TyDenote d.Ty] [TyPoison d.Ty] [DialectSignature d]
    [DialectEffects d] [DialectCall d] [DialectValidation d]
    [DialectMemDenote d] [LawfulDialectEffects d] (op : d.Op) (h : (effects op).control = false) :
    isTerminator op = false :=
  LawfulDialectEffects.notControl op h

/-- In every dialect whose semantics with memory lifts its semantics in the
set monad, an op that never ends in UB with memory never does in the set
monad. -/
theorem neverUB_setM (d : Dialect) [TyDenote d.Ty] [DialectSignature d] [DialectEffects d]
    [DialectDenote d SetM] [DialectMemDenote d] [LiftsSetM d] {op : d.Op} (h : NeverUB op) :
    NeverUBSetM op :=
  h.setM

/-- In every dialect whose semantics with memory lifts its semantics in the
set monad, an op that makes no poison with memory makes none in the set
monad. -/
theorem makesNoPoison_setM (d : Dialect) [TyDenote d.Ty] [TyPoison d.Ty] [DialectSignature d]
    [DialectEffects d] [DialectDenote d SetM] [DialectMemDenote d] [LiftsSetM d] {op : d.Op}
    (h : MakesNoPoison op) : MakesNoPoisonSetM op :=
  h.setM

/-! # Memory obligations -/

/-- Every dialect with a semantics with memory gives its ops a semantics in
the state layer over the set monad, wherever a run names its memories. -/
example (d : Dialect) [TyDenote d.Ty] [DialectSignature d] [DialectEffects d]
    [DialectMemDenote d] {N : Type} [DecidableEq N] (lay : N → MemLayout)
    (ρ : DialectEffects.Mem d → N) : DialectDenote d (StateT (Memory.Memories N (unitsOf lay))
        SetM) :=
  DialectMemDenote.denoteAt lay ρ

/-- In every dialect lawful in its effects, a valid op that runs by its own
rule and does not declare a write to a memory of a run writes no unit of
it, wherever the run names the dialect's memories. -/
theorem writesNot (d : Dialect) [TyDenote d.Ty] [TyPoison d.Ty] [DialectSignature d]
    [DialectEffects d] [DialectCall d] [DialectValidation d]
    [DialectMemDenote d] [LawfulDialectEffects d] (op : d.Op) (hv : TypesValid op)
    (hc : isTerminator op = true ∨ callee? op = none) {N : Type} [DecidableEq N]
    (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N) (x : N)
    (h : ¬ ((effects op).writes.map ρ).Has x) : OwnRuleHas lay ρ (WritesNot x) op :=
  LawfulDialectEffects.writesNot op hv hc lay ρ x h

/-- In every dialect lawful in its effects, a valid op that runs by its own
rule and does not declare a read of a memory of a run does not depend on
its units, wherever the run names the dialect's memories. -/
theorem readsNot (d : Dialect) [TyDenote d.Ty] [TyPoison d.Ty] [DialectSignature d]
    [DialectEffects d] [DialectCall d] [DialectValidation d]
    [DialectMemDenote d] [LawfulDialectEffects d] (op : d.Op) (hv : TypesValid op)
    (hc : isTerminator op = true ∨ callee? op = none) {N : Type} [DecidableEq N]
    (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N) (x : N)
    (h : ¬ ((effects op).reads.map ρ).Has x) : OwnRuleHas lay ρ (ReadsNot x) op :=
  LawfulDialectEffects.readsNot op hv hc lay ρ x h

/-- In every dialect lawful in its effects, a valid op that runs by its own
rule and does not declare allocation in a memory of a run leaves its
allocations as they were, wherever the run names the dialect's memories. -/
theorem allocatesNot (d : Dialect) [TyDenote d.Ty] [TyPoison d.Ty] [DialectSignature d]
    [DialectEffects d] [DialectCall d] [DialectValidation d]
    [DialectMemDenote d] [LawfulDialectEffects d] (op : d.Op) (hv : TypesValid op)
    (hc : isTerminator op = true ∨ callee? op = none) {N : Type} [DecidableEq N]
    (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N) (x : N)
    (h : ¬ ((effects op).allocates.map ρ).Has x) : OwnRuleHas lay ρ (AllocatesNot x) op :=
  LawfulDialectEffects.allocatesNot op hv hc lay ρ x h

/-- In every dialect lawful in its totality, a valid op that runs by its
own rule has an outcome from any memories, wherever a run names the
dialect's memories. -/
theorem memTotal (d : Dialect) [TyDenote d.Ty] [DialectSignature d] [DialectEffects d]
    [DialectCall d] [DialectValidation d] [DialectMemDenote d] [LawfulDialectTotal d]
    (op : d.Op) (hv : TypesValid op) (hc : isTerminator op = true ∨ callee? op = none)
    {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N) :
    OwnRuleHas lay ρ HasOutcome op :=
  LawfulDialectTotal.total op hv hc lay ρ

/-- Every lawful dialect that lifts the set monad is lawful in its
totality. -/
theorem lawfulTotal_ofLawful (d : Dialect) [TyDenote d.Ty] [TyPoison d.Ty] [TyRefinement d.Ty]
    [DialectSignature d] [DialectEffects d] [DialectCall d] [DialectValidation d]
    [DialectDenote d SetM] [DialectMemDenote d] [LiftsSetM d] [LawfulDialectPoison d] :
    LawfulDialectTotal d :=
  LawfulDialectTotal.ofLawful

/-- Every sum of two dialects lawful in their totality is lawful in its
totality, when the extension accepts the base's valid types. Neither side
needs a semantics in the set monad, so a side whose ops touch memory may
take part. -/
theorem sum_lawfulTotal (base e : Dialect) [TyDenote base.Ty] [TyDenote e.Ty]
    [DialectSignature base] [DialectSignature (base.over e)] [DialectEffects base]
    [DialectEffects (base.over e)] [DialectMemOver base e] [DialectMemDenote base]
    [DialectMemDenote (base.over e)] [DialectCall base] [DialectCall (base.over e)]
    [DialectValidation base] [DialectValidation (base.over e)] [LawfulDialectTotal base]
    [LawfulDialectTotal (base.over e)]
    (hty : ∀ t : base.Ty, validTy t → validTy (d := base.over e) (.inl t)) :
    LawfulDialectTotal (base ⊞ e) :=
  Dialect.sum.lawfulTotal hty

/-- In every sum, the memories are the extension's, which name the base's:
a memory has one name in the sum, whichever side names it. -/
example (base e : Dialect) [DialectEffects base] [DialectEffects (base.over e)]
    [DialectMemOver base e] : DialectEffects.Mem (base ⊞ e) = DialectEffects.Mem (base.over e) :=
  rfl

/-- In every lift, an extension's name for a memory of what it depends on
becomes that memory's name in the larger base. -/
theorem liftMem_ofBase (e dep big : Dialect) [TyDenote dep.Ty] [TyDenote big.Ty]
    [DialectEffects dep] [DialectEffects big] [DialectEffects (dep.over e)]
    [DialectMemOver dep e] (μ : DialectEffects.Mem dep → DialectEffects.Mem big)
    (a : DialectEffects.Mem dep) :
    Dialect.lift.liftMem (e := e) μ (DialectMemOver.ofBase a) = .inl (μ a) :=
  Dialect.lift.liftMem_ofBase μ a

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
functions whose summary leaves out may-UB never ends in UB, in its runs with
memory, wherever a run names the dialect's memories. -/
theorem summary_neverUB (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty] [TyPoison d.Ty]
    [DialectSignature d] [DialectEffects d] [DialectCall d] [DialectValidation d]
    [DialectMemDenote d] [LawfulDialectEffects d] {N : Type} [DecidableEq N]
    (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N) {ctx : ModuleContext d} {M : Module d}
    (hv : ∀ g ∈ M.funcs, g.Valid ctx) {s : Name} {f : Func d} (hf : M.func? s = some f)
    (hs : (M.table.summary s).mayUB = false) (args : HVector toType (f.params.map (·.2)))
    (fuel : Nat) (r : String) : ¬ f.memRuns lay ρ M args fuel (.ub r) :=
  Module.summary_neverUB lay ρ hv hf hs args fuel r

/-- In every dialect lawful in its effects, a function of a module of valid
functions whose summary leaves out may produce poison returns no poison on
arguments with none, in its runs with memory, wherever a run names the
dialect's memories. -/
theorem summary_noPoison (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty] [TyPoison d.Ty]
    [DialectSignature d] [DialectEffects d] [DialectCall d] [DialectValidation d]
    [DialectMemDenote d] [LawfulDialectEffects d] {N : Type} [DecidableEq N]
    (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N) {ctx : ModuleContext d} {M : Module d}
    (hv : ∀ g ∈ M.funcs, g.Valid ctx) {s : Name} {f : Func d} (hf : M.func? s = some f)
    (hs : (M.table.summary s).mayPoison = false) (args : HVector toType (f.params.map (·.2)))
    (hargs : ¬ args.Any TyPoison.IsPoison) (fuel : Nat) (vs : List (DVal d)) :
    f.memRuns lay ρ M args fuel (.ok (.ok (.ret vs))) → DVals.Clean vs :=
  Module.summary_noPoison lay ρ hv hf hs args hargs fuel vs

/-!
The core dialect declares a class and a set of effects for each of its ops,
case by case: `Core.Op.poisonClass` and `Core.Op.effects` have no case for
the rest, so a new core op does not build until it has both, and
`scripts/check_g0.py` fails if a case for the rest comes back. Thirty-three
ops propagate poison and seven are exceptions (ADR-2026-10-29-2006). The
samples of the core ops name all 45 of their names, the float constant
sharing `const`'s and the two bit casts `bitcast`, and the checks below pin both on them. No core op declares an effect on memory or
is observable, since the core dialect has neither memory nor a trace yet
(ADR-2026-11-09-1541).
-/

#guard (Core.samples.map Core.Op.name).eraseDups.length == 45
#guard ((Core.samples.filter (Core.Op.poisonClass · == .propagates)).map Core.Op.name).eraseDups ==
  ["const", "add", "sub", "mul", "sdiv", "udiv", "srem", "urem", "and", "or", "xor", "shl", "lshr",
   "ashr", "zext", "sext", "trunc", "poison", "icmp", "fcmp", "fadd", "fsub", "fmul", "fdiv", "fneg",
   "fabs", "sqrt", "fma", "frem", "fmod", "bitcast", "sitofp", "uitofp",
   "fpext", "fptrunc", "ptradd", "fptosi", "fptoui"]
#guard ((Core.samples.filter (Core.Op.poisonClass · == .exception)).map Core.Op.name).eraseDups ==
  ["select", "freeze", "br", "cond_br", "ret", "unreachable", "call"]
#guard ((Core.samples.filter (Core.Op.effects · == {})).map Core.Op.name).eraseDups ==
  ["const", "add", "and", "or", "xor", "select", "zext", "sext", "trunc", "freeze", "call", "icmp",
   "fcmp", "fadd", "fdiv", "fneg", "fabs", "bitcast", "sitofp", "uitofp", "fpext", "fptrunc",
   "ptradd"]
#guard ((Core.samples.filter (·.effects.mayUB)).map Core.Op.name).eraseDups ==
  ["sdiv", "udiv", "srem", "urem", "cond_br", "unreachable"]
#guard ((Core.samples.filter (·.effects.mayPoison)).map Core.Op.name).eraseDups ==
  ["add", "sub", "mul", "sdiv", "shl", "lshr", "ashr", "poison", "fcmp", "fsub", "fmul", "sqrt",
   "fma", "frem", "fmod", "fptosi", "fptoui"]
#guard ((Core.samples.filter (·.effects.control)).map Core.Op.name).eraseDups ==
  ["br", "cond_br", "ret", "unreachable"]
-- The sets that depend on an attribute, at each value of it.
#guard [Core.Op.add 8 {}, .sub 8 {}, .mul 8 {}].all (·.effects == {})
#guard (Core.WrapFlags.all.filter (· != {})).all fun f =>
  [Core.Op.add 8 f, .sub 8 f, .mul 8 f].all (·.effects == { mayPoison := true })
#guard [Core.Op.sdiv 8 false, .udiv 8 false, .srem 8, .urem 8].all (·.effects == { mayUB := true })
#guard [Core.Op.sdiv 8 true, .udiv 8 true].all (·.effects == { mayUB := true, mayPoison := true })
-- A float op may produce poison with `nnan` or `ninf`; `nsz` and the
-- reserved words alone keep it pure.
#guard [({} : Core.FastMath), { nsz := true }, { contract := true, reassoc := true }].all fun fl =>
  [Core.Op.fcmp .olt fl 8 23, .fbin .fadd fl 8 23, .funary .fneg fl 8 23, .fma fl 8 23].all
    (·.effects == {})
#guard [({ nnan := true } : Core.FastMath), { ninf := true }, { nnan := true, nsz := true }].all
  fun fl => [Core.Op.fcmp .olt fl 8 23, .fbin .fadd fl 8 23, .funary .fneg fl 8 23,
    .fma fl 8 23].all (·.effects == { mayPoison := true })
#guard Core.samples.all fun o => o.effects.reads == .these [] && o.effects.writes == .these [] &&
  o.effects.allocates == .these [] && !o.effects.observable

end FirTest.G0
