import Fir.Core.Lawful
import FirTest.OverCore

/-!
Tests of refinement for a dialect whose ops are monotone only at valid op
instances (#99, ADR-2026-11-05-1715).

The probe dialect has one op over the core dialect's integers, `id w` at
`iN` with `N = w`, and no text format. It gives its operand back at
every width that validation accepts. At `i0`, which validation rejects,
it gives a value for poison and poison for a value, so it is not
monotone there (`probe0_not_monotone`). Its poison class is an
exception, so the poison obligations ask only that it be total and
monotone at valid instances, and it meets them: the probe dialect is
lawful, and so is its sum with the core dialect, `CoreProbe`
(`coreProbe_lawful`).

The refinement engine once asked monotonicity at every op instance,
valid or not, which `CoreProbe` does not meet (`coreProbe_not_monotone`).
It now asks it only of the ops that a run can reach. So `CoreProbe` gets
both function-level refinement theorems, for every function of every
valid module, by the lawful class alone: on refined arguments
(`coreProbe_args`) and on replacing a callee's body
(`coreProbe_replaceBody`).
-/

namespace FirTest.Probe

/-- An op instance of the probe dialect: `id w` at `iN` with `N = w`. -/
inductive Op where
  | id (w : Nat)
  deriving Repr, DecidableEq

end FirTest.Probe

namespace FirTest

open Fir

/-- The probe dialect: its op, over the core dialect's types. -/
abbrev ProbeDialect : Dialect := OverCore Probe.Op

namespace Probe

/-- The operand types of a probe op. -/
def Op.sig : Op → List (Core.Ty ⊕ Empty)
  | .id w => [.inl (.int w)]

/-- The result types of a probe op. -/
def Op.returnTypes : Op → List (Core.Ty ⊕ Empty)
  | .id w => [.inl (.int w)]

instance : DialectSignature ProbeDialect where
  sig := Op.sig
  returnTypes := Op.returnTypes
  isTerminator _ := false
  succCount _ := 0

/-- The probe dialect accepts the types that the core dialect accepts, and
has no rule of its own. -/
instance : DialectValidation ProbeDialect where
  validTy := OverCore.ValidTy
  symbolRefs _ := []
  validOp _ _ := True
  validFunc _ _ _ := True

/-- A probe op states its own rule for poison, and declares every effect:
at `i0`, which validation rejects, it gives poison for a value. The probe
dialect has no memory of its own: its memories are the core's. -/
instance : DialectEffects ProbeDialect :=
  ⟨DialectEffects.Mem CoreDialect ⊕ Empty, fun _ => .exception, fun _ => .all⟩

/-- The probe dialect's memories are the core's, and none of its own. -/
instance : DialectMemOver CoreDialect (Ext Op) := ⟨Empty, id, id, fun _ => rfl, fun _ => rfl⟩

/-- The rule of `id`: the operand, at a width above zero; at `i0`, a
value for poison and poison for a value. -/
def idValue : (w : Nat) → PoisonOr (BitVec w) → PoisonOr (BitVec w)
  | 0, .value _ => .poison
  | 0, .poison => .value 0
  | _ + 1, a => a

/-- The rule of each probe op, in the set monad. -/
def Op.denote : (op : Op) → HVector toType (Fir.sig (d := ProbeDialect) op) →
    SetM (HVector toType (Fir.returnTypes (d := ProbeDialect) op))
  | .id w, .cons a .nil => pure (.cons (idValue w a) .nil)

/-- No probe op is a terminator, so no probe op has an exit. -/
instance : DialectDenote ProbeDialect SetM where
  denote := Op.denote
  exit _ _ := fun _ => False

/-- No probe op calls a function. -/
instance : DialectCall ProbeDialect := ⟨fun _ => none⟩

/-- No probe op touches memory: at every naming of its memories, it runs by
its rule in the set monad and keeps the memories. -/
instance : DialectMemDenote ProbeDialect := DialectMemDenote.ofSetM

/-- The probe dialect's semantics with memory lifts its semantics in the set
monad. -/
instance : LiftsSetM ProbeDialect := DialectMemDenote.ofSetM_liftsSetM

/-- A valid probe op instance has a width above zero. -/
theorem pos_of_typesValid {w : Nat} (h : TypesValid (d := ProbeDialect) (.id w)) : 0 < w :=
  (h.1 (.inl (.int w)) List.mem_cons_self).1

/-- `id` is total at every width. -/
theorem id_total (w : Nat) : OpTotal (d := ProbeDialect) (.id w) := fun
  | .cons _ .nil => ⟨fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩

/-- `id` is monotone at every width above zero. -/
theorem id_monotone (w : Nat) : OpMonotone (d := ProbeDialect) (.id (w + 1)) := by
  intro args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons a .nil, .cons a' .nil, ⟨ha, _⟩ =>
    intro e he
    subst he
    exact ⟨_, rfl, ha, trivial⟩

/-- The probe dialect is lawful: its valid op instances are total and
monotone, and it has no op that propagates poison. -/
instance lawful : LawfulDialectPoison ProbeDialect where
  poison_isRefinedBy {t} := match t with
    | .inl _ => fun _ => Core.Ty.poison_isRefinedBy
    | .inr t => t.elim
  propagates _ _ h := nomatch h
  returnsOnDefined _ _ h := nomatch h
  total | .id w, _, _ => id_total w
  monotone
    | .id w, hv, _ => by
      have hw := pos_of_typesValid hv
      obtain ⟨n, rfl⟩ : ∃ n, w = n + 1 := ⟨w - 1, by omega⟩
      exact id_monotone n

/-- The probe dialect is lawful in its effects: it declares every effect,
so the obligations ask nothing of may-UB, poison or control, and it touches
no memory. -/
instance lawfulEffects : LawfulDialectEffects ProbeDialect where
  neverUB _ _ _ h := nomatch h
  makesNoPoison _ _ _ h := nomatch h
  notControl _ h := nomatch h
  writesNot := DialectMemDenote.ofSetM_writesNot
  readsNot := DialectMemDenote.ofSetM_readsNot
  allocatesNot := DialectMemDenote.ofSetM_allocatesNot

/-- The probe dialect is lawful in its totality: it is lawful, and it lifts
the set monad, so `id` has an outcome from any memories. -/
instance lawfulTotal : LawfulDialectTotal ProbeDialect := LawfulDialectTotal.ofLawful

end Probe

/-- The sum of the core dialect and the probe dialect. -/
abbrev CoreProbe : Dialect := CoreSum Probe.Op

/-- The sum is lawful: the probe dialect accepts the core's valid types. -/
instance coreProbe_lawful : LawfulDialectPoison CoreProbe := Dialect.sum.lawfulPoison fun _ h => h

/-- The sum is lawful in its effects, since both sides are. -/
instance coreProbe_lawfulEffects : LawfulDialectEffects CoreProbe :=
  Dialect.sum.lawfulEffects fun _ h => h

/-- The sum is lawful in its totality, since both sides are. -/
instance coreProbe_lawfulTotal : LawfulDialectTotal CoreProbe :=
  Dialect.sum.lawfulTotal fun _ h => h

/-- `id` at `i0` is not a valid op instance. -/
theorem probe0_not_typesValid : ¬ TypesValid (d := CoreProbe) (.inr (.id 0)) :=
  fun h => absurd (h.1 (.inl (.int 0)) List.mem_cons_self).1 (by decide)

/-- `id` at `i0` is not monotone: on poison it gives a value, and on
a value, which refines poison, it gives poison, which does not refine
that value. -/
theorem probe0_not_monotone : ¬ OpMonotone (d := CoreProbe) (.inr (.id 0)) := by
  intro h
  obtain ⟨e, he, hr⟩ :=
    (h (.cons .poison .nil) (.cons (.value 0) .nil) ⟨trivial, trivial⟩).1 rfl _ rfl
  subst he
  exact hr.1

/-- So `CoreProbe` does not meet the hypothesis that the engine asked
before: monotonicity of every terminator and every op with no callee, at
every op instance. -/
theorem coreProbe_not_monotone :
    ¬ ∀ op : CoreProbe.Op, isTerminator op = true ∨ callee? op = none → OpMonotone op :=
  fun h => probe0_not_monotone (h (.inr (.id 0)) (.inr rfl))

/-- Refined arguments, for every function of a module of `CoreProbe` whose
functions are all valid, by the lawful class alone. -/
theorem coreProbe_args {ctx : ModuleContext CoreProbe} {M : Module CoreProbe}
    (hv : ∀ g ∈ M.funcs, g.Valid ctx) {f : Func CoreProbe} (hf : f ∈ M.funcs)
    {a a' : HVector toType (f.params.map (·.2))} (ha : a.Forall₂ TyRefinement.IsRefinedBy a') :
    observable (f.runs M a) ⊑ observable (f.runs M a') :=
  Func.runs_args_isRefinedBy_of_lawful hv hf ha

/-- Every vector of values of the sum's types, which are the core's. -/
def argVectors : (ts : List CoreProbe.Ty) → List (HVector toType ts)
  | [] => [.nil]
  | .inl t :: ts => t.values.flatMap fun v => (argVectors ts).map (.cons v)
  | .inr t :: _ => t.elim

/-- `argVectors ts` holds every vector of values of the types `ts`. -/
theorem mem_argVectors : ∀ {ts : List CoreProbe.Ty} (a : HVector toType ts), a ∈ argVectors ts
  | [], .nil => List.mem_singleton_self _
  | .inl _ :: _, .cons v a => List.mem_flatMap.2 ⟨v, Core.Ty.mem_values v,
      List.mem_map_of_mem (mem_argVectors a)⟩
  | .inr t :: _, _ => t.elim

/-- Congruence in the callee, for every valid module of `CoreProbe`, by the
lawful class alone, whatever the new body. -/
theorem coreProbe_replaceBody {M : Module CoreProbe} (hM : M.Valid) {g : Func CoreProbe}
    (hg : g ∈ M.funcs) (b : Region CoreProbe)
    (h : g.runs M ⊑ (g.replaceBody g.name b).runs (M.replaceBody g.name b))
    {f : Func CoreProbe} (hf : f ∈ M.funcs) :
    f.runs M ⊑ (f.replaceBody g.name b).runs (M.replaceBody g.name b) :=
  Func.runs_replaceBody_isRefinedBy_of_lawful
    (Dialect.sum.isRefinedBy_refl (e := Ext Probe.Op) Core.Ty.isRefinedBy_refl
      fun {t} => Empty.elim t)
    (Dialect.sum.isRefinedBy_trans (e := Ext Probe.Op) Core.Ty.isRefinedBy_trans
      fun {t} => Empty.elim t)
    hM hg b ⟨argVectors _, mem_argVectors⟩ h hf

/-! # Axioms -/

/-- info: 'Fir.Func.OpsMonotone.enter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.OpsMonotone.enter

/-- info: 'Fir.Func.OpsMonotone.jump' depends on axioms: [propext] -/
#guard_msgs in #print axioms Fir.Func.OpsMonotone.jump

/-- info: 'Fir.CallsRefined.callee_allowed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.CallsRefined.callee_allowed

/-- info: 'Fir.CallsRefined.callee_allowedBelow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.CallsRefined.callee_allowedBelow

/-- info: 'Fir.Func.Valid.opsMonotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.Valid.opsMonotone

/-- info: 'Fir.Func.runs_args_isRefinedBy_of_lawful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.runs_args_isRefinedBy_of_lawful

/-- info: 'Fir.Func.runs_replaceBody_isRefinedBy_of_lawful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.runs_replaceBody_isRefinedBy_of_lawful

/-- info: 'Fir.Core.opsMonotone_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.opsMonotone_all

/-- info: 'FirTest.probe0_not_monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms FirTest.probe0_not_monotone

/-- info: 'FirTest.coreProbe_not_monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms FirTest.coreProbe_not_monotone

/-- info: 'FirTest.coreProbe_args' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.coreProbe_args

/-- info: 'FirTest.coreProbe_replaceBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirTest.coreProbe_replaceBody

end FirTest
