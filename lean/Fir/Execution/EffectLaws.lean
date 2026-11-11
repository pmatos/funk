import Fir.Execution.Propagation
import Fir.Execution.MemoryObligations

/-!
# Effect obligations

A pass may rely on an op's declared effects, so each declaration must be
sound: an effect that an op leaves out, it does not have
(ADR-2026-11-09-1541). The declaration may over-approximate: an op may
declare an effect that it never has. Each effect left out carries an
obligation, stated over the op's semantics in the set monad:

* _No may-UB_: the op never ends in UB, and the exit of a terminator never
  does.
* _No may produce poison_: on operands with no poison, no result the op
  returns is poison.
* _No control_: the op is not a terminator.

As the poison obligations do, the first two look only at what runs by the
op's own rule: the meaning of an op that is not a terminator, and the exit
of a terminator. So they cover the terminators and the ops with no callee.
An op with a callee runs its callee, never a rule of its own, and has its
callee's effects (ADR-2026-11-02-1514). They speak only of valid op
instances, as the poison obligations do.

The memory-named effects have the obligations of the section on memory
obligations, over the op's semantics in the state layer, wherever a run
names the dialect's memories (ADR-2026-11-09-1542):

* _No write to m_: the op leaves the units of `m`'s allocations as they
  were.
* _No read of m_: the op does not depend on the units of `m`.
* _No allocation in m_: the op leaves `m`'s allocations as they were.

They too look only at what runs by the op's own rule, and speak only of
valid op instances. _Observable_ has no obligation yet: M0's runs have no
trace, so an op cannot add an event, and there is nothing yet for the
obligation to state. It comes with the trace: an op that is not observable
adds no event (ADR-2026-11-09-1540).

A dialect meets every obligation of this section by showing that it is
lawful in its effects, the last definition below.
-/

namespace Fir

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d SetM]

/-- Never UB: on every operand vector, an op that is not a terminator never
ends in UB, and neither does the exit of a terminator. -/
def NeverUB (op : d.Op) : Prop :=
  ∀ (args : HVector toType (sig op)) (r : String),
    (isTerminator op = false → ¬ DialectDenote.denote (m := SetM) op args (.ub r)) ∧
    (isTerminator op = true → ¬ DialectDenote.exit (m := SetM) op args (.ub r))

/-- Makes no poison: on operands with no poison, no result vector that an op
that is not a terminator returns holds a poison. -/
def MakesNoPoison [TyPoison d.Ty] (op : d.Op) : Prop :=
  isTerminator op = false → ∀ args : HVector toType (sig op), ¬ args.Any TyPoison.IsPoison →
    ∀ rs, DialectDenote.denote (m := SetM) op args (.ok rs) → ¬ rs.Any TyPoison.IsPoison

/-- A dialect whose effect declarations are sound: every valid instance that
runs by its own rule, a terminator or an op with no callee, never ends in
UB unless it declares may-UB, makes no poison unless it declares that it
may produce poison, and, wherever a run names the dialect's memories,
writes, reads and allocates in no memory that it does not declare; and
every op that does not declare control is not a terminator. -/
class LawfulDialectEffects (d : Dialect) [TyDenote d.Ty] [TyPoison d.Ty] [DialectSignature d]
    [DialectEffects d] [DialectDenote d SetM] [DialectCall d] [DialectValidation d]
    [DialectMemDenote d] : Prop where
  neverUB : ∀ op : d.Op, TypesValid op → isTerminator op = true ∨ callee? op = none →
    (effects op).mayUB = false → NeverUB op
  makesNoPoison : ∀ op : d.Op, TypesValid op → isTerminator op = true ∨ callee? op = none →
    (effects op).mayPoison = false → MakesNoPoison op
  notControl : ∀ op : d.Op, (effects op).control = false → isTerminator op = false
  writesNot : ∀ op : d.Op, TypesValid op → isTerminator op = true ∨ callee? op = none →
    ∀ {N : Type} [DecidableEq N] (unit : N → Nat) (ρ : DialectEffects.Mem d → N) (x : N),
      ¬ ((effects op).writes.map ρ).Has x → OwnRuleHas unit ρ (WritesNot x) op
  readsNot : ∀ op : d.Op, TypesValid op → isTerminator op = true ∨ callee? op = none →
    ∀ {N : Type} [DecidableEq N] (unit : N → Nat) (ρ : DialectEffects.Mem d → N) (x : N),
      ¬ ((effects op).reads.map ρ).Has x → OwnRuleHas unit ρ (ReadsNot x) op
  allocatesNot : ∀ op : d.Op, TypesValid op → isTerminator op = true ∨ callee? op = none →
    ∀ {N : Type} [DecidableEq N] (unit : N → Nat) (ρ : DialectEffects.Mem d → N) (x : N),
      ¬ ((effects op).allocates.map ρ).Has x → OwnRuleHas unit ρ (AllocatesNot x) op

end Fir
