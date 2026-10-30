import Fir.Core.Arith
import Fir.Core.Control
import Fir.Core.Text

/-!
# The core dialect's semantics

`DialectDenote CoreDialect SetM` gives every core op its meaning in the set
monad. It is one instance over all 24 core ops, which sends each op to the
rule of its family. The rules are written once, for any monad: `Op.denote?`
for the ops that are not terminators, and `Op.exit?` for the terminators.
So this instance and the monad that `fir-ref run` computes in share them.

# Ops without rules

An op whose family has not landed has no rule yet: `Op.denote?` or
`Op.exit?` gives `none` for it. After #10, that is every core op but
`const`, `add` without flags and `ret`; `add` with a flag is one of them.
ADR-2026-10-30-1855 decides what such an op does until its family lands:

* In the spec, it has no outcome: on every operand vector, its `denote` or
  its `exit` is the empty set. That is not a stand-in semantics. The
  totality obligation `OpTotal` rejects it, as it rejects
  `Core.Unlawful.noOutcome`, so `LawfulDialectPoison CoreDialect` cannot be
  proved while any op lacks its rules, and no theorem can take a missing
  rule for a final one.
* A run that reaches such an op has no way to end on that path. So
  `Progress` and `NeverStuck` hold for the tracer subset only, until #14 to
  #20 extend them as they add their ops.
* `fir-ref run` prints no outcome for a run that reaches such an op. It
  says that the op has no execution rules yet, as an error
  (ADR-2026-10-30-1856).

Each ticket from #14 to #20 adds its family's rules to `Op.denote?` and
`Op.exit?`, in its own section, and proves their obligations beside them.
-/

namespace Fir.Core

variable {m : Type → Type} [Monad m]

/-- The rule of each core op that is not a terminator, in any monad, when
its family has given it one. -/
def Op.denote? : (op : Op) → Option (HVector toType (Fir.sig (d := CoreDialect) op) →
    m (HVector toType (Fir.returnTypes (d := CoreDialect) op)))
  | .const w v => some fun _ => pure (.cons (constValue w v) .nil)
  | .add _ ⟨false, false⟩ => some fun
    | .cons a (.cons b .nil) => pure (.cons (addValues a b) .nil)
  | _ => none

/-- The rule of each core terminator, in any monad, when its family has
given it one. -/
def Op.exit? : (op : Op) → Option (HVector toType (Fir.sig (d := CoreDialect) op) → m Exit)
  | .ret _ => some fun _ => pure retExit
  | _ => none

/-- The op has rules: as an op that is not a terminator, or as a
terminator. -/
def Op.hasRules (op : Op) : Bool := (op.denote? (m := Id)).isSome || (op.exit? (m := Id)).isSome

-- Among one instance of every core op, the tracer subset has rules.
#guard (samples.filter Op.hasRules).map Op.name ==
  ["const", "const", "const", "const", "add", "ret", "ret"]
#guard !(Op.add 32 { nuw := true }).hasRules && !(Op.add 32 { nsw := true }).hasRules

end Fir.Core

namespace Fir

/-- The core dialect's semantics in the set monad: each op's rule, and no
outcome for an op that has no rule yet. -/
instance : DialectDenote CoreDialect SetM where
  denote op args := match op.denote? (m := SetM) with
    | some rule => rule args
    | none => fun _ => False
  exit op args := match op.exit? (m := SetM) with
    | some rule => rule args
    | none => fun _ => False

end Fir
