import Fir.Execution.Frame

/-!
# The external-call rule

A call may name an external declaration: a function that funk did not
compile, which the module names by a symbol and a signature, with no body
(ADR-2026-11-09-1547). The run cannot run such a callee. It hands the call
to the _external-call rule_ instead, a part of the semantics of its own,
beside the rules of ops, given the declaration's symbol, the call's
arguments and its result types. The human ruled this on 2026-11-21, on
#239 (Q1): one `call` op, and a call to a declaration goes to this rule.
An indirect call (#235) whose pointer names a declaration reuses it, with
the symbol it picks when it runs.

The rule gives the call's results, each with its type. The run takes one
step for it, as for an op that runs by its own rule, and checks that the
results have the call's result types, as it checks the values a callee
returns.

What the rule does depends on the layer:

* In the layers with no world, the set monad and the layer with memory,
  an external call is UB, as a stand-in. No outside code exists there to
  answer it. Every guarantee of those layers keeps its statement and
  stays true, but says nothing of code that calls outside the module: the
  guarantees over traced runs are the ones that cover external calls. The
  human ruled this on 2026-11-21, on #239 (Q2). Rejected: any results and
  any memories, which give a call infinitely many outcomes, against the
  finiteness that congruence in the callee needs; and guarantees with
  memory that cover only modules that call no declaration.
* In the traced layer the dialect gives the rule: it is the dialect's
  semantics there (`DialectTrace`), where the world answers an external
  call.

Since a stand-in that is UB is refined by every computation, a statement
that reads it as a source says nothing of external calls; the warning on
`call` in the core's section on calls applies to it too.
-/

namespace Fir

variable {d : Dialect} [TyDenote d.Ty]

/-- The external-call rule of the dialect `d` in the monad `m`:
`extCall g args rs` calls the external declaration `g` on the arguments
`args`, each with its type, for results of the types `rs`, and gives the
results, each with its type. -/
class DialectExtCall (d : Dialect) [TyDenote d.Ty] (m : Type → Type) where
  extCall : Name → List (DVal d) → List d.Ty → m (List (DVal d))

/-- A dialect's semantics in the monad `m` with its external-call rule
there: what a layer whose rule is the dialect's gives, as the traced
layer does. -/
class DialectRun (d : Dialect) [TyDenote d.Ty] [DialectSignature d] (m : Type → Type) extends
    DialectDenote d m, DialectExtCall d m

/-- The reason of the UB that an external call is in the layers with no
world. -/
def extCallUB : String := "an external call has no meaning without a world"

/-- In the set monad, which has no world, an external call is UB. -/
instance : DialectExtCall d SetM := ⟨fun _ _ _ => MonadUB.ub extCallUB⟩

/-- In the set monad, an external call is UB. -/
theorem extCall_setM (g : Name) (args : List (DVal d)) (rs : List d.Ty) :
    DialectExtCall.extCall (m := SetM) g args rs = MonadUB.ub extCallUB := rfl

variable [DecidableEq d.Ty]

/-- An external declaration accepts a call on operands of the types `ts`
for results of the types `rs`: its parameter types start `ts`, and are
all of them unless it ends in `...`, and its result types are `rs`. -/
def Extern.accepts (e : Extern d) (ts rs : List d.Ty) : Bool :=
  (if e.variadic then (e.params.map (·.2)).isPrefixOf ts else e.params.map (·.2) == ts) &&
    e.results == rs

/-- The module `M` declares the symbol `g` as an external declaration that
accepts a call on operands of the types `ts` for results of the types
`rs`. -/
def Module.declares (M : Module d) (g : Name) (ts rs : List d.Ty) : Bool :=
  M.items.any fun i => match i.extern? with
    | some e => e.name == g && e.accepts ts rs
    | none => false

end Fir
