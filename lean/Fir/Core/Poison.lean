import Fir.Core.Values
import Fir.Core.Text
import Fir.Execution.Propagation

/-!
# The poison classes of the core ops

Every one of the 25 core ops has a class (ADR-2026-10-30-0818).

Nineteen ops propagate poison: `const`, `poison`, `add`, `sub`, `mul`,
`sdiv`, `udiv`, `srem`, `urem`, `and`, `or`, `xor`, `shl`, `lshr`, `ashr`,
`icmp`, `zext`, `sext` and `trunc`. `const` and `poison` have no operands,
so they propagate poison whatever their semantics. `poison` meets the
obligation of a result on defined operands too: its one operand vector,
the empty one, holds no poison, and on it `poison` returns a result, the
poison of its type. The obligation asks for a result, not for a defined
one; it rules out an op that is always UB, and `poison` never is
(ADR-2026-11-03-1615). The four divisions are immediate UB on a poison
divisor, and propagate a poison dividend, but for one case: `sdiv` and
`srem` by `-1` are immediate UB on a poison dividend. Their obligation
allows both kinds of UB, because a defined value in place of the poison
would be UB too: a zero divisor, or a dividend that is the signed minimum.

Six ops are exceptions, each with its own rule:

* `select`: a poison condition gives poison; the operand not chosen does not
  matter, and the one chosen is given as it is.
* `freeze`: poison gives an arbitrary but fixed value.
* `cond_br`: a poison condition is immediate UB.
* `br`, `ret` and `call` pass values on as they are, poison included: to
  block arguments, to the caller, or to the callee and back.

The core dialect's execution rules landed with its op families, and the
obligations with them. Ticket #10 gave the semantics of the tracer subset,
`const`, `add` and `ret`, with the instance of
`DialectDenote CoreDialect SetM`, and proved the obligations of those three
ops: `PropagatesPoison` for `add`, a result on defined operands for
`const` and `add`, and totality and monotonicity for all three. Each family
ticket then proved the obligations of its ops: #14 for `add` with its
flags, `sub`, `mul` and `freeze`, #15 for the bitwise ops and shifts, #16
for `icmp` and `select`, #17 for the width changes, #18 for the
divisions, #19 for the branches and #122 for `poison`. `call` has no
op-level obligation, as below.
The last ticket, #20, gave `LawfulDialectPoison CoreDialect`
(`Core.lawfulDialectPoison`, in the section on the core dialect's poison
obligations). The exceptions' rules are tested by their tickets: `freeze`
by #14, `select` by #16, the branches and block arguments by #19, `call`
by #20.

`call` gets its meaning from the call effect, which the interpreter runs
with the fuel budget that the caller has left (ADR-2026-11-02-0836): #20
names the callee of `call @g`, `@g`. The set monad has no module and no
such effect, so `call` has no rule there, and no op-level obligation: the
obligations ask totality and monotonicity only of terminators and of ops
with no callee (ADR-2026-11-02-1514). Their counterparts for calls hold at
function level (the section on refinement through core calls): a call on
arguments that refine others refines the call on those others
(`Core.args_isRefinedBy`), and congruence in the callee: replacing a
callee's body refines every caller when the callee, run in the new
module, refines the old one (`Core.replaceBody_isRefinedBy`).

Below, for every semantics, a poison core value is refined by every value
of its type, and `const` and `poison` meet their poison clauses and are
monotone. Their totality and their results on defined operands follow from
their rules, with the obligations of `add` and `ret`, in the sections after
the interpreter.
-/

namespace Fir.Core

/-- The poison class of each core op. Each op is listed, with no case for
the rest, so a new core op does not build until it declares its class
(ADR-2026-11-03-0600). -/
def Op.poisonClass : Op → PoisonClass
  | .const .. | .add .. | .sub .. | .mul .. | .sdiv .. | .udiv .. | .srem _ | .urem _
  | .and _ | .or _ | .xor _ | .shl _ | .lshr _ | .ashr _ | .icmp .. | .zext .. | .sext ..
  | .trunc .. | .poison _ => .propagates
  | .select _ | .freeze _ | .br | .condBr | .ret _ | .call .. => .exception

/-- A core value is poison when it is the poison of its `iN`. -/
def Ty.IsPoison : {t : Ty} → ⟦t⟧ → Prop
  | .int _, v => v = .poison
  | .ptr, _ => False

end Fir.Core

namespace Fir

instance : DialectPoison CoreDialect := ⟨Core.Op.poisonClass⟩

instance : TyPoison Core.Ty := ⟨Core.Ty.IsPoison⟩

-- The exceptions among one instance of every core op.
#guard (Core.samples.filter (Core.Op.poisonClass · == .exception)).map Core.Op.name ==
  ["select", "freeze", "br", "cond_br", "ret", "ret", "call"]

/-- A poison core value is refined by every value of its type. -/
theorem Core.Ty.poison_isRefinedBy :
    ∀ {t : Core.Ty} (p v : ⟦t⟧), Core.Ty.IsPoison p → Core.Ty.IsRefinedBy p v
  | .int _, _, _, h => by subst h; trivial
  | .ptr, p, _, _ => nomatch (p : Empty)

/-- `const` has no operands, so it propagates poison, whatever its
semantics. -/
theorem Core.const_propagatesPoison [DialectDenote CoreDialect SetM] (w : Nat) (v : BitVec w) :
    PropagatesPoison (d := CoreDialect) (.const w v) where
  poisonOut args h := by cases args with | nil => exact h.elim
  ubByOwnRules args _ h := by cases args with | nil => exact h.elim

/-- `const` has no operands, so it is monotone, whatever its semantics. -/
theorem Core.const_monotone [DialectDenote CoreDialect SetM] (w : Nat) (v : BitVec w) :
    OpMonotone (d := CoreDialect) (.const w v) := by
  intro args args' _
  cases args; cases args'
  exact ⟨fun _ => SetM.isRefinedBy_refl (HVector.forall₂_refl Core.Ty.isRefinedBy_refl) _,
    fun _ => SetM.isRefinedBy_refl (fun _ => rfl) _⟩

/-- `poison` has no operands, so it propagates poison, whatever its
semantics. -/
theorem Core.poison_propagatesPoison [DialectDenote CoreDialect SetM] (w : Nat) :
    PropagatesPoison (d := CoreDialect) (.poison w) where
  poisonOut args h := by cases args with | nil => exact h.elim
  ubByOwnRules args _ h := by cases args with | nil => exact h.elim

/-- `poison` has no operands, so it is monotone, whatever its semantics. -/
theorem Core.poison_monotone [DialectDenote CoreDialect SetM] (w : Nat) :
    OpMonotone (d := CoreDialect) (.poison w) := by
  intro args args' _
  cases args; cases args'
  exact ⟨fun _ => SetM.isRefinedBy_refl (HVector.forall₂_refl Core.Ty.isRefinedBy_refl) _,
    fun _ => SetM.isRefinedBy_refl (fun _ => rfl) _⟩

end Fir
