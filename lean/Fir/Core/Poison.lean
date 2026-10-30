import Fir.Core.Values
import Fir.Core.Text
import Fir.Execution.Propagation

/-!
# The poison classes of the core ops

Every one of the 24 core ops has a class (ADR-2026-10-30-0818).

Eighteen ops propagate poison: `const`, `add`, `sub`, `mul`, `sdiv`, `udiv`,
`srem`, `urem`, `and`, `or`, `xor`, `shl`, `lshr`, `ashr`, `icmp`, `zext`,
`sext` and `trunc`. `const` has no operands, so it propagates poison
whatever its semantics. The four divisions are immediate UB on a poison
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

The core dialect's execution rules land with its op families, so the
obligations land with them too. Ticket #10 gives the semantics of the
tracer subset, `const`, `add` and `ret`, with the instance of
`DialectDenote CoreDialect SetM`, and proves the obligations of those three
ops: `PropagatesPoison` for `add`, and totality and monotonicity for all
three. Each family ticket then proves the obligations of its ops: #14 for
`add` with its flags, `sub`, `mul` and `freeze`, #15 for the bitwise ops
and shifts, #16 for `icmp` and `select`, #17 for the width changes, #18 for
the divisions, #19 for the branches and #20 for `call`. The last of them
gives `LawfulDialectPoison CoreDialect`. The exceptions' rules are tested
by their tickets: `freeze` by #14, `select` by #16, the branches and block
arguments by #19, `call` by #20.

Below, for every semantics, a poison core value is refined by every value
of its type, and `const` meets its poison clauses and is monotone. Its
totality waits for its semantics, in #10.
-/

namespace Fir.Core

/-- The poison class of each core op. -/
def Op.poisonClass : Op → PoisonClass
  | .select _ | .freeze _ | .br | .condBr | .ret _ | .call .. => .exception
  | _ => .propagates

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
  exact ⟨SetM.isRefinedBy_refl (HVector.forall₂_refl Core.Ty.isRefinedBy_refl) _,
    SetM.isRefinedBy_refl (fun _ => rfl) _⟩

end Fir
