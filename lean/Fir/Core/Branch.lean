import Fir.Core.Values

/-!
# Branches and block arguments

Ticket #19 gives `br` and `cond_br` their rules. Both are terminators: they
end a block and say where control goes next, to one of their successors.
A successor names a block and the values it passes to that block's
arguments, as in `br ^loop(%i1, %acc1)`. The rule of a terminator says
only which successor control goes to, as a `goto i` with the index `i` of
that successor; the interpreter then binds the arguments of the block that
the successor names to the values it passes, and runs that block (H1,
ADR-2026-10-29-2010).

`br` has one successor, and goes to it on every run. It has no operands:
the values it passes are its successor's, not its own.

`cond_br %c, ^a, ^b` takes an `i1` condition and has two successors. It
goes to the first, `^a`, when `%c` is `true`, and to the second, `^b`,
when `%c` is `false`. A poison condition is immediate UB (S1,
ADR-2026-10-29-2006). It is never a free choice between the two
successors: a compiler learns facts from a branch, and the section on
poison and immediate UB explains why those facts would be wrong if a
branch on poison could go either way (ADR-2026-10-30-0818).

Both are exceptions to poison propagation that pass values on as they are
(ADR-2026-10-30-0818). A successor's values reach the block's arguments
unchanged, so a poison value arrives as poison. Only `cond_br`'s own
condition may not be poison.

A block runs ops in order until its terminator, and a terminator may send
control back to a block that has run before, so a function with branches
may loop. Each op takes one step of fuel, the terminator included, so a
run of a loop that never ends runs out of fuel at every budget: it
diverges.

`cond_br` ends in one of two ways, at a successor or with UB, and never
chooses. So its rule is a function, `condBrExit`, to `Ev`, the ways a
computation of the set monad may end, and `exitOfEv` makes it a rule in
any monad with the UB effect, as the core dialect's semantics asks. Its UB
has the reason `cond_br on poison`, which names the op and its case.
Reasons are for people: refinement ignores them.
-/

namespace Fir.Core

/-- Where `br` sends control: to its one successor. -/
def brExit : Exit := .goto 0

/-- Where `cond_br` sends control on the condition `c`: to its first
successor when `c` is `true`, and to its second when `c` is `false`. A
poison condition is immediate UB. -/
def condBrExit : PoisonOr (BitVec 1) → Ev Exit
  | .value c => .ok (if c = 1 then .goto 0 else .goto 1)
  | .poison => .ub "cond_br on poison"

/-- The rule, in any monad with the UB effect, of a terminator that ends
as `e` says: at the place `e` gives, or with immediate UB. -/
def exitOfEv {m : Type → Type} [Monad m] [MonadUB m] : Ev Exit → m Exit
  | .ok x => pure x
  | .ub r => MonadUB.ub r

/-! # Tests

`true` is the `i1` value `1`, and `false` is `0`. -/

#guard brExit == .goto 0
#guard condBrExit (.value 1) == .ok (.goto 0)
#guard condBrExit (.value 0) == .ok (.goto 1)
#guard condBrExit .poison == .ub "cond_br on poison"

end Fir.Core
