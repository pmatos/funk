import Fir.Core.Values

/-!
# Return and unreachable

The terminators' execution rules say where control goes when a block
ends. This section gives `ret` and `unreachable` their rules, and the next
gives `br` and `cond_br` theirs.

`ret` sends control back to the caller, and the interpreter returns its
operands as they are, any number of them (ADR-2026-10-30-0816). Poison is
returned as poison: `ret` is one of the exceptions to poison propagation
that pass values on (ADR-2026-10-29-2006). Validation makes the returned
values the function's result types.

`unreachable` sends control nowhere: reaching it is immediate UB
(ADR-2026-11-09-1548). It has no operands, so no poison reaches it, and no
successors. A producer puts it where it knows control never goes, such as
after a call that never returns, and a compiler may then assume that no
run reaches it. Its UB has the reason `unreachable reached`. It is an
exception to poison propagation that is always UB, which the poison
classes section allows (ADR-2026-10-29-2006).
-/

namespace Fir.Core

/-- Where `ret` sends control: back to the caller. -/
def retExit : Exit := .ret

/-- Where `unreachable` sends control: nowhere, since reaching it is
immediate UB. -/
def unreachableExit : Ev Exit := .ub "unreachable reached"

end Fir.Core
