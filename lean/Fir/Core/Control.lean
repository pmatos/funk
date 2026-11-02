import Fir.Core.Values

/-!
# Return

The terminators' execution rules say where control goes when a block ends.
Ticket #10 gives `ret` its rule, and #19 gives `br` and `cond_br` theirs,
in the next section.

`ret` sends control back to the caller, and the interpreter returns its
operands as they are, any number of them (ADR-2026-10-30-0816). Poison is
returned as poison: `ret` is one of the exceptions to poison propagation
that pass values on (ADR-2026-10-30-0818). Validation makes the returned
values the function's result types.
-/

namespace Fir.Core

/-- Where `ret` sends control: back to the caller. -/
def retExit : Exit := .ret

end Fir.Core
