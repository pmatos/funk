import Fir.Core.Ops
import Fir.Execution.OpEffects

/-!
# The effects of the core ops

Every core op of M0 is pure, may produce poison, may hit UB, or is a
terminator, as its rules say (ADR-2026-11-09-1541). No core op reads,
writes, allocates or frees memory, or adds an event to the trace: the core
dialect has no memory yet, so its memories have no names, and M0's runs
have no trace.

* Pure: `const`, `and`, `or`, `xor`, `icmp`, `select`, `zext`, `sext`,
  `trunc`, `freeze`, and `add`, `sub` and `mul` without flags. On operands
  with no poison each gives a defined result, and none hits UB. `select`
  gives poison only for a poison condition or a poison operand that it
  chooses, and `freeze` gives defined bits.
* May produce poison: `poison`; `add`, `sub` and `mul` with a flag, which
  give poison when the flag is broken; and the shifts, which give poison
  for an amount of `N` or more.
* May-UB: the four divisions, on a zero or poison divisor, and `sdiv` and
  `srem` on the signed minimum or a poison dividend by `-1`. `sdiv` and
  `udiv` with `exact` may produce poison too.
* Control: the terminators `br`, `ret` and `cond_br`. `cond_br` may hit UB
  too, on a poison condition.

`call`'s own rule does nothing but run its callee, so its own set is
empty. That does not make a call pure: a call has its callee's effects too,
which come from the callee's run, and a reader of a call's effects adds
them.

The proofs that each declaration is sound are in the section on the core
dialect's effect obligations, after the rules.
-/

namespace Fir.Core

/-- The core dialect has no memory yet, so no memory has a name. -/
abbrev Mem : Type := Empty

/-- The effects of each core op instance. Each op is listed, with no case
for the rest, so a new core op does not build until it declares its
effects (ADR-2026-11-03-0600). A flag of `add`, `sub` or `mul`, and `exact`
on a division, may produce poison. -/
def Op.effects : Op → Effects Mem
  | .const .. | .and _ | .or _ | .xor _ | .icmp .. | .select _ | .zext .. | .sext .. | .trunc ..
  | .freeze _ | .call .. => {}
  | .add _ f | .sub _ f | .mul _ f => { mayPoison := f != {} }
  | .sdiv _ x | .udiv _ x => { mayUB := true, mayPoison := x }
  | .srem _ | .urem _ => { mayUB := true }
  | .shl _ | .lshr _ | .ashr _ | .poison _ => { mayPoison := true }
  | .br | .ret _ => { control := true }
  | .condBr => { mayUB := true, control := true }

end Fir.Core
