import Fir.Core.FloatFlags
import Fir.Execution.OpEffects

/-!
# The effects of the core ops

Every core op of M0 is pure, may produce poison, may hit UB, or is a
terminator, as its rules say (ADR-2026-11-09-1541). The core dialect names
the memories of a module by their numbers, as a pointer type `ptr<N>` names
memory `N`, and the module's data layout says which of them it has. No core
op reads, writes, allocates or frees memory yet, or adds an event to the
trace: M0's runs have no trace.

* Pure: `const`, a float's included, `and`, `or`, `xor`, `icmp`,
  `select`, `zext`, `sext`, `trunc`, `freeze`, `add`, `sub` and `mul`
  without flags, `fcmp` and the float arithmetic, `fadd`, `fsub`, `fmul`,
  `fdiv`, `frem`, `fmod`, `fneg`, `fabs`, `sqrt` and `fma`, without `nnan`
  and `ninf`, the bit casts, the conversions from integers, `sitofp` and
  `uitofp`, the conversions between formats, `fpext` and `fptrunc`, and
  the pointer offset `ptradd`, which moves a pointer and keeps its
  provenance. `nsz` alone keeps a float op pure: it chooses a zero's sign,
  a defined value, as `freeze` chooses bits. On operands
  with no poison each gives a defined result, and none hits UB. `select`
  gives poison only for a poison condition or a poison operand that it
  chooses, and `freeze` gives defined bits. A float op's NaN is a defined
  value, and M1 has no floating-point exceptions (ADR-2026-11-09-1549).
* May produce poison: `poison`; `add`, `sub` and `mul` with a flag, which
  give poison when the flag is broken; the shifts, which give poison
  for an amount of `N` or more; `fcmp` and the float arithmetic with
  `nnan` or `ninf`, which give poison on a NaN or an infinity; and the
  conversions to integers, `fptosi` and `fptoui`, which give poison for
  an integer that `iN` does not hold, an infinity or a NaN.
* May-UB: the four divisions, on a zero or poison divisor, and `sdiv` and
  `srem` on the signed minimum or a poison dividend by `-1`. `sdiv` and
  `udiv` with `exact` may produce poison too.
* Control: the terminators `br`, `ret`, `cond_br` and `unreachable`.
  `cond_br` may hit UB too, on a poison condition, and `unreachable` hits
  UB whenever a run reaches it (ADR-2026-11-09-1548).

`call`'s own rule does nothing but run its callee, so its own set is
empty. That does not make a call pure: a call has its callee's effects too,
which come from the callee's run, and the effects of a call in place add
its callee's summary (the section on function summaries).

The proofs that each declaration is sound are in the section on the core
dialect's effect obligations, after the rules.
-/

namespace Fir.Core

/-- The core dialect names each memory of a module by its number: memory
`N` is the memory of `ptr<N>`, and memory 0 is the default memory. -/
abbrev Mem : Type := Nat

/-- The effects of each core op instance. Each op is listed, with no case
for the rest, so a new core op does not build until it declares its
effects (ADR-2026-11-03-0600). A flag of `add`, `sub` or `mul`, `exact`
on a division, and `nnan` or `ninf` on a float op, may produce poison. -/
def Op.effects : Op → Effects Mem
  | .const .. | .fconst .. | .and _ | .or _ | .xor _ | .icmp .. | .select _ | .zext .. | .sext ..
  | .trunc .. | .freeze _ | .call .. | .toBits .. | .ofBits .. | .sitofp .. | .uitofp .. | .fpext ..
  | .fptrunc .. | .ptradd .. => {}
  | .fcmp _ fl .. | .fbin _ fl .. | .funary _ fl .. | .fma fl .. => { mayPoison := fl.mayPoison }
  | .add _ f | .sub _ f | .mul _ f => { mayPoison := f != {} }
  | .sdiv _ x | .udiv _ x => { mayUB := true, mayPoison := x }
  | .srem _ | .urem _ => { mayUB := true }
  | .shl _ | .lshr _ | .ashr _ | .poison _ | .fptosi .. | .fptoui .. => { mayPoison := true }
  | .br | .ret _ => { control := true }
  | .condBr | .unreachable => { mayUB := true, control := true }

end Fir.Core
