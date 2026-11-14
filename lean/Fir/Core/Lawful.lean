import Fir.Core.CallRefine
import Fir.Execution.Lawful

/-!
# Every valid core op instance meets the obligations

Each core op that touches no memory meets the poison obligations in the
set monad, at every core op instance whose types validation accepts, from
the obligations that each op family proves, in the sections from the
constant obligations to the branch obligations:

* _Propagation._ Each of the 34 ops that propagate poison does, at every
  width and float format: `const` at an integer and at a float type,
  `poison`, the arithmetic, the four divisions, the bitwise ops and
  shifts, `icmp`, `fcmp`, the width changes, the float arithmetic, the
  bit casts, the conversions from integers, the conversions between
  formats, the pointer offset, the conversions to integers and `alloca`,
  which has no operands.
* _A result on defined operands._ Each of them but `alloca` returns a
  result on some operand vector with no poison. `poison` does on the empty
  vector, where its result is poison: the obligation asks for a result, not
  for a defined one (ADR-2026-10-29-2006). The four divisions do only at a
  width above zero, and validation accepts `iN` only for N of at least
  1, so they do at every valid width. This is the one obligation that needs the
  instance to be valid (ADR-2026-10-29-2006).
* _Poison is refined by every value._ A poison of a core type is refined
  by every value of that type: of `iN` at every width, of every float
  format, and of every pointer type, whose values are pointers.
* _Totality and monotonicity._ Every core terminator and every core op
  with no callee is total and monotone, at every width: every core op but
  `call`, which the obligations leave out, since its meaning is its
  callee's run (ADR-2026-10-29-2006), and `alloca`, which is monotone at
  once but not total, since it has no rule in the set monad.

So the core dialect as a whole does not meet the lawful class of the set
monad: `alloca` has no outcome there. Its obligations are those of the
semantics with memory, which each op meets: an op that touches no memory
from its tie and what it meets here, and `alloca` by its own rule (the
sections on the stack allocation obligations and on every valid core
function, with memory).
-/

namespace Fir.Core

/-- Each core op that propagates poison does, at every width. -/
theorem Op.propagates_all : (op : Op) → Fir.poisonClass (d := CoreDialect) op = .propagates →
    PropagatesPoison (d := CoreDialect) op
  | .const w v, _ => const_propagatesPoison w v
  | .fconst e m v, _ => fconst_propagatesPoison e m v
  | .add w f, _ => add_propagatesPoison w f
  | .sub w f, _ => sub_propagatesPoison w f
  | .mul w f, _ => mul_propagatesPoison w f
  | .sdiv w x, _ => sdiv_propagatesPoison w x
  | .udiv w x, _ => udiv_propagatesPoison w x
  | .srem w, _ => srem_propagatesPoison w
  | .urem w, _ => urem_propagatesPoison w
  | .and w, _ => and_propagatesPoison w
  | .or w, _ => or_propagatesPoison w
  | .xor w, _ => xor_propagatesPoison w
  | .shl w, _ => shl_propagatesPoison w
  | .lshr w, _ => lshr_propagatesPoison w
  | .ashr w, _ => ashr_propagatesPoison w
  | .icmp p w, _ => icmp_propagatesPoison p w
  | .fcmp p fl e m, _ => fcmp_propagatesPoison p fl e m
  | .fbin o fl e m, _ => fbin_propagatesPoison o fl e m
  | .funary o fl e m, _ => funary_propagatesPoison o fl e m
  | .fma fl e m, _ => fma_propagatesPoison fl e m
  | .zext m n, _ => zext_propagatesPoison m n
  | .sext m n, _ => sext_propagatesPoison m n
  | .trunc m n, _ => trunc_propagatesPoison m n
  | .toBits e m, _ => toBits_propagatesPoison e m
  | .ofBits e m, _ => ofBits_propagatesPoison e m
  | .sitofp n e m, _ => intToFloat_propagatesPoison n e m true
  | .uitofp n e m, _ => intToFloat_propagatesPoison n e m false
  | .fpext e m e' m', _ => convertFloat_propagatesPoison e m e' m' true
  | .fptrunc e m e' m', _ => convertFloat_propagatesPoison e m e' m' false
  | .ptradd n w, _ => ptradd_propagatesPoison n w
  | .alloca k t c a n, _ => alloca_propagatesPoison k t c a n
  | .fptosi e m n, _ => floatToInt_propagatesPoison e m n true
  | .fptoui e m n, _ => floatToInt_propagatesPoison e m n false
  | .poison w, _ => poison_propagatesPoison w
  | .select _, h | .freeze _, h | .br, h | .condBr, h | .ret _, h | .unreachable, h
  | .call .., h => nomatch h

/-- A valid core op instance with an operand of type `iN` has `N` above
zero. -/
theorem pos_of_typesValid {op : Op} {w : Nat} (hv : TypesValid (d := CoreDialect) op)
    (hw : i w ∈ Fir.sig (d := CoreDialect) op) : 0 < w :=
  (hv.1 _ hw).1

/-- Each valid core op instance that propagates poison returns a result on
some operand vector with no poison. The divisions need their width above
zero, which validation gives. -/
theorem Op.returnsOnDefined_valid : (op : Op) → op.touchesMemory = false →
    TypesValid (d := CoreDialect) op → Fir.poisonClass (d := CoreDialect) op = .propagates →
    ReturnsOnDefined (d := CoreDialect) op
  | .const w v, _, _, _ => const_returnsOnDefined w v
  | .fconst e m v, _, _, _ => fconst_returnsOnDefined e m v
  | .add w f, _, _, _ => add_returnsOnDefined w f
  | .sub w f, _, _, _ => sub_returnsOnDefined w f
  | .mul w f, _, _, _ => mul_returnsOnDefined w f
  | .sdiv w x, _, hv, _ => sdiv_returnsOnDefined w (pos_of_typesValid hv List.mem_cons_self) x
  | .udiv w x, _, hv, _ => udiv_returnsOnDefined w (pos_of_typesValid hv List.mem_cons_self) x
  | .srem w, _, hv, _ => srem_returnsOnDefined w (pos_of_typesValid hv List.mem_cons_self)
  | .urem w, _, hv, _ => urem_returnsOnDefined w (pos_of_typesValid hv List.mem_cons_self)
  | .and w, _, _, _ => and_returnsOnDefined w
  | .or w, _, _, _ => or_returnsOnDefined w
  | .xor w, _, _, _ => xor_returnsOnDefined w
  | .shl w, _, _, _ => shl_returnsOnDefined w
  | .lshr w, _, _, _ => lshr_returnsOnDefined w
  | .ashr w, _, _, _ => ashr_returnsOnDefined w
  | .icmp p w, _, _, _ => icmp_returnsOnDefined p w
  | .fcmp p fl e m, _, _, _ => fcmp_returnsOnDefined p fl e m
  | .fbin o fl e m, _, _, _ => fbin_returnsOnDefined o fl e m
  | .funary o fl e m, _, _, _ => funary_returnsOnDefined o fl e m
  | .fma fl e m, _, _, _ => fma_returnsOnDefined fl e m
  | .zext m n, _, _, _ => zext_returnsOnDefined m n
  | .sext m n, _, _, _ => sext_returnsOnDefined m n
  | .trunc m n, _, _, _ => trunc_returnsOnDefined m n
  | .toBits e m, _, _, _ => toBits_returnsOnDefined e m
  | .ofBits e m, _, _, _ => ofBits_returnsOnDefined e m
  | .sitofp n e m, _, _, _ => intToFloat_returnsOnDefined n e m true
  | .uitofp n e m, _, _, _ => intToFloat_returnsOnDefined n e m false
  | .fpext e m e' m', _, _, _ => convertFloat_returnsOnDefined e m e' m' true
  | .fptrunc e m e' m', _, _, _ => convertFloat_returnsOnDefined e m e' m' false
  | .ptradd n w, _, _, _ => ptradd_returnsOnDefined n w
  | .fptosi e m n, _, _, _ => floatToInt_returnsOnDefined e m n true
  | .fptoui e m n, _, _, _ => floatToInt_returnsOnDefined e m n false
  | .poison w, _, _, _ => poison_returnsOnDefined w
  | .select _, _, _, h | .freeze _, _, _, h | .br, _, _, h | .condBr, _, _, h | .ret _, _, _, h
  | .unreachable, _, _, h | .call .., _, _, h => nomatch h
  | .alloca .., h, _, _ => nomatch h

end Fir.Core
