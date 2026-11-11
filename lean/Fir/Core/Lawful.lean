import Fir.Core.CallRefine
import Fir.Execution.Lawful

/-!
# Every valid core op instance meets the obligations

The core dialect is lawful: it meets the poison obligations. Each of them
is proved for every core op instance whose types validation accepts, from
the obligations that each op family proves, in the sections from the
constant obligations to the branch obligations:

* _Propagation._ Each of the 21 ops that propagate poison does, at every
  width and float format: `const` at an integer and at a float type,
  `poison`, the arithmetic, the four divisions, the bitwise ops and
  shifts, `icmp`, `fcmp` and the width changes.
* _A result on defined operands._ Each of them returns a result on some
  operand vector with no poison. `poison` does on the empty vector, where
  its result is poison: the obligation asks for a result, not for a
  defined one (ADR-2026-11-03-1615). The four divisions do only at a
  width above zero, and validation accepts `iN` only for N of at least
  1, so they do at every valid width. This is the one obligation that needs the
  instance to be valid (ADR-2026-11-02-1515).
* _Poison is refined by every value._ A poison `iN` is refined by every
  value of `iN`, at every width; `ptr`, which validation rejects, has no
  values.
* _Totality and monotonicity._ Every core terminator and every core op
  with no callee is total and monotone, at every width: every core op but
  `call`, which the obligations leave out, since its meaning is its
  callee's run (ADR-2026-11-02-1514).

So every generic theorem that asks for a lawful dialect holds for the core
dialect. For example, every function of a valid core module has an
outcome at every budget by the class alone (the section on what the
lawful class gives), as the section on core functions with calls shows by
the ops' own obligations.
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
  | .fcmp p e m, _ => fcmp_propagatesPoison p e m
  | .zext m n, _ => zext_propagatesPoison m n
  | .sext m n, _ => sext_propagatesPoison m n
  | .trunc m n, _ => trunc_propagatesPoison m n
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
theorem Op.returnsOnDefined_valid : (op : Op) → TypesValid (d := CoreDialect) op →
    Fir.poisonClass (d := CoreDialect) op = .propagates → ReturnsOnDefined (d := CoreDialect) op
  | .const w v, _, _ => const_returnsOnDefined w v
  | .fconst e m v, _, _ => fconst_returnsOnDefined e m v
  | .add w f, _, _ => add_returnsOnDefined w f
  | .sub w f, _, _ => sub_returnsOnDefined w f
  | .mul w f, _, _ => mul_returnsOnDefined w f
  | .sdiv w x, hv, _ => sdiv_returnsOnDefined w (pos_of_typesValid hv List.mem_cons_self) x
  | .udiv w x, hv, _ => udiv_returnsOnDefined w (pos_of_typesValid hv List.mem_cons_self) x
  | .srem w, hv, _ => srem_returnsOnDefined w (pos_of_typesValid hv List.mem_cons_self)
  | .urem w, hv, _ => urem_returnsOnDefined w (pos_of_typesValid hv List.mem_cons_self)
  | .and w, _, _ => and_returnsOnDefined w
  | .or w, _, _ => or_returnsOnDefined w
  | .xor w, _, _ => xor_returnsOnDefined w
  | .shl w, _, _ => shl_returnsOnDefined w
  | .lshr w, _, _ => lshr_returnsOnDefined w
  | .ashr w, _, _ => ashr_returnsOnDefined w
  | .icmp p w, _, _ => icmp_returnsOnDefined p w
  | .fcmp p e m, _, _ => fcmp_returnsOnDefined p e m
  | .zext m n, _, _ => zext_returnsOnDefined m n
  | .sext m n, _, _ => sext_returnsOnDefined m n
  | .trunc m n, _, _ => trunc_returnsOnDefined m n
  | .poison w, _, _ => poison_returnsOnDefined w
  | .select _, _, h | .freeze _, _, h | .br, _, h | .condBr, _, h | .ret _, _, h | .unreachable, _, h
  | .call .., _, h => nomatch h

end Fir.Core

namespace Fir

/-- The core dialect is lawful: every core op instance whose types
validation accepts meets the poison obligations. -/
theorem Core.lawfulDialectPoison : LawfulDialectPoison CoreDialect where
  poison_isRefinedBy _ := Core.Ty.poison_isRefinedBy
  propagates op _ := Core.Op.propagates_all op
  returnsOnDefined := Core.Op.returnsOnDefined_valid
  total op _ := Core.Op.total_all op
  monotone op _ := Core.Op.monotone_all op

instance : LawfulDialectPoison CoreDialect := Core.lawfulDialectPoison

end Fir
