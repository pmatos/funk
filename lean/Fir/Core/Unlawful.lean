import Fir.Core.Poison

/-!
# Semantics that the obligations reject

The poison obligations are propositions, so a check that they reject a
semantics is a theorem, as a check that validation rejects a function is.
Each semantics below is a candidate `DialectDenote CoreDialect SetM` that
breaks one rule of this chapter, and a theorem shows that the obligations
reject it.

* `noOutcome`: no op has any outcome. Totality rejects it.
* `poisonIsUB`: every op is immediate UB when an operand is poison, and
  returns some result otherwise. Its `add` turns a poison operand into UB,
  which would undo the deferral that poison exists for. The clause "UB only
  by the op's own rules" rejects it: on operands with no poison, this `add`
  is never UB.
* `oldSDiv`: `sdiv` by the rule that the human rejected, under which a
  poison dividend by `-1` gives poison. Monotonicity rejects it: refining
  the poison to the signed minimum turns a result into UB.
* `alwaysUB`: every op is UB on every operand vector. It meets the poison
  clauses, and the obligation that a propagating op returns a result on
  some defined operands rejects it.
-/

namespace Fir.Core.Unlawful

/-- No op has any outcome. -/
@[instance_reducible] def noOutcome : DialectDenote CoreDialect SetM where
  denote _ _ := fun _ => False
  exit _ _ := fun _ => False

/-- Totality rejects a semantics in which an op has no outcome. -/
theorem noOutcome_unlawful : ¬ @LawfulDialectPoison CoreDialect _ _ _ _ _ noOutcome := by
  intro h
  obtain ⟨_, he⟩ := (h.total (.add 1 {}) (.cons .poison (.cons .poison .nil))).1 rfl
  exact he

/-- Every op is immediate UB when an operand is poison, and returns some
result otherwise. -/
@[instance_reducible] def poisonIsUB : DialectDenote CoreDialect SetM where
  denote _ args := fun e =>
    (args.Any TyPoison.IsPoison ∧ ∃ r, e = .ub r) ∨
      (¬ args.Any TyPoison.IsPoison ∧ ∃ rs, e = .ok rs)
  exit _ _ := fun e => ∃ r, e = .ub r

/-- An `add` that is UB on a poison operand is not UB by its own rules: on
operands with no poison, it is never UB. -/
theorem poisonIsUB_unlawful : ¬ @LawfulDialectPoison CoreDialect _ _ _ _ _ poisonIsUB := by
  intro h
  letI := poisonIsUB
  let args : HVector toType (sig (d := CoreDialect) (.add 1 {})) :=
    .cons .poison (.cons .poison .nil)
  have hp : args.Any TyPoison.IsPoison := Or.inl rfl
  obtain ⟨_, ⟨hn, _⟩, _, hub⟩ :=
    (h.propagates (.add 1 {}) rfl).ubByOwnRules args "poison" hp (Or.inl ⟨hp, _, rfl⟩)
  rcases hub with ⟨hp', _⟩ | ⟨_, _, he⟩
  · exact hn hp'
  · cases he

/-- `sdiv` of two values by the rejected rule: a zero or poison divisor is
UB, and so is the signed minimum by `-1`, but a poison dividend by `-1`
gives poison. -/
def sdivOld (w : Nat) : PoisonOr (BitVec w) → PoisonOr (BitVec w) → SetM (PoisonOr (BitVec w))
  | _, .poison => fun e => ∃ r, e = .ub r
  | .poison, .value b => fun e => if b = 0 then ∃ r, e = .ub r else e = .ok .poison
  | .value a, .value b => fun e =>
    if b = 0 ∨ (a = BitVec.intMin w ∧ b = -1) then ∃ r, e = .ub r
    else e = .ok (.value (a.sdiv b))

/-- `sdiv` by the rejected rule; every other op is UB. -/
@[instance_reducible] def oldSDiv : DialectDenote CoreDialect SetM where
  denote
    | .sdiv w _, .cons a (.cons b .nil) => fun
      | .ok (.cons q .nil) => sdivOld w a b (.ok q)
      | .ub r => sdivOld w a b (.ub r)
    | _, _ => fun e => ∃ r, e = .ub r
  exit _ _ := fun e => ∃ r, e = .ub r

/-- Monotonicity rejects the rule that a poison dividend by `-1` gives
poison: the signed minimum refines that poison, and by `-1` it is UB. -/
theorem oldSDiv_not_monotone : ¬ @OpMonotone CoreDialect _ _ oldSDiv _ (.sdiv 8 false) := by
  intro h
  have hargs : HVector.Forall₂ TyRefinement.IsRefinedBy
      (.cons .poison (.cons (.value (-1)) .nil) : HVector toType (sig (d := CoreDialect) (.sdiv 8 false)))
      (.cons (.value (BitVec.intMin 8)) (.cons (.value (-1)) .nil)) :=
    ⟨trivial, rfl, trivial⟩
  have hub : oldSDiv.denote (.sdiv 8 false)
      (.cons (.value (BitVec.intMin 8)) (.cons (.value (-1)) .nil)) (.ub "INT_MIN / -1") := by
    show sdivOld 8 _ _ _
    simp [sdivOld]
  obtain ⟨e, he, hr⟩ := (h _ _ hargs).1 rfl _ hub
  match e, he, hr with
  | .ub r, he, _ =>
    have he : sdivOld 8 .poison (.value (-1)) (.ub r) := he
    simp [sdivOld] at he
  | .ok (.cons _ .nil), _, hr => exact hr

/-- So the obligations reject the rule. -/
theorem oldSDiv_unlawful : ¬ @LawfulDialectPoison CoreDialect _ _ _ _ _ oldSDiv :=
  fun h => oldSDiv_not_monotone (h.monotone _)

/-!
# A semantics that is always UB

A semantics in which every op is UB on every operand vector, the defined
ones included, meets the poison clauses: for it, UB is each op's own rule,
so UB on a poison operand is too. The obligation that every propagating op
returns a result on some operand vector with no poison rejects it.
Exceptions are exempt from that obligation, so an exception that is always
UB, such as a future `unreachable`, stays allowed.

The obligations still do not fix what an op computes, such as `add` of two
values giving their sum. The semantics of each op family (#10, #14 to #20)
does.
-/

/-- Each poison replaced by the value `0`. -/
def fillZero : {ts : List Ty} → HVector toType ts → HVector toType ts
  | [], .nil => .nil
  | .int _ :: _, .cons x xs =>
    .cons (.value (match (x : PoisonOr _) with | .poison => 0 | .value v => v)) (fillZero xs)
  | .ptr :: _, .cons x _ => nomatch (x : Empty)

/-- `fillZero` puts a defined value in place of each poison. -/
theorem fillZero_fills :
    ∀ {ts : List Ty} (xs : HVector toType ts), xs.IsFilledBy (d := CoreDialect) (fillZero xs)
  | [], .nil => ⟨fun h => h, trivial⟩
  | .int _ :: _, .cons x xs => by
    obtain ⟨hn, hr⟩ := fillZero_fills xs
    refine ⟨?_, ?_, hr⟩
    · rintro (h | h)
      · cases x <;> cases h
      · exact hn h
    · cases x
      · exact .inl rfl
      · exact .inr rfl
  | .ptr :: _, .cons x _ => nomatch (x : Empty)

/-- Every op is UB on every operand vector. -/
@[instance_reducible] def alwaysUB : DialectDenote CoreDialect SetM where
  denote _ _ := fun e => ∃ r, e = .ub r
  exit _ _ := fun e => ∃ r, e = .ub r

/-- The poison clauses accept a semantics in which every op is always UB. -/
theorem alwaysUB_propagatesPoison (op : Op) :
    @PropagatesPoison CoreDialect _ _ _ alwaysUB op := by
  letI := alwaysUB
  exact {
    poisonOut := fun _ _ _ ⟨_, h⟩ => nomatch h
    ubByOwnRules := fun args r _ _ => ⟨fillZero args, fillZero_fills args, r, r, rfl⟩ }

/-- But the obligations reject it: `add` returns no result on any operands. -/
theorem alwaysUB_unlawful : ¬ @LawfulDialectPoison CoreDialect _ _ _ _ _ alwaysUB := by
  intro h
  obtain ⟨_, _, _, _, he⟩ := h.returnsOnDefined (.add 1 {}) rfl
  cases he

end Fir.Core.Unlawful
