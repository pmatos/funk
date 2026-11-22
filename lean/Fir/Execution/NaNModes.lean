import Fir.Execution.MemoryModes

/-!
# Exhaustive runs that try a few NaNs

A float op whose result is a NaN chooses its sign and mantissa: `m + 1` bits
in `float<e,m>`, 24 in `f32` and 53 in `f64` (ADR-2026-11-09-1549). Exhaustive
mode tries every value of a choice, so a run that makes such a choice goes past
any budget it can walk. The tree labels that choice, `ChoiceKind.nan e`, and
the walk below tries, at a NaN choice, only a few NaNs: the positive quiet NaN,
and each bit pattern of a list it is given that is a NaN of the format.
At every other choice it tries every value, as exhaustive mode does
(ADR-2026-11-16-0855).

So the walk finds a part of the run's set, not all of it. Each leaf it lists
is a way the tree may end, and each leaf counts the NaN choices on its path.
When no path made a NaN choice, the list is exactly the set, as exhaustive
mode's is. The harness gives the walk the bits of what native code returned, so
that a NaN that native code gives is one the walk tries
(`docs/decisions/fir-ref.md#trying-a-few-nans`).

The walk charges its budget the bits that count the values it tries at a
choice: `w` at a choice of `w` bits, and at a NaN choice the fewest bits that
count its NaNs. So the budget bounds the number of paths, as in exhaustive
mode.
-/

namespace Fir

namespace ChoiceTree

variable {ε α : Type}

/-- Whether `n` is the bits of a NaN of `float<e,m>`: below `2 ^ (1 + e + m)`,
with every exponent bit set and a mantissa that is not zero. -/
def isNaNBits (e m n : Nat) : Bool :=
  n < 2 ^ (1 + e + m) && (n / 2 ^ m) % 2 ^ e == 2 ^ e - 1 && n % 2 ^ m != 0

/-- The NaNs that the walk tries at a NaN choice of `w = m + 1` bits in
`float<e,m>`, as the values of the choice, the top bit the sign and the low
`m` bits the mantissa: the positive quiet NaN, with only the top mantissa
bit set, then each NaN of `nans`, each value once. With no NaNs given, a NaN
choice tries one value and charges nothing, so a run with any number of NaN
choices has one path through them. -/
def nanTries (nans : List Nat) (e w : Nat) : List (BitVec w) :=
  let m := w - 1
  ((2 ^ (m - 1) ::
      (nans.filter (isNaNBits e m)).map fun n => n / 2 ^ (e + m) * 2 ^ m + n % 2 ^ m).map
    (BitVec.ofNat w)).eraseDups

/-- The fewest bits that count `n` values. -/
def bitsFor (n : Nat) : Nat := Nat.log2 (2 * n - 1)

/-- What the walk does at a choice of `w` bits of the kind `c`: the values
it tries, the bits it charges, and whether the choice is a NaN's (`1`) or
not (`0`). -/
def tryAt (nans : List Nat) (w : Nat) : ChoiceKind → List (BitVec w) × Nat × Nat
  | .bits => (allBits w, w, 0)
  | .nan e => let ts := nanTries nans e w; (ts, bitsFor ts.length, 1)

/-- The walk that tries a few NaNs, with the NaNs `nans`: every leaf it
reaches, each with the choices and the NaN choices on its path, when no path
charges more than `budget` bits in all, and `none` otherwise. The paths come
in order: at each choice, the values it tries, in order. -/
def exploreNaN (nans : List Nat) : ChoiceTree ε α → Nat → Option (List (Leaf ε α × Nat × Nat))
  | .pure a, _ => some [(.ok a, 0, 0)]
  | .ub r, _ => some [(.ub r, 0, 0)]
  | .noOutcome e, _ => some [(.noOutcome e, 0, 0)]
  | .choose w c k, budget =>
    let t := tryAt nans w c
    if t.2.1 ≤ budget then
      collect (fun b => ((k b).exploreNaN nans (budget - t.2.1)).map
        (List.map fun p => (p.1, p.2.1 + 1, p.2.2 + t.2.2))) t.1 []
    else none

/-- Each leaf that the walk lists, that has an outcome, is a way the tree
may end. -/
theorem exploreNaN_sub {nans : List Nat} :
    ∀ {t : ChoiceTree ε α} {budget : Nat} {ls : List (Leaf ε α × Nat × Nat)},
      t.exploreNaN nans budget = some ls → ∀ p ∈ ls, ∀ e, p.1.ev? = some e → t.toSet e
  | .pure _, _, _, h, p, hp, e, he | .ub _, _, _, h, p, hp, e, he
  | .noOutcome _, _, _, h, p, hp, e, he => by
    cases h
    rw [List.mem_singleton.1 hp] at he
    cases he <;> rfl
  | .choose w c k, budget, ls, h, p, hp, e, he => by
    simp only [exploreNaN] at h
    split at h
    · rcases (collect_mem h p).1 hp with hp | ⟨b, _, l, hl, hpl⟩
      · nomatch hp
      · obtain ⟨lb, hlb, rfl⟩ := Option.map_eq_some_iff.1 hl
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hpl
        exact ⟨b, exploreNaN_sub hlb q hq e he⟩
    · cases h

theorem collect_ne_nil {g : β → Option (List γ)} {bs : List β} {ls : List γ}
    (h : collect g bs [] = some ls) (hb : bs ≠ []) (hg : ∀ b l, g b = some l → l ≠ []) :
    ls ≠ [] := by
  obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil bs hb
  obtain ⟨l, hl⟩ := collect_some h b hb
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil l (hg b l hl)
  exact List.ne_nil_of_mem ((collect_mem h x).2 (.inr ⟨b, hb, l, hl, hx⟩))

theorem nanTries_ne_nil (nans : List Nat) (e w : Nat) : nanTries nans e w ≠ [] :=
  List.ne_nil_of_mem (List.mem_eraseDups.2 List.mem_cons_self)

theorem tryAt_ne_nil (nans : List Nat) (w : Nat) (c : ChoiceKind) : (tryAt nans w c).1 ≠ [] := by
  cases c with
  | bits => exact List.ne_nil_of_mem (mem_allBits 0)
  | nan e => exact nanTries_ne_nil nans e w

/-- The walk lists at least one leaf. -/
theorem exploreNaN_ne_nil {nans : List Nat} :
    ∀ {t : ChoiceTree ε α} {budget : Nat} {ls : List (Leaf ε α × Nat × Nat)},
      t.exploreNaN nans budget = some ls → ls ≠ []
  | .pure _, _, _, h | .ub _, _, _, h | .noOutcome _, _, _, h => by cases h; simp
  | .choose w c k, budget, ls, h => by
    simp only [exploreNaN] at h
    split at h
    · refine collect_ne_nil h (tryAt_ne_nil nans w c) fun b l hl => ?_
      obtain ⟨lb, hlb, rfl⟩ := Option.map_eq_some_iff.1 hl
      simpa using exploreNaN_ne_nil hlb
    · cases h

/-- When no leaf that the walk lists made a NaN choice, the walk lists
exactly the tree's set, as exhaustive mode does. -/
theorem exploreNaN_toSet {nans : List Nat} :
    ∀ {t : ChoiceTree ε α} {budget : Nat} {ls : List (Leaf ε α × Nat × Nat)},
      t.exploreNaN nans budget = some ls → (∀ p ∈ ls, p.2.2 = 0) →
        ∀ e, t.toSet e ↔ ∃ p ∈ ls, p.1.ev? = some e
  | .pure a, _, ls, h, _, e | .ub a, _, ls, h, _, e => by
    cases h
    exact ⟨fun he => ⟨_, List.mem_singleton_self _, by rw [he]; rfl⟩,
      fun ⟨_, hp, he⟩ => by rw [List.mem_singleton.1 hp] at he; cases he; rfl⟩
  | .noOutcome _, _, ls, h, _, e => by
    cases h
    exact ⟨False.elim, fun ⟨_, hp, he⟩ => by rw [List.mem_singleton.1 hp] at he; cases he⟩
  | .choose w c k, budget, ls, h, h0, e => by
    have hs := exploreNaN_sub h
    simp only [exploreNaN] at h
    split at h
    · have hall : ∀ b ∈ (tryAt nans w c).1, ∃ lb,
          (k b).exploreNaN nans (budget - (tryAt nans w c).2.1) = some lb ∧
            ∀ q ∈ lb, (q.1, q.2.1 + 1, q.2.2 + (tryAt nans w c).2.2) ∈ ls := by
        intro b hb
        obtain ⟨l, hl⟩ := collect_some h b hb
        obtain ⟨lb, hlb, rfl⟩ := Option.map_eq_some_iff.1 hl
        exact ⟨lb, hlb, fun q hq =>
          (collect_mem h _).2 (.inr ⟨b, hb, _, hl, List.mem_map.2 ⟨q, hq, rfl⟩⟩)⟩
      cases c with
      | nan e' =>
        exfalso
        obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _ (tryAt_ne_nil nans w (.nan e'))
        obtain ⟨lb, hlb, hin⟩ := hall b hb
        obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil lb (exploreNaN_ne_nil hlb)
        have := h0 _ (hin q hq)
        simp [tryAt] at this
      | bits =>
        constructor
        · rintro ⟨b, hb⟩
          obtain ⟨lb, hlb, hin⟩ := hall b (mem_allBits b)
          have h0' : ∀ q ∈ lb, q.2.2 = 0 := fun q hq => by
            have := h0 _ (hin q hq)
            simpa [tryAt] using this
          obtain ⟨q, hq, hqe⟩ := (exploreNaN_toSet hlb h0' e).1 hb
          exact ⟨_, hin q hq, hqe⟩
        · rintro ⟨p, hp, hpEv⟩
          exact hs p hp e hpEv
    · cases h

end ChoiceTree

/-! # The walk of a run with memory -/

open Memory

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  {N : Type} [DecidableEq N] {ε : Type}
  [DialectEffects d] [DialectMemDenote d] (lay : N → MemLayout)
  (ρ : DialectEffects.Mem d → N) (L : RunItems) [DialectDenote d (StateT (Memories N (unitsOf lay))
      (ChoiceTree ε))]

/-- Each outcome that the walk that tries a few NaNs lists is an outcome of
the run with memory at the fuel budget it runs with. -/
theorem Func.memExploreNaN_outcomes (h : MemMapsDenote (d := d) lay (ε := ε) ρ L) (M : Module d)
    (f : Func d) (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat) (nans : List Nat)
    {ls : List (ChoiceTree.Leaf ε (Except Stuck (Result (List (DVal d)))) × Nat × Nat)}
    (hx : (f.memTree (unitsOf lay) (RunItems.start d lay ρ L) M args fuel).exploreNaN nans budget = some ls)
    {p : ChoiceTree.Leaf ε (Except Stuck (Result (List (DVal d)))) × Nat × Nat} (hp : p ∈ ls)
    {o : Outcome (List (DVal d))} (ho : p.1.pathEnd = .outcome o) :
    Run.outcomes (f.memRuns lay ρ L M args fuel) o := by
  rw [Run.outcomes_iff, ← Func.memTree_toSet lay ρ L h]
  exact ChoiceTree.exploreNaN_sub hx p hp _ ((ChoiceTree.Leaf.ev?_eq_outcome p.1 o).2 ho)

/-- A stuck path that the walk lists is a stuck path of the run with
memory. -/
theorem Func.memExploreNaN_stuck (h : MemMapsDenote (d := d) lay (ε := ε) ρ L) (M : Module d)
    (f : Func d) (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat) (nans : List Nat)
    {ls : List (ChoiceTree.Leaf ε (Except Stuck (Result (List (DVal d)))) × Nat × Nat)}
    (hx : (f.memTree (unitsOf lay) (RunItems.start d lay ρ L) M args fuel).exploreNaN nans budget = some ls)
    {p : ChoiceTree.Leaf ε (Except Stuck (Result (List (DVal d)))) × Nat × Nat} (hp : p ∈ ls)
    {st : Stuck} (hst : p.1.pathEnd = .stuck st) :
    Run.IsStuck (f.memRuns lay ρ L M args fuel) := by
  obtain ⟨st', he⟩ := (ChoiceTree.Leaf.ev?_eq_stuck p.1).2 ⟨st, hst⟩
  exact ⟨st', by rw [← Func.memTree_toSet lay ρ L h]; exact ChoiceTree.exploreNaN_sub hx p hp _ he⟩

/-- When no path that the walk lists made a NaN choice, it lists exactly the
outcomes of the run with memory, as exhaustive mode does. -/
theorem Func.memExploreNaN_exact (h : MemMapsDenote (d := d) lay (ε := ε) ρ L) (M : Module d)
    (f : Func d) (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat) (nans : List Nat)
    {ls : List (ChoiceTree.Leaf ε (Except Stuck (Result (List (DVal d)))) × Nat × Nat)}
    (hx : (f.memTree (unitsOf lay) (RunItems.start d lay ρ L) M args fuel).exploreNaN nans budget = some ls)
    (h0 : ∀ p ∈ ls, p.2.2 = 0) (o : Outcome (List (DVal d))) :
    Run.outcomes (f.memRuns lay ρ L M args fuel) o ↔ ∃ p ∈ ls, p.1.pathEnd = .outcome o := by
  rw [Run.outcomes_iff, ← Func.memTree_toSet lay ρ L h, ChoiceTree.exploreNaN_toSet hx h0]
  simp only [ChoiceTree.Leaf.ev?_eq_outcome]

end Fir
