import Fir.Execution.ChoiceTree

/-!
# Exhaustive and scripted runs

`fir-ref` has two ways to walk a tree of choices (ADR-2026-10-29-2017):

* _Exhaustive mode_ visits every path, so it finds every way the run may
  end. The number of paths doubles with each bit chosen, so it takes a
  budget on the total number of bits that one path may choose. When some
  path would choose more, it says so and gives no set, and only then:
  this is `ChoiceTree.explore_isSome_iff`. Within its budget, it gives
  exactly the run's set of outcomes: this is `ChoiceTree.explore_toSet`
  for any tree, and `Func.explore_outcomes` for a run of the interpreter.
* _Scripted mode_ follows one path: the one that a _choice sequence_ names,
  one value for each choice the run makes, in order. A sequence _fits_ the
  run when it gives exactly as many values as the run makes choices, and
  each value reads as a value of its choice's width. One that does not fit
  is an error of its own, a _misfit_, never an outcome. On a sequence that
  fits, scripted mode gives a member of the run's set of outcomes: this is
  `ChoiceTree.script_toSet`, and `Func.script_outcomes` for a run.
* _Sampled mode_ is scripted mode with no sequence given up front: it
  draws each choice as the run makes it, from a generator, and reports the
  values it drew. Those values are a sequence that fits the run, and
  scripted mode on them follows the same path: this is
  `ChoiceTree.sample_script`. So sampled mode, too, gives a member of the
  run's set of outcomes, whatever the generator.

All three modes report how many choices a path made, so that a run that
makes no choice is known to have one outcome. The choice budget is not the
fuel budget: each mode runs the interpreter at one fuel budget `n`, so the
theorems speak of `(run n).outcomes`, as the section on outcomes and
behaviours says. `fir-ref`'s command line and JSON are
ADR-2026-10-30-2218's.
-/

namespace Fir

namespace ChoiceTree

variable {ε α : Type}

/-- How one path of a tree ends: with a result, with UB, or with no
outcome. -/
inductive Leaf (ε α : Type) where
  | ok (a : α)
  | ub (reason : String)
  | noOutcome (e : ε)

/-- The way a computation of the set monad ends that a leaf stands for, if
it stands for one. -/
def Leaf.ev? : Leaf ε α → Option (Ev α)
  | .ok a => some (.ok a)
  | .ub r => some (.ub r)
  | .noOutcome _ => none

/-- Every value of `w` bits, from zero up, read as an unsigned number. -/
def allBits (w : Nat) : List (BitVec w) := (List.range (2 ^ w)).map (BitVec.ofNat w)

theorem mem_allBits {w : Nat} (b : BitVec w) : b ∈ allBits w :=
  List.mem_map.2 ⟨b.toNat, List.mem_range.2 b.isLt, by simp⟩

/-- `acc` reversed, then the lists that `g` gives for each element of `bs`,
in order and joined; `none` when `g` gives `none` for one of them. It
takes no stack per element. -/
def collect (g : β → Option (List γ)) : List β → List γ → Option (List γ)
  | [], acc => some acc.reverse
  | b :: bs, acc => match g b with
    | some l => collect g bs (l.reverseAux acc)
    | none => none

theorem collect_mem {g : β → Option (List γ)} :
    ∀ {bs : List β} {acc ls : List γ}, collect g bs acc = some ls →
      ∀ x, x ∈ ls ↔ x ∈ acc ∨ ∃ b ∈ bs, ∃ l, g b = some l ∧ x ∈ l
  | [], acc, ls, h, x => by
    cases h
    simp
  | b :: bs, acc, ls, h, x => by
    simp only [collect] at h
    split at h
    · rename_i l hl
      rw [collect_mem h x, List.reverseAux_eq, List.mem_append, List.mem_reverse]
      constructor
      · rintro ((hx | hx) | ⟨b', hb', l', hl', hx'⟩)
        · exact .inr ⟨b, List.mem_cons_self, l, hl, hx⟩
        · exact .inl hx
        · exact .inr ⟨b', List.mem_cons_of_mem _ hb', l', hl', hx'⟩
      · rintro (hx | ⟨b', hb', l', hl', hx'⟩)
        · exact .inl (.inr hx)
        · rcases List.mem_cons.1 hb' with rfl | hb'
          · rw [hl] at hl'
            cases hl'
            exact .inl (.inl hx')
          · exact .inr ⟨b', hb', l', hl', hx'⟩
    · cases h

theorem collect_some {g : β → Option (List γ)} :
    ∀ {bs : List β} {acc ls : List γ}, collect g bs acc = some ls → ∀ b ∈ bs, ∃ l, g b = some l
  | [], _, _, _, _, hb => nomatch hb
  | b :: bs, acc, ls, h, b', hb' => by
    simp only [collect] at h
    split at h
    · rename_i l hl
      rcases List.mem_cons.1 hb' with rfl | hb'
      · exact ⟨l, hl⟩
      · exact collect_some h b' hb'
    · cases h

/-- Exhaustive mode: every leaf of the tree, each with the number of
choices on its path, when no path chooses more than `budget` bits in all,
and `none` otherwise. The paths come in order: at each choice, the values
from zero up. -/
def explore : ChoiceTree ε α → Nat → Option (List (Leaf ε α × Nat))
  | .pure a, _ => some [(.ok a, 0)]
  | .ub r, _ => some [(.ub r, 0)]
  | .noOutcome e, _ => some [(.noOutcome e, 0)]
  | .choose w k, budget =>
    if w ≤ budget then
      collect (fun b => ((k b).explore (budget - w)).map (List.map fun p => (p.1, p.2 + 1)))
        (allBits w) []
    else none

/-- Within its budget, exhaustive mode finds exactly the tree's set: each
way the tree may end is a leaf it lists, and each leaf it lists that has
an outcome is a way the tree may end. -/
theorem explore_toSet : ∀ {t : ChoiceTree ε α} {budget : Nat} {ls : List (Leaf ε α × Nat)},
    t.explore budget = some ls → ∀ e, t.toSet e ↔ ∃ p ∈ ls, p.1.ev? = some e
  | .pure a, _, ls, h, e => by
    cases h
    exact ⟨fun he => ⟨_, List.mem_singleton_self _, by rw [he]; rfl⟩,
      fun ⟨_, hp, he⟩ => by rw [List.mem_singleton.1 hp] at he; cases he; rfl⟩
  | .ub r, _, ls, h, e => by
    cases h
    exact ⟨fun he => ⟨_, List.mem_singleton_self _, by rw [he]; rfl⟩,
      fun ⟨_, hp, he⟩ => by rw [List.mem_singleton.1 hp] at he; cases he; rfl⟩
  | .noOutcome _, _, ls, h, e => by
    cases h
    exact ⟨False.elim, fun ⟨_, hp, he⟩ => by rw [List.mem_singleton.1 hp] at he; cases he⟩
  | .choose w k, budget, ls, h, e => by
    simp only [explore] at h
    split at h
    · constructor
      · rintro ⟨b, hb⟩
        obtain ⟨l, hl⟩ := collect_some h b (mem_allBits b)
        obtain ⟨lb, hlb, rfl⟩ := Option.map_eq_some_iff.1 hl
        obtain ⟨p, hp, hpeq⟩ := (explore_toSet hlb e).1 hb
        exact ⟨(p.1, p.2 + 1), (collect_mem h _).2 (.inr ⟨b, mem_allBits b, _, hl,
          List.mem_map.2 ⟨p, hp, rfl⟩⟩), hpeq⟩
      · rintro ⟨p, hp, hpeq⟩
        rcases (collect_mem h p).1 hp with hp | ⟨b, _, l, hl, hpl⟩
        · nomatch hp
        · obtain ⟨lb, hlb, rfl⟩ := Option.map_eq_some_iff.1 hl
          obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hpl
          exact ⟨b, (explore_toSet hlb e).2 ⟨q, hq, hpeq⟩⟩
    · cases h

/-- No path of the tree chooses more than `budget` bits in all. -/
def Within : ChoiceTree ε α → Nat → Prop
  | .choose w k, budget => w ≤ budget ∧ ∀ b, (k b).Within (budget - w)
  | _, _ => True

theorem collect_isSome {g : β → Option (List γ)} :
    ∀ {bs : List β} {acc : List γ}, (collect g bs acc).isSome ↔ ∀ b ∈ bs, (g b).isSome
  | [], _ => by simp [collect]
  | b :: bs, acc => by
    simp only [collect]
    split
    · rename_i l hl
      rw [collect_isSome]
      simp [hl]
    · rename_i hl
      simp [hl]

/-- Exhaustive mode gives a list exactly when no path of the tree chooses
more than its budget. -/
theorem explore_isSome_iff : ∀ {t : ChoiceTree ε α} {budget : Nat},
    (t.explore budget).isSome ↔ t.Within budget
  | .pure _, _ | .ub _, _ | .noOutcome _, _ => by simp [explore, Within]
  | .choose w k, budget => by
    simp only [explore, Within]
    split
    · rename_i hw
      rw [collect_isSome]
      simp only [Option.isSome_map]
      constructor
      · intro h
        exact ⟨hw, fun b => explore_isSome_iff.1 (h b (mem_allBits b))⟩
      · intro ⟨_, h⟩ b _
        exact explore_isSome_iff.2 (h b)
    · rename_i hw
      simp [hw]

/-- Why a choice sequence does not fit a run. Choices are counted from
zero. -/
inductive Misfit (σ : Type) where
  /-- The run makes choice `made`, of `w` bits, and the sequence has no
  more values. -/
  | short (made w : Nat)
  /-- The value `s` that the sequence gives for choice `made` does not read
  as `w` bits. -/
  | unread (made w : Nat) (s : σ)
  /-- The run makes `made` choices, and the sequence has `length` values. -/
  | long (made length : Nat)

/-- Scripted mode: the leaf that the choice sequence `cs` leads to, and how
many choices its path makes, after `made` choices already made. `read w s`
reads the value `s` as `w` bits. A path with no outcome ends the walk,
whatever is left of the sequence; any other leaf must use all of it. -/
def script (read : (w : Nat) → σ → Option (BitVec w)) :
    ChoiceTree ε α → List σ → Nat → Except (Misfit σ) (Leaf ε α × Nat)
  | .noOutcome e, _, made => .ok (.noOutcome e, made)
  | .pure a, [], made => .ok (.ok a, made)
  | .ub r, [], made => .ok (.ub r, made)
  | .pure _, cs@(_ :: _), made | .ub _, cs@(_ :: _), made => .error (.long made (made + cs.length))
  | .choose w _, [], made => .error (.short made w)
  | .choose w k, s :: cs, made => match read w s with
    | some b => (k b).script read cs (made + 1)
    | none => .error (.unread made w s)

/-- On a choice sequence that fits, scripted mode ends with a way the tree
may end. -/
theorem script_toSet {read : (w : Nat) → σ → Option (BitVec w)} :
    ∀ {t : ChoiceTree ε α} {cs : List σ} {made : Nat} {l : Leaf ε α} {c : Nat} {e : Ev α},
      t.script read cs made = .ok (l, c) → l.ev? = some e → t.toSet e
  | .noOutcome _, _, _, _, _, _, h, he => by cases h; cases he
  | .pure _, [], _, _, _, _, h, he => by cases h; cases he; rfl
  | .ub _, [], _, _, _, _, h, he => by cases h; cases he; rfl
  | .pure _, _ :: _, _, _, _, _, h, _ | .ub _, _ :: _, _, _, _, _, h, _
  | .choose _ _, [], _, _, _, _, h, _ => by cases h
  | .choose w k, s :: cs, made, l, c, e, h, he => by
    simp only [script] at h
    split at h
    · rename_i b _
      exact ⟨b, script_toSet h he⟩
    · cases h

/-- A value that a path chose, with its width. -/
abbrev Chosen := (w : Nat) × BitVec w

/-- Reads a chosen value as `w` bits: it reads when its width is `w`. -/
def readChosen (w : Nat) : Chosen → Option (BitVec w)
  | ⟨v, b⟩ => if h : v = w then some (h ▸ b) else none

/-- Sampled mode: the leaf of the path on which `draw` gives each choice,
starting from the generator `g`, and the values chosen on it, in order.
`draw w g` gives `w` bits and the generator's next state. -/
def sample (draw : (w : Nat) → γ → BitVec w × γ) : ChoiceTree ε α → γ → Leaf ε α × List Chosen
  | .pure a, _ => (.ok a, [])
  | .ub r, _ => (.ub r, [])
  | .noOutcome e, _ => (.noOutcome e, [])
  | .choose w k, g =>
    let d := draw w g
    let p := (k d.1).sample draw d.2
    (p.1, ⟨w, d.1⟩ :: p.2)

/-- The values that sampled mode chose are a choice sequence that fits the
tree: scripted mode on them reaches the same leaf, after as many choices as
there are values. -/
theorem sample_script {draw : (w : Nat) → γ → BitVec w × γ} :
    ∀ (t : ChoiceTree ε α) (g : γ) (made : Nat),
      t.script readChosen (t.sample draw g).2 made =
        .ok ((t.sample draw g).1, made + (t.sample draw g).2.length)
  | .pure _, _, _ | .ub _, _, _ | .noOutcome _, _, _ => rfl
  | .choose w k, g, made => by
    simp only [sample, script, readChosen, dite_true, List.length_cons]
    rw [sample_script (k (draw w g).1) (draw w g).2 (made + 1), Nat.add_assoc, Nat.add_comm 1]

end ChoiceTree

/-!
# A run's paths

A run of the interpreter computes in `ExceptT Stuck m`, so a leaf of its
tree holds a result, or says that the path is stuck. `fir-ref` reports
each path as one of the run's outcomes, as stuck, or as ending with no
outcome.
-/

/-- How one path of a run ends: with an outcome, stuck, or with no
outcome, for the reason `e`. -/
inductive PathEnd (O ε : Type) where
  | outcome (o : Outcome O)
  | stuck (st : Stuck)
  | noOutcome (e : ε)

open ChoiceTree in
/-- How the path of a run that ends at this leaf ends. -/
def ChoiceTree.Leaf.pathEnd {O ε : Type} : Leaf ε (Except Stuck (Result O)) → PathEnd O ε
  | .ok (.ok (.ret o)) => .outcome (.ret o)
  | .ok (.ok .fuelExhausted) => .outcome .fuelExhausted
  | .ok (.error st) => .stuck st
  | .ub r => .outcome (.ub r)
  | .noOutcome e => .noOutcome e

/-- The way a run's computation ends when it has the outcome `o`. -/
def Outcome.ev {O : Type} : Outcome O → Ev (Except Stuck (Result O))
  | .ret o => .ok (.ok (.ret o))
  | .ub r => .ub r
  | .fuelExhausted => .ok (.ok .fuelExhausted)

theorem Run.outcomes_iff {O : Type} (s : Run O) (o : Outcome O) : s.outcomes o ↔ s o.ev := by
  cases o <;> rfl

theorem ChoiceTree.Leaf.ev?_eq_outcome {O ε : Type} (l : Leaf ε (Except Stuck (Result O)))
    (o : Outcome O) : l.ev? = some o.ev ↔ l.pathEnd = .outcome o := by
  rcases l with ((_ | (_ | _)) | _ | _) <;> cases o <;> simp [ev?, pathEnd, Outcome.ev]

theorem ChoiceTree.Leaf.ev?_eq_stuck {O ε : Type} (l : Leaf ε (Except Stuck (Result O))) :
    (∃ st, l.ev? = some (.ok (.error st))) ↔ ∃ st, l.pathEnd = .stuck st := by
  rcases l with ((_ | (_ | _)) | _ | _) <;> simp [ev?, pathEnd]

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] {ε : Type}
  [DialectDenote d (ChoiceTree ε)] [DialectDenote d SetM]

/-- The run of a function in the tree of choices denotes its run in the set
monad, when the tree's semantics of each op denotes the set monad's. -/
theorem Func.run_toSet (h : (ChoiceTree.toSetMorphism (ε := ε)).MapsDenote (d := d)) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) :
    (f.run (m := ChoiceTree ε) args fuel).run.toSet = f.run (m := SetM) args fuel :=
  congrArg ExceptT.run (Func.run_map h f args fuel)

/-- Exhaustive mode, within its choice budget, gives exactly the outcomes of
the run at the fuel budget it runs with. -/
theorem Func.explore_outcomes (h : (ChoiceTree.toSetMorphism (ε := ε)).MapsDenote (d := d))
    (f : Func d) (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat)
    {ls : List (ChoiceTree.Leaf ε (Except Stuck (Result (List (DVal d)))) × Nat)}
    (hx : (f.run (m := ChoiceTree ε) args fuel).run.explore budget = some ls)
    (o : Outcome (List (DVal d))) :
    Run.outcomes (f.run (m := SetM) args fuel) o ↔ ∃ p ∈ ls, p.1.pathEnd = .outcome o := by
  rw [Run.outcomes_iff, ← Func.run_toSet h, ChoiceTree.explore_toSet hx]
  simp only [ChoiceTree.Leaf.ev?_eq_outcome]

/-- Exhaustive mode, within its choice budget, finds a stuck path exactly
when the run has one. -/
theorem Func.explore_stuck (h : (ChoiceTree.toSetMorphism (ε := ε)).MapsDenote (d := d))
    (f : Func d) (args : HVector toType (f.params.map (·.2))) (fuel budget : Nat)
    {ls : List (ChoiceTree.Leaf ε (Except Stuck (Result (List (DVal d)))) × Nat)}
    (hx : (f.run (m := ChoiceTree ε) args fuel).run.explore budget = some ls) :
    Run.IsStuck (f.run (m := SetM) args fuel) ↔ ∃ p ∈ ls, ∃ st, p.1.pathEnd = .stuck st := by
  simp only [Run.IsStuck, ← Func.run_toSet h, ChoiceTree.explore_toSet hx]
  constructor
  · rintro ⟨st, p, hp, he⟩
    exact ⟨p, hp, (ChoiceTree.Leaf.ev?_eq_stuck p.1).1 ⟨st, he⟩⟩
  · rintro ⟨p, hp, hs⟩
    obtain ⟨st, he⟩ := (ChoiceTree.Leaf.ev?_eq_stuck p.1).2 hs
    exact ⟨st, p, hp, he⟩

/-- Scripted mode, on a choice sequence that fits, gives an outcome of the
run at the fuel budget it runs with. -/
theorem Func.script_outcomes (h : (ChoiceTree.toSetMorphism (ε := ε)).MapsDenote (d := d))
    {σ : Type} (read : (w : Nat) → σ → Option (BitVec w)) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (cs : List σ)
    {l : ChoiceTree.Leaf ε (Except Stuck (Result (List (DVal d))))} {c : Nat}
    (hs : (f.run (m := ChoiceTree ε) args fuel).run.script read cs 0 = .ok (l, c))
    {o : Outcome (List (DVal d))} (ho : l.pathEnd = .outcome o) :
    Run.outcomes (f.run (m := SetM) args fuel) o := by
  rw [Run.outcomes_iff, ← Func.run_toSet h]
  exact ChoiceTree.script_toSet hs ((ChoiceTree.Leaf.ev?_eq_outcome l o).2 ho)

/-- Scripted mode, on a choice sequence that fits, finds a stuck path only
when the run has one. -/
theorem Func.script_stuck (h : (ChoiceTree.toSetMorphism (ε := ε)).MapsDenote (d := d))
    {σ : Type} (read : (w : Nat) → σ → Option (BitVec w)) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (cs : List σ)
    {l : ChoiceTree.Leaf ε (Except Stuck (Result (List (DVal d))))} {c : Nat}
    (hs : (f.run (m := ChoiceTree ε) args fuel).run.script read cs 0 = .ok (l, c))
    {st : Stuck} (hst : l.pathEnd = .stuck st) :
    Run.IsStuck (f.run (m := SetM) args fuel) := by
  obtain ⟨st', he⟩ := (ChoiceTree.Leaf.ev?_eq_stuck l).2 ⟨st, hst⟩
  exact ⟨st', by rw [← Func.run_toSet h]; exact ChoiceTree.script_toSet hs he⟩

end Fir
