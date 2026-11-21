import Fir.Execution.TraceMoveSel
import Fir.Execution.TraceChain

/-!
# The target's branch of moves

A configuration whose run shows a stream at unboundedly many budgets goes on by
a move to one that does too (`TGood.move`). Taking such moves one after the
other gives a _branch_ of the target (`TGood.branch`): configurations, each
going on by a move to the next, each showing the stream after the acts of the
moves before it, with deadlines less their steps.

The branch shows all of the stream (`TBranchT.exhaustive`). Were it to show
fewer than `k` acts, the deadline of the next act would fall by each move's
steps and never below them, so the moves would show finitely many steps in
all. From some move on, each would show none, and so enter a callee whose
entry block starts with a call, forever: the ops would start an endless chain
of calls, whose paths show nothing (`Func.traceOps_silent`), though the run
shows an act within its deadline.

So each configuration of the branch shows the stream after the moves before
it, at every budget, with the deadlines of its moves (`TBranchT.tShows`,
`TBranch.tShows`). The proof of divergence across a black box needs this of
the configuration that enters the black box's callee.
-/

namespace Fir

open Memory

/-- A sequence with a first element and a way to go on from each element at
each place: each element meets `P` at its place and goes on to the next by `R`.
This is dependent choice, by the axiom of choice. -/
theorem exists_seq_of_step {α : Type} {P : Nat → α → Prop} {R : Nat → α → α → Prop} {a₀ : α}
    (h₀ : P 0 a₀) (h : ∀ i a, P i a → ∃ b, P (i + 1) b ∧ R i a b) :
    ∃ s : Nat → α, s 0 = a₀ ∧ ∀ i, P i (s i) ∧ R i (s i) (s (i + 1)) := by
  classical
  let next : Nat → α → α := fun i a => if hp : P i a then Classical.choose (h i a hp) else a
  let s : Nat → α := fun i => Nat.rec a₀ (fun i a => next i a) i
  have hs : ∀ i, P i (s i) := by
    intro i
    induction i with
    | zero => exact h₀
    | succ i ih =>
      show P (i + 1) (next i (s i))
      simp only [next, dite_eq_left ih]
      exact (Classical.choose_spec (h i _ ih)).1
  refine ⟨s, rfl, fun i => ⟨hs i, ?_⟩⟩
  show R i (s i) (next i (s i))
  simp only [next, dite_eq_left (hs i)]
  exact (Classical.choose_spec (h i _ (hs i))).2

variable {A : Type}

/-- A stream that, once it has no act at a place, has none at any later
place. -/
def Stream.Closed (S : Nat → Option A) : Prop := ∀ i, (S (i + 1)).isSome → (S i).isSome

/-- A stream after some places is closed when the stream is. -/
theorem Stream.Closed.drop {S : Nat → Option A} (h : Stream.Closed S) (a : Nat) :
    Stream.Closed (Stream.drop S a) := fun i hi => h (i + a) (by simpa [Stream.drop, Nat.add_right_comm] using hi)

/-- A closed stream with an act at a place has acts at every earlier place. -/
theorem Stream.Closed.avail {S : Nat → Option A} (h : Stream.Closed S) {p : Nat} {a : A}
    (hp : S p = some a) : Stream.Avail S (p + 1) := by
  have : ∀ q i, i + q = p → (S i).isSome := fun q => by
    induction q with
    | zero => intro i hi; rw [Nat.add_zero] at hi; rw [hi, hp]; rfl
    | succ q ih => intro i hi; exact h i (ih (i + 1) (by omega))
  exact fun i hi => this (p - i) i (by omega)

/-- A trace that shows a stream's first acts, then a trace that shows acts of
the stream after them, shows acts of the stream. -/
theorem Stream.Cons.append {S : Nat → Option A} {l m : List A} (hl : Stream.Cons S l)
    (hm : Stream.Cons (Stream.drop S l.length) m) : Stream.Cons S (l ++ m) := fun i a ha => by
  by_cases hi : i < l.length
  · rw [List.getElem?_append_left hi] at ha
    exact hl i a ha
  · rw [List.getElem?_append_right (by omega)] at ha
    have := hm _ _ ha
    simp only [Stream.drop] at this
    rwa [Nat.sub_add_cancel (by omega)] at this

/-- The moves of a branch, one more at the end. -/
theorem TBranch.pre_succ (t : Nat → List (Step A)) :
    ∀ i j, TBranch.pre t i (j + 1) = TBranch.pre t i j ++ t (i + j)
  | i, 0 => by simp [TBranch.pre]
  | i, j + 1 => by
    rw [TBranch.pre, TBranch.pre_succ t (i + 1) j, TBranch.pre, List.append_assoc,
      Nat.add_right_comm, Nat.add_assoc]

/-- A list of ops each of whose callees' entry blocks starts with a call of
the next starts no chain of calls. -/
theorem Module.not_callChain_of_seq {d : Dialect} [TyDenote d.Ty] [DialectSignature d]
    [DialectCall d] {M : Module d} {os : Nat → List (Operation d)}
    (h : ∀ l, M.callHead? (os l) = some (os (l + 1))) : ∀ c i, ¬ M.CallChain (os i) c := by
  intro c
  induction c with
  | zero =>
    intro i hc
    cases hc with
    | stop hn => rw [h i] at hn; cases hn
  | succ c ih =>
    intro i hc
    cases hc with
    | call hs hc =>
      rw [h i] at hs
      cases hs
      exact ih (i + 1) hc

variable {E Ans : Type} {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]
  {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (TraceM (Step (Act E Ans)) (TraceState Mem unit))] {M : Module d}

/-- A branch of the target: configurations `c`, each going on by the move of
the marked trace `t i` and the fuel `F i` to the next, each showing the stream
`T i` with the deadlines `K i` at unboundedly many budgets, the next stream and
deadlines being those after the move, which shows the stream's first acts, and
each deadline after them at least its steps. -/
structure TBranchT (M : Module d) (c : Nat → TCfg d Mem unit) (t : Nat → List (Step (Act E Ans)))
    (F : Nat → Nat) (T : Nat → Nat → Option (Act E Ans)) (K : Nat → Nat → Nat) : Prop where
  move : ∀ i, TCfg.Move (Act E Ans) M (c i) (c (i + 1)) (t i) (F i)
  good : ∀ i, TGood ((c i).exh (Act E Ans) M) (T i) (K i)
  stream : ∀ i, T (i + 1) = Stream.drop (T i) (Step.actsOf (t i)).length
  deadline : ∀ i, K (i + 1) = Stream.dropK (K i) (Step.actsOf (t i)).length (Step.ticks (t i))
  cons : ∀ i, Stream.Cons (T i) (Step.actsOf (t i))
  steps : ∀ i x, Stream.Avail (T i) (x + (Step.actsOf (t i)).length) →
    K i (x + (Step.actsOf (t i)).length) < Step.ticks (t i) → x = 0

/-- A configuration whose run shows a stream at unboundedly many budgets
starts a branch of the target. -/
theorem TGood.branch (hone : OpsOneStep d (Act E Ans) (TraceState Mem unit))
    (hfin : OpsStepFinite d E Ans (TraceState Mem unit)) {c₀ : TCfg d Mem unit}
    {T₀ : Nat → Option (Act E Ans)} {K₀ : Nat → Nat} (h : TGood (c₀.exh (Act E Ans) M) T₀ K₀) :
    ∃ c t F T K, c 0 = c₀ ∧ T 0 = T₀ ∧ K 0 = K₀ ∧ TBranchT M c t F T K := by
  obtain ⟨s, hs₀, hs⟩ := exists_seq_of_step
    (α := TCfg d Mem unit × (Nat → Option (Act E Ans)) × (Nat → Nat) × List (Step (Act E Ans)) × Nat)
    (a₀ := (c₀, T₀, K₀, [], 0))
    (P := fun _ a => TGood (a.1.exh (Act E Ans) M) a.2.1 a.2.2.1)
    (R := fun _ a b => TCfg.Move (Act E Ans) M a.1 b.1 b.2.2.2.1 b.2.2.2.2 ∧
      b.2.1 = Stream.drop a.2.1 (Step.actsOf b.2.2.2.1).length ∧
      b.2.2.1 = Stream.dropK a.2.2.1 (Step.actsOf b.2.2.2.1).length (Step.ticks b.2.2.2.1) ∧
      Stream.Cons a.2.1 (Step.actsOf b.2.2.2.1) ∧
      ∀ x, Stream.Avail a.2.1 (x + (Step.actsOf b.2.2.2.1).length) →
        a.2.2.1 (x + (Step.actsOf b.2.2.2.1).length) < Step.ticks b.2.2.2.1 → x = 0)
    h fun _ a ha => by
      obtain ⟨c₁, t, F, hmv, hg, hc, hst⟩ := TGood.move hone hfin ha
      exact ⟨(c₁, _, _, t, F), hg, hmv, rfl, rfl, hc, hst⟩
  refine ⟨fun i => (s i).1, fun i => (s (i + 1)).2.2.2.1, fun i => (s (i + 1)).2.2.2.2,
    fun i => (s i).2.1, fun i => (s i).2.2.1, by simp only [hs₀], by simp only [hs₀],
    by simp only [hs₀], ?_⟩
  exact ⟨fun i => (hs i).2.1, fun i => (hs i).1, fun i => (hs i).2.2.1, fun i => (hs i).2.2.2.1,
    fun i => (hs i).2.2.2.2.1, fun i => (hs i).2.2.2.2.2⟩

namespace TBranchT

variable {c : Nat → TCfg d Mem unit} {t : Nat → List (Step (Act E Ans))} {F : Nat → Nat}
  {T : Nat → Nat → Option (Act E Ans)} {K : Nat → Nat → Nat}

/-- The stream of a configuration of the branch is the first one's after the
acts of the moves before it. -/
theorem stream_eq (hb : TBranchT M c t F T K) (i : Nat) :
    ∀ j, T (i + j) = Stream.drop (T i) (Step.actsOf (TBranch.pre t i j)).length
  | 0 => by funext x; simp [Stream.drop, TBranch.pre, Step.actsOf]
  | j + 1 => by
    rw [← Nat.add_assoc, hb.stream, stream_eq hb i j, TBranch.pre_succ]
    funext x
    simp only [Stream.drop, Step.actsOf, List.flatMap_append, List.length_append]
    rw [Nat.add_assoc, Nat.add_comm (List.flatMap _ (t (i + j))).length]

/-- The moves of the branch from a configuration show acts of its stream. -/
theorem cons_pre (hb : TBranchT M c t F T K) :
    ∀ j i, Stream.Cons (T i) (Step.actsOf (TBranch.pre t i j))
  | 0, _ => fun _ _ h => by simp [TBranch.pre, Step.actsOf] at h
  | j + 1, i => by
    have e : Step.actsOf (TBranch.pre t i (j + 1)) =
        Step.actsOf (t i) ++ Step.actsOf (TBranch.pre t (i + 1) j) := by
      simp [TBranch.pre, Step.actsOf]
    rw [e]
    exact (hb.cons i).append (hb.stream i ▸ cons_pre hb j (i + 1))

/-- The moves of the branch show all of the stream: each act of a
configuration's stream is shown by some moves from it. -/
theorem exhaustive (hone : OpsOneStep d (Act E Ans) (TraceState Mem unit))
    (hb : TBranchT M c t F T K) (i : Nat) {p : Nat} (hp : Stream.Avail (T i) (p + 1)) :
    ∃ j, p < (Step.actsOf (TBranch.pre t i j)).length := by
  refine Classical.byContradiction fun hno => ?_
  have hA : ∀ j, (Step.actsOf (TBranch.pre t i j)).length ≤ p := fun j =>
    Nat.le_of_not_lt fun hlt => hno ⟨j, hlt⟩
  have hAsucc : ∀ j, (Step.actsOf (TBranch.pre t i (j + 1))).length =
      (Step.actsOf (TBranch.pre t i j)).length + (Step.actsOf (t (i + j))).length := fun j => by
    rw [TBranch.pre_succ]
    simp [Step.actsOf]
  have hJsucc : ∀ j, Step.ticks (TBranch.pre t i (j + 1)) =
      Step.ticks (TBranch.pre t i j) + Step.ticks (t (i + j)) := fun j => by
    rw [TBranch.pre_succ, Step.ticks_append]
  -- The deadline of the next act falls by each move's steps, never below them.
  have hdl : ∀ j, Step.ticks (TBranch.pre t i j) ≤ K i (p + 1) ∧
      K (i + j) (p + 1 - (Step.actsOf (TBranch.pre t i j)).length) =
        K i (p + 1) - Step.ticks (TBranch.pre t i j) := by
    intro j
    induction j with
    | zero => simp [TBranch.pre, Step.ticks, Step.actsOf]
    | succ j ih =>
      have ha := hA (j + 1)
      rw [hAsucc] at ha ⊢
      rw [hJsucc, ← Nat.add_assoc, hb.deadline]
      simp only [Stream.dropK]
      have hx : p + 1 - ((Step.actsOf (TBranch.pre t i j)).length +
          (Step.actsOf (t (i + j))).length) + (Step.actsOf (t (i + j))).length =
          p + 1 - (Step.actsOf (TBranch.pre t i j)).length := by omega
      rw [hx, ih.2]
      have havail : Stream.Avail (T (i + j)) (p + 1 - ((Step.actsOf (TBranch.pre t i j)).length +
          (Step.actsOf (t (i + j))).length) + (Step.actsOf (t (i + j))).length) := by
        rw [hx, hb.stream_eq i j]
        intro q hq
        exact hp _ (by omega)
      have hnlt : ¬ K (i + j) (p + 1 - ((Step.actsOf (TBranch.pre t i j)).length +
          (Step.actsOf (t (i + j))).length) + (Step.actsOf (t (i + j))).length) <
          Step.ticks (t (i + j)) := fun hlt => by
        have := hb.steps (i + j) _ havail hlt
        omega
      rw [hx, ih.2] at hnlt
      constructor <;> omega
  -- So, from some move on, the moves show no step.
  have hev : ∃ j₀, ∀ j, j₀ ≤ j → Step.ticks (t (i + j)) = 0 := by
    refine Classical.byContradiction fun hne => ?_
    have hun : ∀ q, ∃ j, q ≤ Step.ticks (TBranch.pre t i j) := by
      intro q
      induction q with
      | zero => exact ⟨0, Nat.zero_le _⟩
      | succ q ih =>
        obtain ⟨j, hj⟩ := ih
        obtain ⟨j', hj'⟩ := Classical.not_forall.1 (fun h' => hne ⟨j, h'⟩)
        obtain ⟨hle, hpos⟩ : j ≤ j' ∧ Step.ticks (t (i + j')) ≠ 0 := by
          by_cases hle : j ≤ j'
          · exact ⟨hle, fun h0 => hj' fun _ => h0⟩
          · exact absurd (fun h => absurd h hle) hj'
        refine ⟨j' + 1, ?_⟩
        rw [hJsucc]
        obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hle
        have := (Step.actsOf_prefix (TBranch.pre_prefix t i j l)).length_le
        have hmono : Step.ticks (TBranch.pre t i j) ≤ Step.ticks (TBranch.pre t i (j + l)) := by
          obtain ⟨r, hr⟩ := TBranch.pre_prefix t i j l
          rw [← hr, Step.ticks_append]
          exact Nat.le_add_right _ _
        omega
    obtain ⟨j, hj⟩ := hun (K i (p + 1) + 1)
    have := (hdl j).1
    omega
  obtain ⟨j₀, hj₀⟩ := hev
  -- Those moves enter callees forever: an endless chain of calls, which shows nothing.
  have hchain : ∀ c', ¬ M.CallChain (c (i + j₀)).os c' :=
    fun c' => Module.not_callChain_of_seq (os := fun l => (c (i + j₀ + l)).os)
      (fun l => (hb.move (i + j₀ + l)).callHead hone (by rw [Nat.add_assoc]; exact hj₀ _ (by omega)))
      c' 0
  have hk : 0 < p + 1 - (Step.actsOf (TBranch.pre t i j₀)).length := by have := hA j₀; omega
  obtain ⟨n, -, mt, ⟨s₁, hx⟩, -, hsee⟩ := hb.good (i + j₀) (p + 1 - (Step.actsOf (TBranch.pre t i j₀)).length) 0
  obtain ⟨s', hs'⟩ := Func.traceOps_silent n _ _ _ _ hchain _ hx (TraceEnd.notStuck_ok _ _ _)
  simp only [Except.ok.injEq, Prod.mk.injEq] at hs'
  obtain ⟨-, rfl, -⟩ := hs'
  have havail : Stream.Avail (T (i + j₀)) (p + 1 - (Step.actsOf (TBranch.pre t i j₀)).length) := by
    rw [hb.stream_eq i j₀]
    intro q hq
    exact hp _ (by omega)
  have := hsee _ (Nat.le_refl _) havail
  have h0 : Step.actsOf (Step.upTo (K (i + j₀) (p + 1 - (Step.actsOf (TBranch.pre t i j₀)).length))
      ([] : List (Step (Act E Ans)))) = [] := by simp [Step.upTo, Step.actsOf]
  rw [h0] at this
  simp only [List.length_nil] at this
  omega

/-- The acts of the moves of the branch from a configuration, its stream
closed, are its stream. -/
theorem acts_eq (hone : OpsOneStep d (Act E Ans) (TraceState Mem unit))
    (hb : TBranchT M c t F T K) (i : Nat) (hcl : Stream.Closed (T i)) : TBranch.acts t i = T i := by
  funext p
  cases hp : T i p with
  | none =>
    cases ha : TBranch.acts t i p with
    | none => rfl
    | some a =>
      obtain ⟨j, hj⟩ := TBranch.acts_some ha
      rw [hb.cons_pre j i p a hj] at hp
      cases hp
  | some a =>
    obtain ⟨j, hj⟩ := hb.exhaustive hone i (hcl.avail hp)
    obtain ⟨b, hb'⟩ : ∃ b, (Step.actsOf (TBranch.pre t i j))[p]? = some b :=
      ⟨_, List.getElem?_eq_getElem hj⟩
    rw [TBranch.acts_eq hb', ← hb.cons_pre j i p b hb', hp]

/-- Each configuration of the branch, its stream closed, shows its stream at
every budget, with the deadlines of the moves from it. -/
theorem tShows (hone : OpsOneStep d (Act E Ans) (TraceState Mem unit))
    (hb : TBranchT M c t F T K) (i : Nat) (hcl : Stream.Closed (T i)) :
    TShows ((c i).exh (Act E Ans) M) (T i) (TBranch.deadline t F i) := by
  have h := TBranch.tShows (fun i => (hb.move i).tStep hone) i
  rwa [hb.acts_eq hone i hcl] at h

end TBranchT

end Fir
