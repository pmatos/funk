import Fir.Execution.TraceWorld
import Fir.Execution.Observe

/-!
# What an external call lets escape

An external call hands its pointer arguments to code outside the module,
which can also read memory that escaped earlier. So the call lets escape
every live allocation that its pointer arguments reach, and every live
allocation that a unit of an escaped allocation points into, again and
again (the human's ruling of 2026-11-20 on #239). A pointer stored into
escaped memory is handed out too, as in LLVM's capture tracking.

The world names each escaped allocation by its handle, its place in the
list of escaped allocations, so the order in which a call lets them escape
is part of what it shows. That order comes from positions, never from
allocation ids, so that a source and a target that hold the same pointers
in the same places give the same allocations the same handles:

* first the pointer arguments, in the order of the arguments and of the
  pointers each holds;
* then, handle by handle from the first, the pointers that the units of
  each escaped live allocation hold, in the order of its units, each
  allocation that joins the list being scanned in its turn.

Only a live allocation escapes (`TraceState.escape`): a dangling pointer
is poison in the comparison of two runs, so it escapes nothing. An
allocation that already escaped keeps its handle. The memories do not
change.

The walk ends: each allocation that joins the list is a live allocation of
the memories' table that had not escaped, and the table is finite. The
result is exactly the closure: the escaped list it starts from is a prefix
of the one it gives, every allocation it adds is reachable from the
pointer arguments or from the allocations that had escaped, and every live
allocation so reachable has a handle.
-/

namespace Fir

open Memory

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem] (μ : Nat → Mem)

/-! # One pointer at a time -/

/-- The allocation `a` of the memory `x` is live in the traced state `s`. -/
def TraceState.Live (s : TraceState Mem unit) (x : Mem) (a : AllocId) : Prop :=
  ((s.mem.mem x).blocks[a]?.map (·.live)) = some true

instance TraceState.instDecidableLive (s : TraceState Mem unit) (x : Mem) (a : AllocId) :
    Decidable (s.Live x a) :=
  inferInstanceAs (Decidable (_ = _))

/-- The traced state after the pointer `q.2` of the memory numbered `q.1`
lets its allocation escape, where the memory numbered `n` is `μ n`: a
pointer without provenance lets nothing escape. -/
def TraceState.escapePtr (s : TraceState Mem unit) (q : Nat × Pointer) : TraceState Mem unit :=
  match q.2.prov with
  | some a => (s.escape (μ q.1) a).2
  | none => s

/-- The traced state after the pointers `qs`, in order, let their
allocations escape. -/
def TraceState.escapePtrs (s : TraceState Mem unit) (qs : List (Nat × Pointer)) :
    TraceState Mem unit :=
  qs.foldl (TraceState.escapePtr μ) s

/-- The pointers that the units of the allocation `a` of the memory `x`
hold, in the order of its units, each with the number of its memory: none
when it is not live. -/
def TraceState.ptrsIn (s : TraceState Mem unit) (x : Mem) (a : AllocId) : List (Nat × Pointer) :=
  match (s.mem.mem x).blocks[a]? with
  | some b => if b.live then b.units.flatMap MemUnit.ptrs else []
  | none => []

/-! # The allocations that may still escape -/

/-- Every allocation of the memories' table, by its memory and its id. -/
def Memory.Memories.allocs (S : Memories Mem unit) : List (Mem × AllocId) :=
  S.table.flatMap fun e => (List.range e.2.blocks.length).map (e.1, ·)

/-- Each allocation of a memory of a table is in the table's list of
allocations. -/
theorem Memory.Memories.mem_lookup_allocs {x : Mem} {a : AllocId} {b : Memory.Block (unit x)} :
    ∀ {T : List (Σ y : Mem, Memory.Memory (unit y))},
      (Memory.Memories.lookup x T).blocks[a]? = some b →
        (x, a) ∈ T.flatMap fun e => (List.range e.2.blocks.length).map (e.1, ·)
  | [], h => by simp [Memory.Memories.lookup, Memory.Memory.empty] at h
  | ⟨y, m⟩ :: t, h => by
    rw [List.flatMap_cons, List.mem_append]
    unfold Memory.Memories.lookup at h
    by_cases hy : y = x
    · subst hy
      simp only [↓reduceDIte] at h
      exact .inl (List.mem_map.2 ⟨a, List.mem_range.2 (List.getElem?_eq_some_iff.1 h).1, rfl⟩)
    · simp only [hy, ↓reduceDIte] at h
      exact .inr (Memory.Memories.mem_lookup_allocs h)

/-- Each allocation of a memory is in the table's list of allocations. -/
theorem Memory.Memories.mem_allocs {S : Memories Mem unit} {x : Mem} {a : AllocId}
    {b : Memory.Block (unit x)} (h : (S.mem x).blocks[a]? = some b) : (x, a) ∈ S.allocs :=
  Memory.Memories.mem_lookup_allocs h

/-- The number of allocations of the table that have not escaped: each
allocation that escapes lowers it. -/
def TraceState.unescaped (s : TraceState Mem unit) : Nat :=
  (s.mem.allocs.filter fun p => decide (p ∉ s.escaped)).length

/-- A filter keeps no more than a filter by a weaker test. -/
theorem List.filter_length_le_of_imp {α : Type} {P Q : α → Bool} :
    ∀ {l : List α}, (∀ y ∈ l, P y = true → Q y = true) → (l.filter P).length ≤ (l.filter Q).length
  | [], _ => Nat.le_refl _
  | y :: l, h => by
    have ih := List.filter_length_le_of_imp (l := l) fun z hz => h z (List.mem_cons_of_mem _ hz)
    have hy := h y List.mem_cons_self
    simp only [List.filter_cons]
    cases hP : P y <;> cases hQ : Q y <;> simp_all <;> omega

/-- A filter keeps fewer than a filter by a weaker test that keeps an element
the first drops. -/
theorem List.filter_length_lt_of_imp {α : Type} {P Q : α → Bool} {l : List α}
    (h : ∀ y ∈ l, P y = true → Q y = true) {z : α} (hz : z ∈ l) (hP : P z = false)
    (hQ : Q z = true) : (l.filter P).length < (l.filter Q).length := by
  induction l with
  | nil => cases hz
  | cons y l ih =>
    have hle := List.filter_length_le_of_imp (P := P) (Q := Q) (l := l) fun w hw => h w (List.mem_cons_of_mem _ hw)
    have hy := h y List.mem_cons_self
    simp only [List.filter_cons]
    rcases List.mem_cons.1 hz with rfl | hz
    · simp only [hP, hQ, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega
    · have := ih (fun w hw => h w (List.mem_cons_of_mem _ hw)) hz
      cases hPy : P y <;> cases hQy : Q y <;> simp_all <;> omega

/-- Letting an allocation escape keeps the memories, and either changes
nothing or adds a live allocation that had not escaped at the end of the
list. -/
theorem TraceState.escape_cases (s : TraceState Mem unit) (x : Mem) (a : AllocId) :
    (s.escape x a).2 = s ∨ (s.Live x a ∧ (x, a) ∉ s.escaped ∧
      (s.escape x a).2 = { s with escaped := s.escaped ++ [(x, a)] }) := by
  unfold TraceState.escape
  split
  · split
    · exact .inl rfl
    · rename_i h₁ _ h₂
      exact .inr ⟨h₁, fun hm => by simp [List.idxOf?_eq_none_iff.1 h₂] at hm, rfl⟩
  · exact .inl rfl

/-- Letting a pointer's allocation escape keeps the memories, and either
changes nothing or adds a live allocation that had not escaped at the end
of the list. -/
theorem TraceState.escapePtr_cases (s : TraceState Mem unit) (q : Nat × Pointer) :
    s.escapePtr μ q = s ∨ ∃ a, q.2.prov = some a ∧ s.Live (μ q.1) a ∧ (μ q.1, a) ∉ s.escaped ∧
      s.escapePtr μ q = { s with escaped := s.escaped ++ [(μ q.1, a)] } := by
  unfold TraceState.escapePtr
  split
  · rename_i a h
    rcases s.escape_cases (μ q.1) a with h' | ⟨hl, hn, h'⟩
    · exact .inl h'
    · exact .inr ⟨a, h, hl, hn, h'⟩
  · exact .inl rfl

/-- Letting a pointer's allocation escape keeps the memories. -/
theorem TraceState.escapePtr_mem (s : TraceState Mem unit) (q : Nat × Pointer) :
    (s.escapePtr μ q).mem = s.mem := by
  rcases s.escapePtr_cases μ q with h | ⟨_, _, _, _, h⟩ <;> rw [h]

/-- Letting the pointers' allocations escape keeps the memories. -/
theorem TraceState.escapePtrs_mem (qs : List (Nat × Pointer)) :
    ∀ s : TraceState Mem unit, (s.escapePtrs μ qs).mem = s.mem := by
  induction qs with
  | nil => intro s; rfl
  | cons q qs ih => intro s; exact (ih (s.escapePtr μ q)).trans (s.escapePtr_mem μ q)

/-- Letting a pointer's allocation escape keeps the escaped list as a
prefix. -/
theorem TraceState.escapePtr_prefix (s : TraceState Mem unit) (q : Nat × Pointer) :
    s.escaped <+: (s.escapePtr μ q).escaped := by
  rcases s.escapePtr_cases μ q with h | ⟨_, _, _, _, h⟩ <;> rw [h]
  · exact List.prefix_refl _
  · exact List.prefix_append _ _

/-- Letting the pointers' allocations escape keeps the escaped list as a
prefix. -/
theorem TraceState.escapePtrs_prefix (qs : List (Nat × Pointer)) :
    ∀ s : TraceState Mem unit, s.escaped <+: (s.escapePtrs μ qs).escaped := by
  induction qs with
  | nil => intro s; exact List.prefix_refl _
  | cons q qs ih => intro s; exact (s.escapePtr_prefix μ q).trans (ih (s.escapePtr μ q))

/-- Letting the pointers' allocations escape either changes nothing or lowers
the number of allocations that have not escaped. -/
theorem TraceState.escapePtrs_cases (qs : List (Nat × Pointer)) :
    ∀ s : TraceState Mem unit, s.escapePtrs μ qs = s ∨ (s.escapePtrs μ qs).unescaped < s.unescaped := by
  induction qs with
  | nil => intro s; exact .inl rfl
  | cons q qs ih =>
    intro s
    show (s.escapePtr μ q).escapePtrs μ qs = s ∨ ((s.escapePtr μ q).escapePtrs μ qs).unescaped < _
    rcases s.escapePtr_cases μ q with h | ⟨a, -, hl, hn, h⟩
    · rw [h]
      exact ih s
    · have hlt : (s.escapePtr μ q).unescaped < s.unescaped := by
        unfold TraceState.unescaped
        rw [h]
        obtain ⟨b, hb⟩ : ∃ b, (s.mem.mem (μ q.1)).blocks[a]? = some b := by
          unfold TraceState.Live at hl
          cases hb : (s.mem.mem (μ q.1)).blocks[a]? with
          | none => rw [hb] at hl; cases hl
          | some b => exact ⟨b, rfl⟩
        refine List.filter_length_lt_of_imp (z := (μ q.1, a)) (fun y _ hy => ?_) (Memories.mem_allocs hb)
          (by simp) (by simpa using hn)
        simp only [List.mem_append, decide_eq_true_eq, not_or] at hy ⊢
        exact hy.1
      rcases ih (s.escapePtr μ q) with h' | h'
      · rw [h']
        exact .inr hlt
      · exact .inr (Nat.lt_trans h' hlt)

/-! # The closure -/

/-- The walk over the escaped list from the handle `k`: each escaped
allocation, in the order of its handle, lets escape what its units point
into, each allocation that joins the list being walked in its turn. -/
def TraceState.reach (s : TraceState Mem unit) (k : Nat) : TraceState Mem unit :=
  if h : k < s.escaped.length then
    (s.escapePtrs μ (s.ptrsIn s.escaped[k].1 s.escaped[k].2)).reach (k + 1)
  else s
termination_by (s.unescaped, s.escaped.length - k)
decreasing_by
  rcases TraceState.escapePtrs_cases μ (s.ptrsIn s.escaped[k].1 s.escaped[k].2) s with h' | h'
  · rw [h']
    exact Prod.Lex.right _ (by omega)
  · exact Prod.Lex.left _ _ h'

/-- What an external call on arguments holding the pointers `qs` lets
escape from the traced state `s`: the pointers' allocations, in order, then
the walk over the escaped list from its first handle. -/
def TraceState.escapeCall (s : TraceState Mem unit) (qs : List (Nat × Pointer)) :
    TraceState Mem unit :=
  (s.escapePtrs μ qs).reach μ 0

/-- The walk keeps the memories and keeps the escaped list as a prefix. -/
theorem TraceState.reach_mem_prefix (s : TraceState Mem unit) (k : Nat) :
    (s.reach μ k).mem = s.mem ∧ s.escaped <+: (s.reach μ k).escaped := by
  induction s, k using TraceState.reach.induct μ with
  | case1 s k h ih =>
    rw [TraceState.reach]
    simp only [h, ↓reduceDIte]
    exact ⟨ih.1.trans (TraceState.escapePtrs_mem μ _ s),
      (TraceState.escapePtrs_prefix μ _ s).trans ih.2⟩
  | case2 s k h =>
    rw [TraceState.reach]
    simp [h]

/-- What an external call lets escape keeps the memories. -/
theorem TraceState.escapeCall_mem (s : TraceState Mem unit) (qs : List (Nat × Pointer)) :
    (s.escapeCall μ qs).mem = s.mem :=
  ((s.escapePtrs μ qs).reach_mem_prefix μ 0).1.trans (TraceState.escapePtrs_mem μ qs s)

/-- What an external call lets escape keeps the escaped list as a prefix:
an allocation that had escaped keeps its handle. -/
theorem TraceState.escapeCall_prefix (s : TraceState Mem unit) (qs : List (Nat × Pointer)) :
    s.escaped <+: (s.escapeCall μ qs).escaped :=
  (TraceState.escapePtrs_prefix μ qs s).trans ((s.escapePtrs μ qs).reach_mem_prefix μ 0).2

end Fir
