import Fir

/-!
The allocations that an observer reaches at the end of a return
(`docs/decisions/fir-ref-run-end.md#reachable-memory`): `fir-ref run`
reports each of them, so that what it reports is what the spec's end of a
return compares (`End.Reachable`). The roots are the escaped allocations, in
the order they escaped, then the allocations that the returned pointers
point into, in the order of the values; from each live allocation reached,
the allocations that its units point into, in the order of its units. A
dangling pointer, into a freed allocation, reaches nothing; an allocation
that the memory never made is reached, and has no block.

`FirRef.reachWalk` visits them depth first, each once, in a loop of tail calls
with a work list and the list of the allocations seen, so it takes no stack
per allocation, per pointer or per unit. It counts its steps: each pops an
entry of the work list, and the entries it pushes are the roots and the
pointers of the units of the allocations it sees, each seen once, so
`endReachFuel` steps, the roots and every unit of every memory, are enough.
That bound is argued here, not proved: a walk that runs out of steps gives
`none`, and `fir-ref` reports it as an error, never as a result.
`reach_iff` proves that when the walk ends, it lists exactly the
allocations of `End.Reachable`.
-/

namespace FirRef

open Fir Memory

section Walk

variable {α : Type} [DecidableEq α] (succs : α → List α)

/-- A walk of the graph whose edges go from `x` to each of `succs x`, from
the entries of `work`, after the nodes `seen`, the last seen first, with at
most `n` steps: the nodes seen, in the order they were first seen, or
`none` when it runs out of steps. -/
def reachWalk : Nat → List α → List α → Option (List α)
  | _, [], seen => some seen.reverse
  | 0, _ :: _, _ => none
  | n + 1, x :: work, seen =>
    if x ∈ seen then reachWalk n work seen else reachWalk n (succs x ++ work) (x :: seen)

/-- Each node that a walk lists holds of a property that holds of the nodes
seen and of the work list, and of the successors of each node it holds
of. -/
theorem reachWalk_sound (P : α → Prop) (hP : ∀ y, P y → ∀ z ∈ succs y, P z) :
    ∀ (n : Nat) (work seen : List α) (L : List α), reachWalk succs n work seen = some L →
      (∀ y ∈ work, P y) → (∀ y ∈ seen, P y) → ∀ y ∈ L, P y
  | _, [], seen, L, h, _, hs => by
    simp only [reachWalk, Option.some.injEq] at h
    subst h
    exact fun y hy => hs y (List.mem_reverse.1 hy)
  | 0, _ :: _, _, _, h, _, _ => by simp [reachWalk] at h
  | n + 1, x :: work, seen, L, h, hw, hs => by
    simp only [reachWalk] at h
    split at h
    · exact reachWalk_sound P hP n work seen L h (fun y hy => hw y (.tail _ hy)) hs
    · refine reachWalk_sound P hP n _ _ L h (fun y hy => ?_) (fun y hy => ?_)
      · rcases List.mem_append.1 hy with hy | hy
        · exact hP x (hw x (.head _)) y hy
        · exact hw y (.tail _ hy)
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact hw y (.head _)
        · exact hs y hy

/-- A walk that ends lists every node seen and every entry of its work
list, and the successors of each node it lists, when each successor of a
node seen is seen or on the work list. -/
theorem reachWalk_closed : ∀ (n : Nat) (work seen : List α) (L : List α),
    reachWalk succs n work seen = some L →
      (∀ y ∈ seen, ∀ z ∈ succs y, z ∈ seen ∨ z ∈ work) →
      (∀ y, y ∈ seen ∨ y ∈ work → y ∈ L) ∧ ∀ y ∈ L, ∀ z ∈ succs y, z ∈ L
  | _, [], seen, L, h, hinv => by
    simp only [reachWalk, Option.some.injEq] at h
    subst h
    refine ⟨fun y hy => ?_, fun y hy z hz => ?_⟩
    · rcases hy with hy | hy
      · exact List.mem_reverse.2 hy
      · cases hy
    · rcases hinv y (List.mem_reverse.1 hy) z hz with h | h
      · exact List.mem_reverse.2 h
      · cases h
  | 0, _ :: _, _, _, h, _ => by simp [reachWalk] at h
  | n + 1, x :: work, seen, L, h, hinv => by
    simp only [reachWalk] at h
    split at h
    · rename_i hx
      obtain ⟨hin, hcl⟩ := reachWalk_closed n work seen L h fun y hy z hz => by
        rcases hinv y hy z hz with h | h
        · exact .inl h
        · rcases List.mem_cons.1 h with rfl | h
          · exact .inl hx
          · exact .inr h
      refine ⟨fun y hy => ?_, hcl⟩
      rcases hy with hy | hy
      · exact hin y (.inl hy)
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact hin y (.inl hx)
        · exact hin y (.inr hy)
    · obtain ⟨hin, hcl⟩ := reachWalk_closed n _ _ L h fun y hy z hz => by
        rcases List.mem_cons.1 hy with rfl | hy
        · exact .inr (List.mem_append.2 (.inl hz))
        · rcases hinv y hy z hz with h | h
          · exact .inl (.tail _ h)
          · rcases List.mem_cons.1 h with rfl | h
            · exact .inl (.head _)
            · exact .inr (List.mem_append.2 (.inr h))
      refine ⟨fun y hy => ?_, hcl⟩
      rcases hy with hy | hy
      · exact hin y (.inl (.tail _ hy))
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact hin y (.inl (.head _))
        · exact hin y (.inr (List.mem_append.2 (.inr hy)))

end Walk

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem] {μ : Nat → Mem} {ar : AddrRule}
  {V : Type} [HRefinement V V] [HasPtrs V]

/-- The allocation that the pointer `p` of the memory numbered `n` points
into, as an observer reaches it from the memories `S`: none when it has no
provenance or is dangling. -/
def reachOf (μ : Nat → Mem) (S : Memories Mem unit) (np : Nat × Pointer) :
    Option (Mem × AllocId) :=
  match np.2.prov with
  | some c => if S.freed (μ np.1) c then none else some (μ np.1, c)
  | none => none

/-- The roots of the end of a return: the escaped allocations, in the order
they escaped, then the allocations that the returned pointers point into,
unless dangling. -/
def endRoots (s : End unit μ ar V) : List (Mem × AllocId) :=
  s.escaped ++ (HasPtrs.ptrs s.vals).filterMap (reachOf μ s.mem)

/-- The allocations that the units of a live allocation point into, unless
dangling, in the order of its units: none for a freed allocation or one
that the memory never made. -/
def endSuccs (s : End unit μ ar V) (xa : Mem × AllocId) : List (Mem × AllocId) :=
  match (s.mem.mem xa.1).blocks[xa.2]? with
  | some b => if b.live then (HasPtrs.ptrs b.units).filterMap (reachOf μ s.mem) else []
  | none => []

/-- The steps that the walk of the end of a return takes at most: one for
each root and each unit of each memory, and one more. -/
def endReachFuel (s : End unit μ ar V) : Nat :=
  (endRoots s).length +
    s.mem.table.foldl (fun n e => e.2.blocks.foldl (fun n b => n + b.units.length) n) 0 + 1

/-- The allocations that an observer reaches from the end of a return, in
the order the walk first reaches them, or `none` when the walk runs out of
steps. -/
def endReach (s : End unit μ ar V) : Option (List (Mem × AllocId)) :=
  reachWalk (endSuccs s) (endReachFuel s) (endRoots s) []

theorem mem_reachOf {S : Memories Mem unit} {np : Nat × Pointer} {xa : Mem × AllocId} :
    reachOf μ S np = some xa ↔ ∃ c, np.2.prov = some c ∧ S.freed (μ np.1) c = false ∧
      xa = (μ np.1, c) := by
  rcases np with ⟨n, p⟩
  rcases hp : p.prov with _ | c
  · simp [reachOf, hp]
  · by_cases hf : S.freed (μ n) c
    · simp [reachOf, hp, hf]
    · simp only [reachOf, hp, hf, Bool.false_eq_true, ite_false, Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨c, rfl, by simpa using hf, rfl⟩
      · rintro ⟨c', hc', _, rfl⟩; cases hc'; rfl

theorem reachable_of_mem_roots {s : End unit μ ar V} {xa : Mem × AllocId} (h : xa ∈ endRoots s) :
    s.Reachable xa.1 xa.2 := by
  rcases List.mem_append.1 h with h | h
  · exact .escaped h
  · obtain ⟨np, hnp, hr⟩ := List.mem_filterMap.1 h
    obtain ⟨c, hc, hf, rfl⟩ := mem_reachOf.1 hr
    exact .val hnp hc hf

theorem reachable_succs {s : End unit μ ar V} {xa : Mem × AllocId} (h : s.Reachable xa.1 xa.2)
    {z : Mem × AllocId} (hz : z ∈ endSuccs s xa) : s.Reachable z.1 z.2 := by
  unfold endSuccs at hz
  split at hz
  · rename_i b hb
    split at hz
    · rename_i hl
      obtain ⟨np, hnp, hr⟩ := List.mem_filterMap.1 hz
      obtain ⟨c, hc, hf, rfl⟩ := mem_reachOf.1 hr
      exact .unit h hb hl hnp hc hf
    · cases hz
  · cases hz

/-- When the walk of the end of a return ends, it lists exactly the
allocations that an observer reaches. -/
theorem reach_iff {s : End unit μ ar V} {L : List (Mem × AllocId)} (h : endReach s = some L)
    (x : Mem) (a : AllocId) : (x, a) ∈ L ↔ s.Reachable x a := by
  constructor
  · intro hm
    exact reachWalk_sound (endSuccs s) (fun xa => s.Reachable xa.1 xa.2)
      (fun _ hy _ hz => reachable_succs hy hz) _ _ _ L h
      (fun _ hy => reachable_of_mem_roots hy) (fun _ hy => nomatch hy) _ hm
  · intro hr
    obtain ⟨hin, hcl⟩ := reachWalk_closed (endSuccs s) _ _ _ L h (fun _ hy => nomatch hy)
    induction hr with
    | escaped he => exact hin _ (.inr (List.mem_append.2 (.inl he)))
    | val hp hpa hf =>
      exact hin _ (.inr (List.mem_append.2 (.inr (List.mem_filterMap.2
        ⟨_, hp, mem_reachOf.2 ⟨_, hpa, hf, rfl⟩⟩))))
    | unit _ hb hl hp hpa hf ih =>
      refine hcl _ ih _ ?_
      simp only [endSuccs, hb, hl, ite_true]
      exact List.mem_filterMap.2 ⟨_, hp, mem_reachOf.2 ⟨_, hpa, hf, rfl⟩⟩

end FirRef
