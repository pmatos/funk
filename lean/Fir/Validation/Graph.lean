import Fir.Validation.Dominance
import Fir.Validation.Search

/-!
The check finds a function's paths with the search above, over the
function's graph as a table: each block's label, with the labels of the
blocks that its terminator can jump to (`Func.Edge`). Every path starts at
the entry. The theorems below say that the search decides `Func.Reachable`
and `Func.Dominates` for every block of the function.
-/

namespace Fir

variable {d : Dialect}

/-- The graph of a function: each block's label, with the labels that the
block can jump to. A label that names several blocks has the successors of
each. -/
def Func.graph (f : Func d) : Std.HashMap Name (List Name) :=
  grouped (f.blocks.map fun b => (b.label, b.succLabels))

/-- Where every path of a function starts: its entry block, if it has one. -/
def Func.start (f : Func d) : List Name := f.entryLabel?.toList

/-- The labels that a path from `start` reaches in the graph `g`. -/
def reachedIn (g : Std.HashMap Name (List Name)) (start : List Name) : Std.HashSet Name :=
  search g (fun _ => true) ∅ start

/-- The labels that a path from `start` reaches in the graph `g` without
passing through `a`. -/
def avoidingIn (g : Std.HashMap Name (List Name)) (start : List Name) (a : Name) :
    Std.HashSet Name :=
  search g (· != a) ∅ start

/-- Whether block `a` dominates block `l`: they are one block, or no path
from the start reaches `l` without passing through `a`. -/
def dominatesIn (g : Std.HashMap Name (List Name)) (start : List Name) (a l : Name) : Bool :=
  a == l || !(avoidingIn g start a).contains l

theorem Func.contains_graph (f : Func d) (l : Name) :
    f.graph.contains l = true ↔ ∃ b ∈ f.blocks, b.label = l := by
  rw [Func.graph, contains_grouped]
  simp only [List.mem_map]
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨_, ⟨b, hb, rfl⟩, rfl⟩

theorem Func.mem_graph (f : Func d) (x y : Name) : y ∈ f.graph.getD x [] ↔ f.Edge x y := by
  rw [Func.graph, mem_getD_grouped]
  simp only [List.mem_map, Func.Edge]
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, rfl, hy⟩
    exact ⟨b, hb, rfl, hy⟩
  · rintro ⟨b, hb, rfl, hy⟩
    exact ⟨_, ⟨b, hb, rfl⟩, rfl, hy⟩

theorem Func.reachable_iff_reach (f : Func d) (l : Name) :
    f.Reachable l ↔ Reach (f.graph.getD · []) (fun _ => true) f.start l := by
  constructor
  · intro h
    induction h with
    | entry he => exact .start (by simp [Func.start, he]) rfl
    | step _ he ih => exact .step ih ((f.mem_graph _ _).mpr he) rfl
  · intro h
    induction h with
    | start hx => exact .entry (by simpa [Func.start] using hx)
    | step _ hy _ ih => exact .step ih ((f.mem_graph _ _).mp hy)

theorem Func.reachesAvoiding_iff_reach (f : Func d) (a l : Name) :
    f.ReachesAvoiding a l ↔ Reach (f.graph.getD · []) (· != a) f.start l := by
  constructor
  · intro h
    induction h with
    | entry he hne => exact .start (by simp [Func.start, he]) (by simpa using hne)
    | step _ he hne ih => exact .step ih ((f.mem_graph _ _).mpr he) (by simpa using hne)
  · intro h
    induction h with
    | start hx hok => exact .entry (by simpa [Func.start] using hx) (by simpa using hok)
    | step _ hy hok ih => exact .step ih ((f.mem_graph _ _).mp hy) (by simpa using hok)

/-- The search decides which blocks the entry reaches. -/
theorem Func.reachedIn_iff {f : Func d} {l : Name} (hl : ∃ b ∈ f.blocks, b.label = l) :
    (reachedIn f.graph f.start).contains l = true ↔ f.Reachable l := by
  rw [← Std.HashSet.mem_iff_contains, reachedIn,
    contains_search_iff ((f.contains_graph l).mpr hl), f.reachable_iff_reach]

/-- The search decides dominance between the blocks of a function. -/
theorem Func.dominatesIn_iff {f : Func d} {a l : Name} (hl : ∃ b ∈ f.blocks, b.label = l) :
    dominatesIn f.graph f.start a l = true ↔ f.Dominates a l := by
  rw [dominatesIn, Func.Dominates, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
    Bool.eq_false_iff, ne_eq, ← Std.HashSet.mem_iff_contains, avoidingIn,
    contains_search_iff ((f.contains_graph l).mpr hl), f.reachesAvoiding_iff_reach]

end Fir
