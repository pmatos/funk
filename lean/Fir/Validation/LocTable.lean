import Fir.Syntax.Location

/-!
# The location table

The rule of a valid location table, which the general rules require of
every module.

Each entry of the table has a distinct reference, and the entries are in
increasing order of reference, so one table has one spelling. A location
that is built from others refers only to entries before it, so no location
refers to itself, directly or not. A fused location fuses at least two.
Every reference, line and column is below 2³².

A source range starts at line 1 or later, and does not end before it starts.
When both of its columns are known (not 0) and it starts and ends on one
line, its end column is at least its start column. An end equal to the
start is an empty range.
-/

namespace Fir

/-- A location is well formed. -/
def Location.WellFormed : Location → Prop
  | .range _ l₁ c₁ l₂ c₂ => 1 ≤ l₁ ∧ (l₁ < l₂ ∨ (l₁ = l₂ ∧ (c₁ = 0 ∨ c₂ = 0 ∨ c₁ ≤ c₂)))
  | .fused locs => 2 ≤ locs.length
  | _ => True

/-- The location table is well formed. -/
def LocTable.Valid (t : LocTable) : Prop :=
  (t.map (·.1)).Pairwise (· < ·) ∧ t.InLimits ∧
  ∀ e ∈ t, e.2.WellFormed ∧ ∀ r ∈ e.2.refs, r < e.1 ∧ r ∈ t.map (·.1)

end Fir
