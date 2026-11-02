import Fir

/-!
How `fir-ref run --seed S` draws its choices (ADR-2026-10-31-0002). Sampled
mode, the spec's `Core.sampled`, takes any generator: whatever it draws,
the values form a choice sequence that fits the run, so the outcome is one
of the run's (`Core.sampled_fits`, `Core.sampled_outcomes`). This file is
the generator that `fir-ref` gives it.

The generator is SplitMix64, seeded with S. A choice of `w` bits takes one
draw of 64 bits, and in one draw out of four it is one of the boundary bit
patterns: 0, 1, all ones, the signed minimum and the signed maximum. Bugs
gather there, and a uniform draw of many bits almost never meets them.
Otherwise it takes as many more draws as `w` needs, and keeps their low `w`
bits. So a seed draws the same values on every machine, for every version
of `fir-ref` that keeps this file.
-/

namespace FirRef

open Fir

/-- The state of the generator, SplitMix64. -/
structure Seed where
  state : UInt64

/-- The next 64 bits of the generator, and its next state. -/
def Seed.next (g : Seed) : UInt64 × Seed :=
  let s := g.state + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

/-- The next `n` draws of 64 bits, the first in the highest bits. It splits
`n` in halves, so that a wide choice takes time near linear in its bits. -/
def Seed.words : Nat → Seed → Nat × Seed
  | 0, g => (0, g)
  | 1, g => let (x, g) := g.next; (x.toNat, g)
  | n + 2, g =>
    let (hi, g) := Seed.words ((n + 2) / 2) g
    let (lo, g) := Seed.words (n + 2 - (n + 2) / 2) g
    (hi <<< (64 * (n + 2 - (n + 2) / 2)) ||| lo, g)
termination_by n _ => n
decreasing_by all_goals omega

/-- The boundary bit patterns of `w` bits, in the order the draw numbers
them. -/
def boundaries (w : Nat) : List (BitVec w) :=
  [0#w, 1#w, BitVec.allOnes w, BitVec.intMin w, BitVec.intMax w]

/-- A choice of `w` bits, and the generator's next state: in one draw out
of four, a boundary bit pattern, and otherwise `w` bits drawn uniformly. -/
def draw (w : Nat) (g : Seed) : BitVec w × Seed :=
  let (x, g) := g.next
  if x % 4 = 0 then ((boundaries w).getD (x / 4 % 5).toNat 0#w, g)
  else
    let (n, g) := Seed.words ((w + 63) / 64) g
    (BitVec.ofNat w n, g)

end FirRef
