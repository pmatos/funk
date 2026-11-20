import Fir.Core.Store

/-!
# Fill rules

This section gives `memSet` its rule (#234; ADR-2026-11-09-1551). A fill,
written `memset`, writes `len` copies of one unit of the memory `N`
through a pointer of `ptr<N>`, where the unit is the value of an `iV` and
`len` is the unsigned value of an `iW`. The module's data layout asks that
`V` be the width of a unit of memory `N` (the human's ruling on #251:
a fill writes one unit value, sized to the memory's unit). The rule takes
the length first:

* a length of 0 does nothing and gives no result, whatever the pointer is,
  poison, dangling or without provenance included (the human's ruling of
  2026-11-18 on #234, Q1);
* otherwise a poison pointer is immediate UB: a pointer with no provenance
  in its place faults, so the UB is the op's own rule (the section on
  poison obligations with memory);
* otherwise it is the store of `len` copies of the value's unit through the
  pointer, an access aligned to one unit, so never misaligned. The unit of
  a value is its bits, and the unit of poison is a poison unit, so a fill
  with poison is not UB: it makes those units poison, as a store of poison
  does. An access that faults is immediate UB, for the reason of its
  fault: whether it faults depends on how many units it writes, not on
  what they hold, so a fill reads no memory.

A poison length runs as some length: the rule chooses `W` bits, as
`freeze` does, and runs with their unsigned value. So a poison length is
UB wherever some length is, as a poison operand is UB wherever some value
in its place is (ADR-2026-10-29-2006; the human's ruling of 2026-11-19 on
#234), and otherwise it writes the units of some length. A choice keeps
the memories and reads none.

`fir-ref run` runs a module without validating it, so the rule is total:
a value of a width that is not a unit's gives the unit of its low bits,
padded with zeros. The ordering does not change the rule: M1's validation
accepts only `nonatomic`. The rule needs the memory effect and the layout
entry of its memory, so `memSet` has no rule in the set monad (the section
on the core's rules with memory).
-/

namespace Fir.Core

open Memory

/-- The unit of `u` bits that a fill writes of a value of `iV`, `V = v`:
the value's bits, cut or padded with zeros to `u` bits, which they are
already when `V` is `u`, and a poison unit for poison. -/
def setUnit (u : Nat) {v : Nat} : PoisonOr (BitVec v) → MemUnit u
  | .value b => .bits (b.setWidth u)
  | .poison => .poison

/-- Why a fill through a poison pointer is UB. -/
def poisonSetPointer : String := "a memset through a poison pointer"

variable {N : Type} {m : Type → Type} [Monad m] [MonadUB m]

/-- The units that a fill of a defined length of `len` units of the value
`x` writes in a memory whose entry is `e`: `len` copies of its unit. -/
abbrev setUnits (e : MemLayout) {v : Nat} (len : Nat) (x : PoisonOr (BitVec v)) :
    List (MemUnit e.unit) :=
  List.replicate len (setUnit e.unit x)

/-- The rule of a fill of a defined length of `len` units of the core's
memory `n` with the value `x` through `p`, in a monad with UB and the
memory effect on the memories of a run whose layout entries are `lay`,
where the run names the core's memory `y` as `ρ y`: nothing for a length
of 0, UB on a poison pointer, and otherwise the store of `len` copies of
the value's unit in the memory `ρ n`, aligned to one unit, with no
result. -/
def setLenRule (lay : N → MemLayout) (ρ : Mem → N) [MonadMemory N (unitsOf lay) m] (v n len : Nat)
    (p : PoisonOr Pointer) (x : PoisonOr (BitVec v)) : m (HVector toType ([] : List Ty)) :=
  if len = 0 then pure .nil else
    match p with
    | .value p => (fun _ => .nil) <$> MonadMemory.store (unit := unitsOf lay) (m := m) (ρ n) p
        (setUnits (lay (ρ n)) len x) 1
    | .poison => MonadUB.ub poisonSetPointer

/-- The rule of `memSet o v w n` on the destination `p`, the value `x` and
the length `l`, an `iW` with `W = w`, in a monad with choice, UB and the
memory effect: the rule of the length's unsigned value, or, for a poison
length, of the unsigned value of `W` bits that it chooses. -/
def memSetRule [MonadChoice m] (lay : N → MemLayout) (ρ : Mem → N)
    [MonadMemory N (unitsOf lay) m] (v w n : Nat) (p : PoisonOr Pointer) (x : PoisonOr (BitVec v)) :
    PoisonOr (BitVec w) → m (HVector toType ([] : List Ty))
  | .value l => setLenRule lay ρ v n l.toNat p x
  | .poison => MonadChoice.choose w >>= fun l => setLenRule lay ρ v n l.toNat p x

/-- A morphism that keeps choice, UB and stores maps the rule of a fill in
the one monad to the same rule in the other. -/
theorem memSetRule_map {μ ν : Type → Type} [Monad μ] [Monad ν] [MonadChoice μ]
    [MonadChoice ν] [MonadUB μ] [MonadUB ν] (lay : N → MemLayout) (ρ : Mem → N)
    [MonadMemory N (unitsOf lay) μ] [MonadMemory N (unitsOf lay) ν] (φ : MonadMorphism μ ν)
    (hk : φ.KeepsChoiceUB)
    (hs : ∀ x p us al, φ.map (MonadMemory.store (m := μ) x p us al) = MonadMemory.store x p us al)
    (v w n : Nat) (p : PoisonOr Pointer) (x : PoisonOr (BitVec v)) (l : PoisonOr (BitVec w)) :
    φ.map (memSetRule (m := μ) lay ρ v w n p x l) = memSetRule lay ρ v w n p x l := by
  have hc (len : Nat) : φ.map (setLenRule (m := μ) lay ρ v n len p x) =
      setLenRule lay ρ v n len p x := by
    unfold setLenRule
    split
    · exact φ.map_pure _
    · cases p with
      | value q => exact (φ.map_map _ _).trans (congrArg _ (hs _ _ _ _))
      | poison => exact hk.ub _
  cases l with
  | value l => exact hc _
  | poison =>
    show φ.map (MonadChoice.choose w >>= _) = MonadChoice.choose w >>= _
    rw [φ.map_bind, hk.choose]
    exact congrArg _ (funext fun _ => hc _)

-- An `i8` gives the byte of its bits; poison gives a poison unit. A value
-- of another width gives its low bits, padded with zeros.
#guard setUnit 8 (.value 0xab#8) == .bits 0xab#8 && setUnit 8 (.poison : PoisonOr (BitVec 8)) == .poison
#guard setUnit 8 (.value 0x1ab#12) == .bits 0xab#8 && setUnit 16 (.value 0xab#8) == .bits 0xab#16

end Fir.Core
