import Fir.Core.Values
import Fir.Core.Validation
import Fir.Memory.EncodeLaws
import Fir.Validation.Layout

/-!
The core's values in memory. A value of `iN` or of `ptr<N>` is stored in a
memory whose units are `u` bits wide, in the memory's byte order, by the
encodings of the section on values in units. The module's data layout
gives the width of `ptr<N>`'s pointers, from its entry for the memory `N`,
so a pointer takes as many units of the memory it is stored in as that
width needs.

The core's loads and stores read and write integers and pointers (#231).
A float type has no encoding here: no op stores one yet. Nor does a
pointer type whose memory the layout does not declare, which validation
rejects.

The laws: an encoding takes the type's size, and decoding it gives the
value back, poison included, at every byte order, for every valid type of
a valid layout.
-/

namespace Fir

/-- Each memory of a valid layout has pointers of at least one bit, the
default memory included. -/
theorem DataLayout.pointer_pos {l : DataLayout} (hl : l.Valid) {n : Nat} {e : MemLayout}
    (h : l.memory? n = some e) : 0 < e.pointer := by
  unfold DataLayout.memory? at h
  split at h
  · rename_i he
    cases h
    exact (hl.entries _ (List.mem_of_find?_eq_some he)).pointer.1
  · split at h
    · cases h
      decide
    · cases h

namespace Core

open Memory

/-- The size of a value of the type `t` in a memory whose units are `u`
bits wide, under the layout `l`: `⌈N / u⌉` units for `iN`, and for
`ptr<N>` as many as the width of memory `N`'s pointers needs. A float type
has none, and neither has a pointer into a memory that `l` does not
declare. -/
def Ty.units? (l : DataLayout) (u : Nat) : Ty → Option Nat
  | .int w => some (unitsFor u w)
  | .ptr n => (l.memory? n).map fun e => unitsFor u e.pointer
  | .float _ _ => none

/-- The encoding of a value of the type `t` in `u`-bit units placed in the
byte order `o`, under the layout `l`, when `t` has a size. -/
def Ty.encode? (l : DataLayout) (u : Nat) (o : ByteOrder) : (t : Ty) → ⟦t⟧ → Option (List (MemUnit u))
  | .int _, v => some (encodeInt u o v)
  | .ptr n, v => (l.memory? n).map fun e => encodePtr (unitsFor u e.pointer) o v
  | .float _ _, _ => none

/-- The decoding of `u`-bit units in the byte order `o` as a value of the
type `t`, under the layout `l`, when `t` has a size. -/
def Ty.decode? (l : DataLayout) (u : Nat) (o : ByteOrder) : (t : Ty) → List (MemUnit u) → Option ⟦t⟧
  | .int w, us => some (decodeInt u w o us)
  | .ptr n, us => (l.memory? n).map fun e => decodePtr (unitsFor u e.pointer) o us
  | .float _ _, _ => none

/-- A value's encoding takes the size of its type. -/
theorem Ty.encode?_length {l : DataLayout} {u : Nat} {o : ByteOrder} {t : Ty} {v : ⟦t⟧}
    {us : List (MemUnit u)} (h : t.encode? l u o v = some us) : t.units? l u = some us.length := by
  cases t with
  | int w =>
    cases h
    exact congrArg some (length_encodeInt (u := u) o (w := w) v).symm
  | ptr n =>
    simp only [Ty.encode?, Option.map_eq_some_iff] at h
    obtain ⟨e, he, rfl⟩ := h
    simp only [Ty.units?, he, Option.map_some]
    exact congrArg some (length_encodePtr (u := u) _ o v).symm
  | float _ _ => cases h

/-- Every integer type has a size, and so has a pointer type whose memory
the layout declares. -/
theorem Ty.units?_isSome {l : DataLayout} {u : Nat} {t : Ty} :
    (t.units? l u).isSome ↔ (∃ w, t = .int w) ∨ ∃ n, t = .ptr n ∧ l.Declares n := by
  cases t <;> simp [Ty.units?, DataLayout.Declares]

/-- Decoding a value's encoding gives the value back, poison included, at
every byte order, for a valid type of a valid layout. -/
theorem Ty.decode?_encode? {l : DataLayout} (hl : l.Valid) {u : Nat} (hu : 0 < u)
    (o : ByteOrder) {t : Ty} (ht : t.Valid) {v : ⟦t⟧} {us : List (MemUnit u)}
    (h : t.encode? l u o v = some us) : t.decode? l u o us = some v := by
  cases t with
  | int w =>
    cases h
    exact congrArg some (decodeInt_encodeInt hu o (w := w) (by simp only [Ty.Valid] at ht; omega) v)
  | ptr n =>
    simp only [Ty.encode?, Option.map_eq_some_iff] at h
    obtain ⟨e, he, rfl⟩ := h
    simp only [Ty.decode?, he]
    exact congrArg some (decodePtr_encodePtr (unitsFor_pos hu (DataLayout.pointer_pos hl he)) o v)
  | float _ _ => cases h

end Core

end Fir
