import Fir.Memory.Encode
import Fir.Memory.Laws

/-!
The laws of encoding values in units, which the ops that load and store
rest on:

* An encoding takes the type's number of units, whatever the value: `⌈w / u⌉`
  for an integer of `w` bits, and the pointer's number for a pointer.
* Decoding an encoding gives the value back, poison included, at every
  byte order. So a load after a store of a value gives the value back, and
  a pointer copied unit by unit keeps its provenance.
* An integer's encoding is the integer itself, with every bit past its
  width zero, and its decoding ignores those bits.
* A punned decoding gives poison: an integer from a pointer's encoding,
  and a pointer from an integer's.
-/

namespace Fir

variable {α : Type}

/-- Placing in a byte order twice gives the units back. -/
theorem ByteOrder.place_place (o : ByteOrder) (us : List α) : o.place (o.place us) = us := by
  cases o <;> simp [place]

/-- Placing keeps the number of units. -/
theorem ByteOrder.length_place (o : ByteOrder) (us : List α) : (o.place us).length = us.length := by
  cases o <;> simp [place]

/-- Placing keeps which units there are. -/
theorem ByteOrder.mem_place {o : ByteOrder} {us : List α} {x : α} : x ∈ o.place us ↔ x ∈ us := by
  cases o <;> simp [place]

/-- Units that are all the same stay as they are when placed. -/
theorem ByteOrder.place_replicate (o : ByteOrder) (n : Nat) (x : α) :
    o.place (List.replicate n x) = List.replicate n x := by
  cases o <;> simp [place]

namespace Memory

variable {u : Nat}

/-!
# How many units
-/

/-- `⌈w / u⌉` units of `u` bits hold `w` bits. -/
theorem le_mul_unitsFor {w : Nat} (hu : 0 < u) : w ≤ u * unitsFor u w := by
  have h1 := Nat.div_add_mod (w + u - 1) u
  have h2 := Nat.mod_lt (w + u - 1) hu
  simp only [unitsFor]
  omega

/-- A value of at least one bit takes at least one unit. -/
theorem unitsFor_pos {w : Nat} (hu : 0 < u) (hw : 0 < w) : 0 < unitsFor u w :=
  Nat.div_pos (by omega) hu

/-- There are `k` digits. -/
theorem length_digits (k n : Nat) : (digits u k n).length = k := by
  induction k generalizing n <;> simp [digits, *]

/-- An integer's encoding takes `⌈w / u⌉` units, poison's too. -/
theorem length_encodeInt (o : ByteOrder) {w : Nat} (v : PoisonOr (BitVec w)) :
    (encodeInt u o v).length = unitsFor u w := by
  cases v <;> simp [encodeInt, ByteOrder.length_place, length_digits]

/-- There are `k` fragments. -/
theorem length_fragments (k : Nat) (p : Pointer) : (fragments k p : List (MemUnit u)).length = k := by
  simp [fragments]

/-- A pointer's encoding takes its `k` units, poison's too. -/
theorem length_encodePtr (k : Nat) (o : ByteOrder) (v : PoisonOr Pointer) :
    (encodePtr k o v : List (MemUnit u)).length = k := by
  cases v <;> simp [encodePtr, ByteOrder.length_place, length_fragments]

/-!
# Integers
-/

/-- The digits of `n` stand for `n` cut to as many bits as they hold. -/
theorem unitsValue_digits (k n : Nat) : unitsValue (digits u k n) = some (n % 2 ^ (u * k)) := by
  induction k generalizing n with
  | zero => simp [digits, unitsValue, Nat.mod_one]
  | succ k ih =>
    simp only [digits, unitsValue, ih, Option.map_some, BitVec.toNat_ofNat]
    rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (u * k)), Nat.mod_mul]

/-- An integer's encoding is the integer itself, read least significant
unit first: every bit past its width is zero. -/
theorem unitsValue_encodeInt (hu : 0 < u) (o : ByteOrder) {w : Nat} (b : BitVec w) :
    unitsValue (o.place (encodeInt u o (.value b))) = some b.toNat := by
  rw [encodeInt, ByteOrder.place_place, unitsValue_digits, Nat.mod_eq_of_lt]
  exact Nat.lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by decide) (le_mul_unitsFor hu))

/-- Units that are not all bits stand for no number. -/
theorem unitsValue_eq_none {us : List (MemUnit u)} {x : MemUnit u} (hx : x ∈ us)
    (hb : ∀ b, x ≠ .bits b) : unitsValue us = none := by
  induction us with
  | nil => simp at hx
  | cons y us ih =>
    rcases List.mem_cons.1 hx with rfl | hx'
    · cases x with
      | bits b => exact absurd rfl (hb b)
      | poison | frag _ _ => rfl
    · cases y <;> simp [unitsValue, ih hx']

/-- Decoding the right number of units of bits gives the number they stand
for, cut to the type's width. -/
theorem decodeInt_eq_value {w : Nat} {o : ByteOrder} {us : List (MemUnit u)} {n : Nat}
    (hlen : us.length = unitsFor u w) (h : unitsValue (o.place us) = some n) :
    decodeInt u w o us = .value (BitVec.ofNat w n) := by
  simp [decodeInt, hlen, h]

/-- Decoding ignores the bits past the type's width: units whose numbers
agree on the low `w` bits decode to the same value. -/
theorem decodeInt_ignores_padding {w : Nat} {o : ByteOrder} {us us' : List (MemUnit u)} {n n' : Nat}
    (hlen : us.length = unitsFor u w) (h : unitsValue (o.place us) = some n)
    (hlen' : us'.length = unitsFor u w) (h' : unitsValue (o.place us') = some n')
    (hmod : n % 2 ^ w = n' % 2 ^ w) : decodeInt u w o us = decodeInt u w o us' := by
  rw [decodeInt_eq_value hlen h, decodeInt_eq_value hlen' h']
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [hmod]

/-- Decoding an integer's encoding gives it back, at every byte order. -/
theorem decodeInt_encodeInt_value (hu : 0 < u) (o : ByteOrder) {w : Nat} (b : BitVec w) :
    decodeInt u w o (encodeInt u o (.value b)) = .value b := by
  rw [decodeInt_eq_value (length_encodeInt o _) (unitsValue_encodeInt hu o b)]
  simp

/-- Decoding poison's encoding gives poison, for a type of at least one
bit. -/
theorem decodeInt_encodeInt_poison (hu : 0 < u) (o : ByteOrder) {w : Nat} (hw : 0 < w) :
    decodeInt u w o (encodeInt u o (.poison : PoisonOr (BitVec w))) = .poison := by
  obtain ⟨k, hk⟩ : ∃ k, unitsFor u w = k + 1 := ⟨unitsFor u w - 1, by
    have := unitsFor_pos hu hw; omega⟩
  simp only [decodeInt, encodeInt, ByteOrder.place_replicate, List.length_replicate, ite_true]
  rw [hk, List.replicate_succ]
  rfl

/-- Decoding an encoding gives the value back, poison included, at every
byte order: the integer law. -/
theorem decodeInt_encodeInt (hu : 0 < u) (o : ByteOrder) {w : Nat} (hw : 0 < w)
    (v : PoisonOr (BitVec w)) : decodeInt u w o (encodeInt u o v) = v := by
  cases v with
  | poison => exact decodeInt_encodeInt_poison hu o hw
  | value b => exact decodeInt_encodeInt_value hu o b

/-!
# Pointers
-/

/-- Decoding an encoding gives the value back, poison included, at every
byte order: the pointer law, for a pointer that takes at least one unit. -/
theorem decodePtr_encodePtr {k : Nat} (hk : 0 < k) (o : ByteOrder) (v : PoisonOr Pointer) :
    decodePtr k o (encodePtr (u := u) k o v) = v := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  cases v with
  | poison =>
    simp only [decodePtr, encodePtr, ByteOrder.place_replicate]
    rw [List.replicate_succ]
  | value p => simp [decodePtr, encodePtr, ByteOrder.place_place, fragments, List.range_succ_eq_map]

/-- Every unit of an integer's digits is bits. -/
theorem mem_digits {k n : Nat} {x : MemUnit u} (hx : x ∈ digits u k n) : ∃ b, x = .bits b := by
  induction k generalizing n with
  | zero => simp [digits] at hx
  | succ k ih =>
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨_, rfl⟩
    · exact ih hx

/-- A pointer's encoding has a unit that is not bits. -/
theorem exists_mem_encodePtr {k : Nat} (hk : 0 < k) (o : ByteOrder) (v : PoisonOr Pointer) :
    ∃ x ∈ (encodePtr k o v : List (MemUnit u)), ∀ b, x ≠ .bits b := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  cases v with
  | poison => exact ⟨.poison, by simp [encodePtr], by simp⟩
  | value p => exact ⟨.frag p 0, by simp [encodePtr, ByteOrder.mem_place, fragments], by simp⟩

/-- A punned load of an integer gives poison: decoding a pointer's units as
an integer, at any byte order. -/
theorem decodeInt_encodePtr {k : Nat} (hk : 0 < k) (o o' : ByteOrder) (w : Nat)
    (v : PoisonOr Pointer) : decodeInt u w o (encodePtr k o' v) = .poison := by
  obtain ⟨x, hx, hb⟩ := exists_mem_encodePtr (u := u) hk o' v
  unfold decodeInt
  split
  · rw [unitsValue_eq_none (ByteOrder.mem_place.2 hx) hb]
  · rfl

/-- A punned load of a pointer gives poison: decoding an integer's units as
a pointer, at any byte order. -/
theorem decodePtr_encodeInt (k : Nat) (o o' : ByteOrder) {w : Nat} (v : PoisonOr (BitVec w)) :
    decodePtr k o (encodeInt u o' v) = .poison := by
  unfold decodePtr
  split
  · rename_i p i rest h
    have hx : MemUnit.frag p i ∈ encodeInt u o' v :=
      ByteOrder.mem_place.1 (h ▸ List.mem_cons_self)
    cases v with
    | poison => simp [encodeInt] at hx
    | value b =>
      obtain ⟨_, hb⟩ := mem_digits (ByteOrder.mem_place.1 hx)
      cases hb
  · rfl

/-!
# Through memory
-/

/-- A load after a store of an integer's encoding, decoded, gives the
integer back, poison included. -/
theorem load_store_encodeInt {M M' : Memory u} {p : Pointer} (hu : 0 < u) (o : ByteOrder)
    {w : Nat} (hw : 0 < w) {v : PoisonOr (BitVec w)} (h : M.store p (encodeInt u o v) = .ok M') :
    (M'.load p (unitsFor u w)).map (decodeInt u w o) = .ok v := by
  have hl := Memory.load_store_same h
  rw [length_encodeInt] at hl
  simp [hl, Except.map, decodeInt_encodeInt hu o hw]

/-- A load after a store of a pointer's encoding, decoded, gives the
pointer back, its provenance included: a pointer stored to memory keeps
it. -/
theorem load_store_encodePtr {M M' : Memory u} {p : Pointer} {k : Nat} (hk : 0 < k)
    (o : ByteOrder) {v : PoisonOr Pointer} (h : M.store p (encodePtr k o v) = .ok M') :
    (M'.load p k).map (decodePtr k o) = .ok v := by
  have hl := Memory.load_store_same h
  rw [length_encodePtr] at hl
  simp [hl, Except.map, decodePtr_encodePtr hk o]

end Memory

end Fir
