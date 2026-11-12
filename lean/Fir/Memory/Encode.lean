import Fir.Memory.Model
import Fir.Syntax.Layout
import Fir.Execution.Values

/-!
A load reads units of a memory and a store writes them, but an op computes
with values. This section says how a value of an integer type `iN` or of a
pointer type `ptr<N>` becomes units of a memory whose units are `u` bits
wide, its _encoding_, and how units become a value again, their
_decoding_ (ADR-2026-11-12-2125). Every dialect whose types have these
values uses them, so they are written once, over `PoisonOr (BitVec w)` and
`PoisonOr Pointer`, the values of those types.

* An integer of `w` bits takes `⌈w / u⌉` units, its digits in base `2^u`.
  When `w` is not a multiple of `u`, its last unit has bits to spare: the
  encoding sets them to zero, and the decoding ignores them, whatever they
  hold. The human ruled this on 2026-11-11, on #231.
* A pointer of the memory `m` takes as many units as `m`'s pointer width
  needs, and each holds one of its fragments, with `m`. So a pointer copied
  unit by unit keeps its provenance (ADR-2026-11-09-1542), and a pointer of
  one memory never decodes as a pointer of another, since a pointer moves
  between memories only through an op (ADR-2026-11-09-1542).
* Poison takes the same number of units, each of them poison.
* The memory's byte order places the units: `little` puts the least
  significant first, at the lowest offset, and `big` the most significant.
  The laws hold at every byte order, and M1's layouts admit only `little`
  (the human's ruling of 2026-11-11 on #231).

Decoding is defined for any units, so a load always has a value. Units that
are not the encoding of a value of the type decode to poison: an integer
from a unit that is poison or a pointer's fragment, and a pointer of `m`
from anything but the fragments of one pointer of `m`, in order. So a
punned load gives poison,
as the human ruled on 2026-11-11, on #231, and a pointer that is partly
overwritten is no longer a pointer. Units of the wrong number decode to
poison too, though a load reads exactly the units of its type.

The section after this one proves the laws.
-/

namespace Fir

/-- Places a value's units in the memory's byte order: the units are given
least significant first, `little` keeps that order, and `big` reverses it.
Placing twice gives the units back, so decoding places them again. -/
def ByteOrder.place {α : Type} : ByteOrder → List α → List α
  | .little, us => us
  | .big, us => us.reverse

namespace Memory

/-- The number of `u`-bit units that `w` bits take: `w / u`, rounded up. -/
def unitsFor (u w : Nat) : Nat := (w + u - 1) / u

/-- The `k` digits of `n` in base `2^u`, least significant first, each a
unit of bits. Digits past `n`'s most significant one are zero. -/
def digits (u : Nat) : Nat → Nat → List (MemUnit u)
  | 0, _ => []
  | k + 1, n => .bits (BitVec.ofNat u n) :: digits u k (n / 2 ^ u)

/-- The number that units of bits stand for, least significant first, or
none when one of them is poison or a pointer's fragment. -/
def unitsValue {u : Nat} : List (MemUnit u) → Option Nat
  | [] => some 0
  | .bits b :: us => (unitsValue us).map (b.toNat + 2 ^ u * ·)
  | _ :: _ => none

/-- The encoding of a value of `iN`, `N = w`, in `u`-bit units placed in
the byte order `o`: its `⌈w / u⌉` digits, with the bits past `w` zero, or
as many poison units. -/
def encodeInt (u : Nat) (o : ByteOrder) {w : Nat} : PoisonOr (BitVec w) → List (MemUnit u)
  | .poison => List.replicate (unitsFor u w) .poison
  | .value b => o.place (digits u (unitsFor u w) b.toNat)

/-- The decoding of `u`-bit units in the byte order `o` as a value of
`iN`, `N = w`: the number they stand for, cut to its low `w` bits, when
there are `⌈w / u⌉` of them and each holds bits; poison otherwise. -/
def decodeInt (u w : Nat) (o : ByteOrder) (us : List (MemUnit u)) : PoisonOr (BitVec w) :=
  if us.length = unitsFor u w then
    match unitsValue (o.place us) with
    | some n => .value (BitVec.ofNat w n)
    | none => .poison
  else .poison

/-- The `k` fragments of the pointer `p` of the memory `m`, least
significant first. -/
def fragments {u : Nat} (m k : Nat) (p : Pointer) : List (MemUnit u) :=
  (List.range k).map (.frag m p)

/-- The encoding of a value of the pointer type of the memory `m` in `k`
units placed in the byte order `o`: the pointer's fragments, or `k` poison
units. -/
def encodePtr {u : Nat} (m k : Nat) (o : ByteOrder) : PoisonOr Pointer → List (MemUnit u)
  | .poison => List.replicate k .poison
  | .value p => o.place (fragments m k p)

/-- The decoding of units in the byte order `o` as a value of the pointer
type of the memory `m`, which takes `k` units: the pointer `p` when they
are the `k` fragments of `p` of `m`, in order; poison otherwise. In one
memory a pointer of `m` always takes the same `k` units, so the first units
of a pointer of `m` are never a pointer of `m`. -/
def decodePtr {u : Nat} (m k : Nat) (o : ByteOrder) (us : List (MemUnit u)) : PoisonOr Pointer :=
  match o.place us with
  | xs@(.frag _ p _ :: _) => if xs = fragments m k p then .value p else .poison
  | _ => .poison

end Memory

end Fir
