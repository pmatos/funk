import Fir.Memory.Policy

/-!
# Address resolvers

Turning an integer back into a pointer takes an angelic choice among the
live, exposed allocations of its memory that hold the address, the address
one past an allocation's end included. A freed allocation never counts
(the human's ruling of 2026-11-18 on #232, Q3). Two allocations can hold
one address: one may end where the next starts. The run makes the choice,
and a step cannot look ahead at what the program does with the pointer, so
the choice is stated outside the step: the run's _resolver_.

A resolver is chosen per call (the human's ruling of 2026-11-20 on #232,
question A): the run counts the integers it turns back into pointers, and
the resolver sees that count, the places of the memory's blocks and the
address, and proposes an allocation, or none. So each call may pick
differently. The memory model takes the proposal when it holds the
address, and otherwise its own pick. The section on runs under every
address policy keeps, among all resolvers, those that avoid UB when one
does. Rejected: a resolver per memory state, under which two calls on the
same address in the same memories pick the same allocation, narrower than
the ruling; wildcard provenance, as Miri has, resolved at each access,
which is broader; and the fixed rule that the allocation that starts at
the address wins, which is not angelic.

The memory model's own pick, which `fir-ref` takes, is the first
allocation, in the order they were made, whose units hold the address,
and when none does, the first whose end it is. It is `fir-ref`'s choice,
not a rule of the spec. When no allocation holds the address, the pointer
has no provenance, and an access through it is immediate UB.

The integer is as wide as the memory's pointers (the human's ruling of
2026-11-18 on #232, Q2), and the pointer's offset is the address less its
allocation's.
-/

namespace Fir.Memory

variable {u : Nat}

/-- An address resolver for one memory: from the number of integers the
run has turned back into pointers, the places of the memory's blocks and
the address, the allocation it proposes, or none. -/
abbrev Resolver := Nat → List Place → Nat → Option AllocId

/-- The resolver of `fir-ref`: it proposes no allocation, so each call
takes the memory model's own pick. -/
def Resolver.canonical : Resolver := fun _ _ _ => none

namespace Memory

/-- Whether the allocation `a` holds the address `z`: it is live, has an
address `y`, and `z` is from `y` to its end, the end included. -/
def holds (M : Memory u) (z a : Nat) : Bool :=
  match M.blocks[a]? with
  | some b => b.live && match b.addr with
    | some y => decide (y ≤ z) && decide (z ≤ y + b.units.length)
    | none => false
  | none => false

/-- Whether the address `z` is the address of a unit of the allocation `a`:
it holds `z`, and `z` is not its end. -/
def within (M : Memory u) (z a : Nat) : Bool := M.holds z a && M.holds (z + 1) a

/-- The memory model's own pick for the address `z`: the first allocation
whose units hold it, and else the first whose end it is. None when no
allocation holds it. -/
def pick (M : Memory u) (z : Nat) : Option AllocId :=
  match (List.range M.blocks.length).find? (M.within z) with
  | some a => some a
  | none => (List.range M.blocks.length).find? (M.holds z)

/-- The allocation that the address `z` is turned into a pointer of, when
the resolver proposes `a?`: the proposal when it holds `z`, and else the
memory model's pick. -/
def resolve (M : Memory u) (z : Nat) : Option AllocId → Option AllocId
  | some a => if M.holds z a then some a else M.pick z
  | none => M.pick z

/-- The pointer that the address `z` becomes in the allocation `a?`: its
offset is `z` less the allocation's address, and with no allocation, it has
no provenance and the offset `z`. -/
def rebuild (M : Memory u) (z : Nat) : Option AllocId → Pointer
  | some a => ⟨some a, (z : Int) - ((M.addrOf a).getD 0 : Nat)⟩
  | none => ⟨none, z⟩

end Memory

namespace Memories

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]

/-- Turns the integer `i` of the memory `x`, whose pointers are `P` bits
wide, back into a pointer under the resolver `k`: the allocation that its
address resolves to, from the proposal of `k` at this call, and the
memories with one more call counted. It never fails. -/
def fromAddr (S : Memories Mem unit) (x : Mem) (k : Resolver) (P : Nat) (i : BitVec P) :
    Pointer × Memories Mem unit :=
  ((S.mem x).rebuild i.toNat ((S.mem x).resolve i.toNat (k S.rebuilds (S.mem x).places i.toNat)),
    { S with rebuilds := S.rebuilds + 1 })

end Memories

end Fir.Memory
