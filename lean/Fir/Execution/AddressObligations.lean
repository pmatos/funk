import Fir.Execution.EffectLaws
import Fir.Execution.MemoryFromAddrLaws
import Fir.Execution.MemoryChoiceLaws

/-!
# Addresses and the declared allocation

The effect obligations compare units and shapes, not addresses, so they
cannot tell an op that exposes from one that does nothing (the section on
exposing in the state layer). Yet the address that an exposure gives
depends on the addresses that earlier exposures gave, so a pass that drops
or swaps exposures may change what later ones return. The human ruled on
2026-11-20, on #232 (question B), that exposing counts as allocating in its
memory, as a declared effect: an op that leaves an allocation in the memory
`x` out of its declaration gives no allocation of `x` an address.

The same holds of the count of integers turned back into pointers of a
memory, which the run's resolver sees (the section on address resolvers):
an op that leaves an allocation in `x` out of its declaration counts no
rebuild in `x`. Which declared effect covers that count is open for the
human; this obligation states the recommended one, that it counts as
allocating, as exposing does.

So, beside the effect obligations (the section on effect obligations), a
dialect whose declarations cover addresses meets two more, over each
valid op instance that runs by its own rule, wherever a run names the
dialect's memories:

* _No exposure in m_: when the op does not declare an allocation in `m`,
  every allocation of `m` keeps its address.
* _No rebuild in m_: when the op does not declare an allocation in `m`,
  the count of `m` is what it was.

They are a class of their own, so that the statement of the effect
obligations, which every guarantee over a dialect asks for, stays as it
is. An op that touches no memory meets both, as it keeps the memories.
-/

namespace Fir

open Memory

section

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem] {α β : Type} {x : Mem}

local notation "SM" => StateT (Memories Mem unit) SetM

/-- The computation `c` keeps the addresses and the count of the memory
`x`: it exposes nothing and counts no rebuild there. -/
def KeepsAddrs (x : Mem) (c : StateT (Memories Mem unit) SetM α) : Prop :=
  ExposesNot x c ∧ RebuildsNot x c

/-- A computation with no memory keeps every address and count. -/
theorem keepsAddrs_lift (c : SetM α) : KeepsAddrs (unit := unit) x (StateT.lift c) :=
  ⟨exposesNot_lift c, rebuildsNot_lift c⟩

/-- Mapping the results keeps the addresses and the count. -/
theorem KeepsAddrs.map (f : α → β) {c : SM α} (h : KeepsAddrs x c) : KeepsAddrs x (f <$> c) :=
  ⟨h.1.map f, h.2.map f⟩

/-- A sequence keeps the addresses and the count when its parts do. -/
theorem KeepsAddrs.bind {c : SM α} {f : α → SM β} (hc : KeepsAddrs x c)
    (hf : ∀ a, KeepsAddrs x (f a)) : KeepsAddrs x (c >>= f) :=
  ⟨hc.1.bind fun a => (hf a).1, hc.2.bind fun a => (hf a).2⟩

/-- A choice of bits then `g` keeps the addresses and the count when `g`
does on every bits. -/
theorem KeepsAddrs.chooseBind {w : Nat} {g : BitVec w → SM α} (hg : ∀ b, KeepsAddrs x (g b)) :
    KeepsAddrs x (MonadChoice.choose w >>= g) :=
  ⟨fun S a S' h => by
    obtain ⟨b, hb⟩ := (SetM.chooseBind_apply g S _).1 h
    exact (hg b).1 S a S' hb,
  fun S a S' h => by
    obtain ⟨b, hb⟩ := (SetM.chooseBind_apply g S _).1 h
    exact (hg b).2 S a S' hb⟩

/-- An allocation keeps every address and count. -/
theorem alloc_keepsAddrs (y : Mem) (k : AllocKind) (n al : Nat) (z : Mem) :
    KeepsAddrs z (MonadMemory.alloc (m := SM) y k n al) :=
  ⟨alloc_exposesNot y k n al z, alloc_rebuildsNot y k n al z⟩

/-- A load keeps every address and count. -/
theorem load_keepsAddrs (y : Mem) (p : Pointer) (n al : Nat) (z : Mem) :
    KeepsAddrs z (MonadMemory.load (m := SM) y p n al) :=
  ⟨load_exposesNot y p n al z, load_rebuildsNot y p n al z⟩

/-- A store keeps every address and count. -/
theorem store_keepsAddrs (y : Mem) (p : Pointer) (us : List (MemUnit (unit y))) (al : Nat)
    (z : Mem) : KeepsAddrs z (MonadMemory.store (m := SM) y p us al) :=
  ⟨store_exposesNot y p us al z, store_rebuildsNot y p us al z⟩

end

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectEffects d]
  [DialectMemDenote d]

/-- A dialect whose allocation declarations cover addresses and rebuilds:
every valid instance that runs by its own rule, a terminator or an op with
no callee, wherever a run names the dialect's memories, gives no address in
a memory where it does not declare an allocation, and counts no integer
turned back into a pointer there. -/
class LawfulDialectAddresses (d : Dialect) [TyDenote d.Ty] [DialectSignature d]
    [DialectEffects d] [DialectCall d] [DialectValidation d] [DialectMemDenote d] : Prop where
  exposesNot : ∀ op : d.Op, TypesValid op → isTerminator op = true ∨ callee? op = none →
    ∀ {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N) (L :
        RunItems) (x : N),
      ¬ ((effects op).allocates.map ρ).Has x → OwnRuleHas lay ρ L (ExposesNot x) op
  rebuildsNot : ∀ op : d.Op, TypesValid op → isTerminator op = true ∨ callee? op = none →
    ∀ {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N) (L :
        RunItems) (x : N),
      ¬ ((effects op).allocates.map ρ).Has x → OwnRuleHas lay ρ L (RebuildsNot x) op

/-- An op whose own rule keeps the addresses and the count of `x` gives no
address and counts no rebuild there. -/
theorem OwnRuleHas.addrs {op : d.Op} {N : Type} [DecidableEq N] {lay : N → MemLayout}
    {ρ : DialectEffects.Mem d → N} {L : RunItems} {x : N}
    (h : OwnRuleHas lay ρ L (KeepsAddrs x) op) :
    OwnRuleHas lay ρ L (ExposesNot x) op ∧ OwnRuleHas lay ρ L (RebuildsNot x) op :=
  ⟨fun args => ⟨fun ht => ((h args).1 ht).1, fun ht => ((h args).2 ht).1⟩,
    fun args => ⟨fun ht => ((h args).1 ht).2, fun ht => ((h args).2 ht).2⟩⟩

/-- An op whose own rule gives no address and counts no rebuild in `x`
keeps the addresses and the count of `x`. -/
theorem OwnRuleHas.keeps {op : d.Op} {N : Type} [DecidableEq N] {lay : N → MemLayout}
    {ρ : DialectEffects.Mem d → N} {L : RunItems} {x : N}
    (he : OwnRuleHas lay ρ L (ExposesNot x) op) (hr : OwnRuleHas lay ρ L (RebuildsNot x) op) :
    OwnRuleHas lay ρ L (KeepsAddrs x) op := fun args =>
  ⟨fun ht => ⟨(he args).1 ht, (hr args).1 ht⟩, fun ht => ⟨(he args).2 ht, (hr args).2 ht⟩⟩

/-- A dialect meets both obligations when each valid op that runs by its own
rule keeps the addresses and the count of each memory where it does not
declare an allocation. -/
theorem LawfulDialectAddresses.ofKeeps [DialectCall d] [DialectValidation d]
    (h : ∀ op : d.Op, TypesValid op → isTerminator op = true ∨ callee? op = none →
      ∀ {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N)
        (L : RunItems) (x : N),
        ¬ ((effects op).allocates.map ρ).Has x → OwnRuleHas lay ρ L (KeepsAddrs x) op) :
    LawfulDialectAddresses d where
  exposesNot op hv hc _ _ lay ρ L x hx := (OwnRuleHas.addrs (h op hv hc lay ρ L x hx)).1
  rebuildsNot op hv hc _ _ lay ρ L x hx := (OwnRuleHas.addrs (h op hv hc lay ρ L x hx)).2

end Fir
