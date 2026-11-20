import Fir.Execution.MemoryRuns

/-!
# Runs under every address policy

A run gives each op an address policy for each memory, by the memory's
number in the data layout, and an op that exposes an allocation gives it
the address the policy proposes, when it may be given (the section on
address policies). An op passes the policy of the memory it exposes in,
and the width of that memory's pointers, from its layout entry, as it
passes the unit width. The spec allows an exposed allocation any address
that may be given, so its runs with memory are those under every policy:
the observable behaviour of a function with memory is each outcome that its
runs under some policy may have. The policy is chosen once for the run, as
an implementation lays its memory out once, and every budget of fuel runs
under it.

At each exposure, every address that may be given is the one given under
the policy that proposes it (the section on address policy laws). A policy
sees the places of its memory, which each exposure that gives an address
changes, so along one path no two exposures that give an address see the
same places: one policy can propose each of them its own address. That is
why the union over policies holds every assignment of addresses along a
path. It is an argument, not a theorem here.

`fir-ref` runs under one policy, the canonical layout, which a run made from
its module gives. Each outcome of that run is one of the spec's. Every
theorem on the runs with memory holds for every record of items, and so for
every policy. A refinement that holds under each policy holds of the runs
under every policy.
-/

namespace Fir

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DecidableEq d.Ty] [DialectCall d]
  [DialectEffects d] [DialectMemDenote d] {N : Type} [DecidableEq N] (lay : N → MemLayout)
  (ρ : DialectEffects.Mem d → N) (L : RunItems)

/-- The observable behaviour with memory of the function `f` of the module
`M` on the arguments `a`, under every address policy: each outcome of its
runs with memory under some policy `g`, with the items `L`. -/
def Func.memBehaviour (M : Module d) (f : Func d) (a : HVector toType (f.params.map (·.2))) :
    Behaviour (List (DVal d)) :=
  fun o => ∃ g, observable (f.memRuns lay ρ (L.withAddrs g) M a) o

/-- Each outcome of a run under one policy, the canonical layout of
`fir-ref` included, is an outcome of the runs under every policy. -/
theorem Func.memBehaviour_of_observable {M : Module d} {f : Func d}
    {a : HVector toType (f.params.map (·.2))} {o : Outcome (List (DVal d))}
    (h : observable (f.memRuns lay ρ L M a) o) : f.memBehaviour lay ρ L M a o :=
  ⟨L.addrs, h⟩

variable [TyRefinement d.Ty]

/-- A refinement that holds under each address policy holds of the runs
under every policy. -/
theorem Func.memBehaviour_isRefinedBy {M M' : Module d} {f f' : Func d}
    {a : HVector toType (f.params.map (·.2))} {a' : HVector toType (f'.params.map (·.2))}
    (h : ∀ g, observable (f.memRuns lay ρ (L.withAddrs g) M a) ⊑
      observable (f'.memRuns lay ρ (L.withAddrs g) M' a')) :
    f.memBehaviour lay ρ L M a ⊑ f'.memBehaviour lay ρ L M' a' := by
  intro t ⟨g, ht⟩
  obtain ⟨s, hs, hst⟩ := h g t ht
  exact ⟨s, ⟨g, hs⟩, hst⟩

end Fir
