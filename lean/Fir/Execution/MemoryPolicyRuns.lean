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
its module gives. Every theorem on the runs with memory holds for every
record of items, and so for every policy and every resolver. A refinement
that holds under each policy holds of the runs under every policy.

A run also turns integers back into pointers under a resolver for each
memory, which sees how many it has turned before, so each call may pick its
own allocation (the section on address resolvers). That choice is angelic:
the run picks whichever allocation keeps the program defined (the human's
rulings of 2026-11-18 and 2026-11-20 on #232, Q3 and question A). A step
cannot see what the program does later with the pointer, so the choice is
made over whole runs: for each policy, the spec keeps the resolvers whose
runs never end in UB, when there is one, and every resolver otherwise. The
spec's behaviour is each outcome of the runs under some policy and a
resolver it keeps. A resolver is chosen once for the run, as a policy is,
and every budget of fuel runs under it. Rejected: a union over every
resolver, under which one resolver that ends in UB would make the program
UB, which is not angelic.

`fir-ref` runs under the canonical resolver. When those runs never end in
UB, each of their outcomes is one of the spec's; when they do, an
other resolver may avoid it. A refinement that holds under each policy and
resolver lifts to the spec's behaviour when the target ends in UB under
each resolver under which the source does: without that, a target could
keep a resolver that the source drops.
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

/-! # Angelic resolvers -/

/-- The runs with memory of `f` under the policy `g` and the resolver `k` of
each memory, with the items `L`. -/
abbrev Func.memRunsUnder (M : Module d) (f : Func d) (a : HVector toType (f.params.map (·.2)))
    (g : Nat → Memory.Policy) (k : Nat → Memory.Resolver) : Nat → Run (List (DVal d)) :=
  f.memRuns lay ρ ((L.withAddrs g).withResolvers k) M a

/-- The resolver `k` is kept under the policy `g`: the runs under both
never end in UB, or the runs under `g` end in UB under every resolver. -/
def Func.Kept (M : Module d) (f : Func d) (a : HVector toType (f.params.map (·.2)))
    (g : Nat → Memory.Policy) (k : Nat → Memory.Resolver) : Prop :=
  (∀ r, ¬ observable (f.memRunsUnder lay ρ L M a g k) (.ub r)) ∨
    ∀ k', ∃ r, observable (f.memRunsUnder lay ρ L M a g k') (.ub r)

/-- The spec's observable behaviour with memory of the function `f` of the
module `M` on the arguments `a`: each outcome of its runs under some
address policy `g` and some resolver `k` kept under `g`, with the items
`L`. -/
def Func.angelicBehaviour (M : Module d) (f : Func d) (a : HVector toType (f.params.map (·.2))) :
    Behaviour (List (DVal d)) :=
  fun o => ∃ g k, f.Kept lay ρ L M a g k ∧ observable (f.memRunsUnder lay ρ L M a g k) o

/-- Each outcome of a run under the policy and resolver of its items, when
that resolver is kept, is one of the spec's. -/
theorem Func.angelicBehaviour_of_observable {M : Module d} {f : Func d}
    {a : HVector toType (f.params.map (·.2))} {o : Outcome (List (DVal d))}
    (hk : f.Kept lay ρ L M a L.addrs L.resolvers) (h : observable (f.memRuns lay ρ L M a) o) :
    f.angelicBehaviour lay ρ L M a o :=
  ⟨L.addrs, L.resolvers, hk, h⟩

/-- When a run under its items never ends in UB, as a run of `fir-ref` under
the canonical policy and resolver may, each of its outcomes is one of the
spec's. -/
theorem Func.angelicBehaviour_of_noUB {M : Module d} {f : Func d}
    {a : HVector toType (f.params.map (·.2))} {o : Outcome (List (DVal d))}
    (hu : ∀ r, ¬ observable (f.memRuns lay ρ L M a) (.ub r))
    (h : observable (f.memRuns lay ρ L M a) o) : f.angelicBehaviour lay ρ L M a o :=
  f.angelicBehaviour_of_observable lay ρ L (.inl hu) h

/-! # Refinement under every policy -/

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


/-- The spec's behaviour of `f` is refined by that of `f'` when each
resolver kept for `f'` under a policy is matched by one kept for `f`, whose
runs those of `f'` refine. -/
theorem Func.angelicBehaviour_isRefinedBy {M M' : Module d} {f f' : Func d}
    {a : HVector toType (f.params.map (·.2))} {a' : HVector toType (f'.params.map (·.2))}
    (h : ∀ g k, f'.Kept lay ρ L M' a' g k → ∃ k', f.Kept lay ρ L M a g k' ∧
      observable (f.memRunsUnder lay ρ L M a g k') ⊑
        observable (f'.memRunsUnder lay ρ L M' a' g k)) :
    f.angelicBehaviour lay ρ L M a ⊑ f'.angelicBehaviour lay ρ L M' a' := by
  intro t ⟨g, k, hk, ht⟩
  obtain ⟨k', hk', hr⟩ := h g k hk
  obtain ⟨s, hs, hst⟩ := hr t ht
  exact ⟨s, ⟨g, k', hk', hs⟩, hst⟩

/-- A refinement that holds under each policy and resolver holds of the
spec's behaviour, when the target ends in UB under each policy and
resolver under which the source does: then the source keeps each resolver
that the target keeps. -/
theorem Func.angelicBehaviour_isRefinedBy_of_each {M M' : Module d} {f f' : Func d}
    {a : HVector toType (f.params.map (·.2))} {a' : HVector toType (f'.params.map (·.2))}
    (h : ∀ g k, observable (f.memRunsUnder lay ρ L M a g k) ⊑
      observable (f'.memRunsUnder lay ρ L M' a' g k))
    (hu : ∀ g k, (∃ r, observable (f.memRunsUnder lay ρ L M a g k) (.ub r)) →
      ∃ r, observable (f'.memRunsUnder lay ρ L M' a' g k) (.ub r)) :
    f.angelicBehaviour lay ρ L M a ⊑ f'.angelicBehaviour lay ρ L M' a' := by
  refine Func.angelicBehaviour_isRefinedBy lay ρ L fun g k hk => ⟨k, ?_, h g k⟩
  rcases hk with hk | hk
  · exact .inl fun r hr => by
      obtain ⟨r', hr'⟩ := hu g k ⟨r, hr⟩
      exact hk r' hr'
  · refine .inr fun k' => ?_
    obtain ⟨r, hr⟩ := hk k'
    obtain ⟨s, hs, hsr⟩ := h g k' _ hr
    cases s with
    | ub r' => exact ⟨r', hs⟩
    | ret v => exact (hsr : False).elim
    | fuelExhausted => exact (hsr : False).elim

end Fir
