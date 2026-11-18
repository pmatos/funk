import Fir.Execution.Refinement

/-!
# Traces of events

A run shows an ordered trace of events (ADR-2026-11-09-1540). An event is
something the program hands to the world outside it, such as an external
call with its arguments, and the world answers it, such as with the call's
results. An event with its answer is an _act_, and a trace is a sequence of
acts. A dialect says what its events and answers are: the tickets that bring
external calls, volatile accesses and inline assembly add the core's.

A traced run ends in one of three ways: it returns, after a finite trace; it
hits UB, after a finite trace; or it diverges. A run that diverges either
falls silent after a finite trace, or shows acts forever, an infinite trace.

# Refinement of traced outcomes

An outcome of the source allows an outcome of the target when:

* the source hits UB after the trace _t_: the target first shows _t_, each
  of its acts refining _t_'s, and may then do anything. So UB in the source
  allows only a target that first shows the source's events;
* both return, with traces whose acts refine element by element, and the
  source's observation is refined by the target's;
* both fall silent after traces whose acts refine element by element;
* both show acts forever, and each act of the target refines the source's
  act at the same place.

One act refines another when its event refines the other's, with poison
refined as for values, and both have the same answer. The world answers what
the target shows: where the source shows poison in an event, the target may
show any value, and the source, whose poison may be any value, gets the same
answer.

# Worlds

A world answers each event from the acts shown before it. A target refines a
source when, for every world, each traced outcome that the target shows at
that world is allowed by one that the source shows with the same answers
(ADR-2026-11-09-1540). Every trace is shown at some world, so this is
refinement of traced behaviours, the theorem at the end of this section.
-/

namespace Fir

/-- An event answered by the world: an _act_ of a trace. -/
structure Act (E Ans : Type) where
  event : E
  answer : Ans
  deriving Repr, DecidableEq

/-- One act refines another when its event refines the other's and both have
the same answer. -/
instance [HRefinement E E] : HRefinement (Act E Ans) (Act E Ans) :=
  ⟨fun a b => a.event ⊑ b.event ∧ a.answer = b.answer⟩

section

variable {E Ans : Type} [HRefinement E E]

/-- Refinement of acts is reflexive when refinement of events is. -/
theorem Act.isRefinedBy_refl (h : ∀ e : E, e ⊑ e) (a : Act E Ans) : a ⊑ a :=
  ⟨h a.event, rfl⟩

/-- Refinement of acts is transitive when refinement of events is. -/
theorem Act.isRefinedBy_trans (h : ∀ {a b c : E}, a ⊑ b → b ⊑ c → a ⊑ c) {a b c : Act E Ans}
    (hab : a ⊑ b) (hbc : b ⊑ c) : a ⊑ c :=
  ⟨h hab.1 hbc.1, hab.2.trans hbc.2⟩

end

/-- How a traced run ends, for acts of type `A` and observations of type
`O`: it returns after a finite trace, hits UB after a finite trace, falls
silent after a finite trace, or shows acts forever. -/
inductive TOutcome (A O : Type) where
  | ret (tr : List A) (o : O)
  | ub (tr : List A) (reason : String)
  | diverge (tr : List A)
  | reacts (acts : Nat → A)

namespace TOutcome

variable {A O : Type}

/-- The act at place `i` of the outcome's trace, if the trace has one. -/
def act? : TOutcome A O → Nat → Option A
  | .ret tr _, i | .ub tr _, i | .diverge tr, i => tr[i]?
  | .reacts T, i => some (T i)

/-- The first `i` acts of the outcome's trace, or all of them when it has
fewer. -/
def before : TOutcome A O → Nat → List A
  | .ret tr _, i | .ub tr _, i | .diverge tr, i => tr.take i
  | .reacts T, i => (List.range i).map T

variable [HRefinement A A]

/-- The outcome `t` first shows the trace `tr`, each of its acts refining
`tr`'s at the same place. -/
def ShowsRefined (tr : List A) (t : TOutcome A O) : Prop :=
  ∀ i a, tr[i]? = some a → ∃ b, t.act? i = some b ∧ a ⊑ b

variable [HRefinement O O]

/-- An outcome of the source allows an outcome of the target. -/
def IsRefinedBy : TOutcome A O → TOutcome A O → Prop
  | .ub tr _, t => ShowsRefined tr t
  | .ret tr a, .ret tr' b => tr ⊑ tr' ∧ a ⊑ b
  | .diverge tr, .diverge tr' => tr ⊑ tr'
  | .reacts T, .reacts T' => ∀ i, T i ⊑ T' i
  | _, _ => False

instance : HRefinement (TOutcome A O) (TOutcome A O) := ⟨IsRefinedBy⟩

end TOutcome

/-- Lists that refine each other refine at each place of the first. -/
theorem List.IsRefinedBy.getElem?_some {A : Type} [HRefinement A A] {l l' : List A} (h : l ⊑ l')
    (i : Nat) (a : A) (ha : l[i]? = some a) : ∃ b, l'[i]? = some b ∧ a ⊑ b := by
  rcases List.IsRefinedBy.getElem? h i with ⟨h₁, _⟩ | ⟨a', b, h₁, h₂, hab⟩
  · rw [h₁] at ha
    cases ha
  · rw [h₁] at ha
    cases ha
    exact ⟨b, h₂, hab⟩

namespace TOutcome

variable {A O : Type} [HRefinement A A] [HRefinement O O]

/-- A target outcome that refines a source outcome shows, at each place of
the source's trace, an act that refines the source's. -/
theorem IsRefinedBy.acts : ∀ {s t : TOutcome A O}, s ⊑ t →
    ∀ i a, s.act? i = some a → ∃ b, t.act? i = some b ∧ a ⊑ b
  | .ub _ _, _, h => h
  | .ret _ _, .ret _ _, h => List.IsRefinedBy.getElem?_some h.1
  | .diverge _, .diverge _, h => List.IsRefinedBy.getElem?_some h
  | .reacts _, .reacts _, h => fun i a ha => by
    cases ha
    exact ⟨_, rfl, h i⟩
  | .ret _ _, .ub _ _, h | .ret _ _, .diverge _, h | .ret _ _, .reacts _, h
  | .diverge _, .ret _ _, h | .diverge _, .ub _ _, h | .diverge _, .reacts _, h
  | .reacts _, .ret _ _, h | .reacts _, .ub _ _, h | .reacts _, .diverge _, h => (h : False).elim

/-- Refinement of traced outcomes is reflexive when refinement of acts and of
observations is. -/
theorem isRefinedBy_refl (hA : ∀ a : A, a ⊑ a) (hO : ∀ o : O, o ⊑ o) :
    ∀ t : TOutcome A O, t ⊑ t
  | .ub _ _ => fun _ a ha => ⟨a, ha, hA a⟩
  | .ret tr o => ⟨List.isRefinedBy_refl hA tr, hO o⟩
  | .diverge tr => List.isRefinedBy_refl hA tr
  | .reacts T => fun i => hA (T i)

/-- Refinement of traced outcomes is transitive when refinement of acts and
of observations is. -/
theorem isRefinedBy_trans (hA : ∀ {a b c : A}, a ⊑ b → b ⊑ c → a ⊑ c)
    (hO : ∀ {a b c : O}, a ⊑ b → b ⊑ c → a ⊑ c) :
    ∀ {s m t : TOutcome A O}, s ⊑ m → m ⊑ t → s ⊑ t
  | .ub _ _, _, _, h₁, h₂ => fun i a ha =>
    let ⟨b, hb, hab⟩ := h₁ i a ha
    let ⟨c, hc, hbc⟩ := IsRefinedBy.acts h₂ i b hb
    ⟨c, hc, hA hab hbc⟩
  | .ret _ _, .ret _ _, .ret _ _, h₁, h₂ =>
    ⟨List.isRefinedBy_trans hA h₁.1 h₂.1, hO h₁.2 h₂.2⟩
  | .diverge _, .diverge _, .diverge _, h₁, h₂ => List.isRefinedBy_trans hA h₁ h₂
  | .reacts _, .reacts _, .reacts _, h₁, h₂ => fun i => hA (h₁ i) (h₂ i)
  | .ret _ _, .ub _ _, _, h, _ | .ret _ _, .diverge _, _, h, _ | .ret _ _, .reacts _, _, h, _
  | .diverge _, .ret _ _, _, h, _ | .diverge _, .ub _ _, _, h, _
  | .diverge _, .reacts _, _, h, _ | .reacts _, .ret _ _, _, h, _
  | .reacts _, .ub _ _, _, h, _ | .reacts _, .diverge _, _, h, _ => (h : False).elim
  | .ret _ _, .ret _ _, .ub _ _, _, h | .ret _ _, .ret _ _, .diverge _, _, h
  | .ret _ _, .ret _ _, .reacts _, _, h | .diverge _, .diverge _, .ret _ _, _, h
  | .diverge _, .diverge _, .ub _ _, _, h | .diverge _, .diverge _, .reacts _, _, h
  | .reacts _, .reacts _, .ret _ _, _, h | .reacts _, .reacts _, .ub _ _, _, h
  | .reacts _, .reacts _, .diverge _, _, h => (h : False).elim

end TOutcome

/-! # Traced behaviours -/

/-- A traced behaviour: a set of traced outcomes. -/
def TBehaviour (A O : Type) : Type := TOutcome A O → Prop

namespace TBehaviour

variable {A O : Type} [HRefinement A A] [HRefinement O O]

/-- Every outcome of the target behaviour is allowed by the source. -/
def IsRefinedBy (src tgt : TBehaviour A O) : Prop :=
  ∀ t, tgt t → ∃ s, src s ∧ s ⊑ t

instance : HRefinement (TBehaviour A O) (TBehaviour A O) := ⟨IsRefinedBy⟩

/-- UB before any event allows anything: a source that may hit UB before it
shows an act is refined by every target. -/
theorem ub_isRefinedBy {src : TBehaviour A O} {r : String} (h : src (.ub [] r))
    (tgt : TBehaviour A O) : src ⊑ tgt :=
  fun _ _ => ⟨.ub [] r, h, fun _ _ ha => nomatch ha⟩

/-- Refinement of traced behaviours is reflexive when refinement of acts and
of observations is. -/
theorem isRefinedBy_refl (hA : ∀ a : A, a ⊑ a) (hO : ∀ o : O, o ⊑ o) (b : TBehaviour A O) :
    b ⊑ b :=
  fun t ht => ⟨t, ht, TOutcome.isRefinedBy_refl hA hO t⟩

/-- Refinement of traced behaviours is transitive when refinement of acts and
of observations is, so a pipeline of correct passes is correct. -/
theorem isRefinedBy_trans (hA : ∀ {a b c : A}, a ⊑ b → b ⊑ c → a ⊑ c)
    (hO : ∀ {a b c : O}, a ⊑ b → b ⊑ c → a ⊑ c) {a b c : TBehaviour A O} (hab : a ⊑ b)
    (hbc : b ⊑ c) : a ⊑ c := fun t ht =>
  let ⟨m, hm, hmt⟩ := hbc t ht
  let ⟨s, hs, hsm⟩ := hab m hm
  ⟨s, hs, TOutcome.isRefinedBy_trans hA hO hsm hmt⟩

end TBehaviour

/-! # Worlds -/

/-- A world: it answers each event from the acts shown before it. -/
def World (E Ans : Type) : Type := List (Act E Ans) → E → Ans

namespace TOutcome

variable {E Ans O : Type}

/-- The outcome is shown at the world `w`: each act's answer is the world's
answer to its event, after the acts before it. -/
def InWorld (w : World E Ans) (t : TOutcome (Act E Ans) O) : Prop :=
  ∀ i a, t.act? i = some a → a.answer = w (t.before i) a.event

/-- The acts before a place of the trace are as many as the place. -/
theorem before_length {A : Type} :
    ∀ {t : TOutcome A O} {i : Nat} {a : A}, t.act? i = some a → (t.before i).length = i
  | .ret tr _, i, _, h | .ub tr _, i, _, h | .diverge tr, i, _, h => by
    have := (List.getElem?_eq_some_iff.mp h).1
    simp only [before, List.length_take]
    omega
  | .reacts _, _, _, _ => by simp [before]

/-- Every traced outcome is shown at some world: the one that answers the
event at each place of its trace with the answer there. -/
theorem inWorld_exists [Inhabited Ans] (t : TOutcome (Act E Ans) O) :
    ∃ w : World E Ans, t.InWorld w :=
  ⟨fun h _ => ((t.act? h.length).map (·.answer)).getD default, fun i a ha => by
    show a.answer = ((t.act? (t.before i).length).map (·.answer)).getD default
    rw [before_length ha, ha]
    rfl⟩

end TOutcome

namespace TBehaviour

variable {E Ans O : Type} [HRefinement E E] [HRefinement O O]

/-- The outcomes of a behaviour shown at the world `w`. -/
def atWorld (w : World E Ans) (b : TBehaviour (Act E Ans) O) : TBehaviour (Act E Ans) O :=
  fun t => b t ∧ t.InWorld w

/-- Refinement holds for every world: a target behaviour refines a source
behaviour exactly when, at every world, each outcome that the target shows
there is allowed by an outcome of the source, which shows the same answers.
-/
theorem isRefinedBy_iff_world [Inhabited Ans] {src tgt : TBehaviour (Act E Ans) O} :
    src ⊑ tgt ↔ ∀ w t, tgt.atWorld w t → ∃ s, src s ∧ s ⊑ t :=
  ⟨fun h _ t ht => h t ht.1, fun h t ht =>
    let ⟨w, hw⟩ := t.inWorld_exists
    h w t ⟨ht, hw⟩⟩

end TBehaviour

/-! # Behaviours with no event

A behaviour of the outcomes of M0 is a traced behaviour whose every trace is
empty: a return or UB after no act, and divergence silent from the start.
Refinement of such traced behaviours is refinement of the behaviours.
-/

/-- An outcome, as a traced outcome with an empty trace. -/
def TOutcome.ofOutcome {A O : Type} : Outcome O → TOutcome A O
  | .ret o => .ret [] o
  | .ub r => .ub [] r
  | .fuelExhausted => .diverge []

/-- A behaviour, as a traced behaviour whose every trace is empty. -/
def TBehaviour.ofBehaviour {A O : Type} (b : Behaviour O) : TBehaviour A O :=
  fun t => ∃ o, b o ∧ t = .ofOutcome o

section

variable {A O : Type} [HRefinement A A] [HRefinement O O]

/-- Two outcomes refine as traced outcomes with empty traces exactly when
they refine as outcomes. -/
theorem TOutcome.ofOutcome_isRefinedBy_iff :
    ∀ {s t : Outcome O}, (TOutcome.ofOutcome s : TOutcome A O) ⊑ (TOutcome.ofOutcome t : TOutcome A O) ↔ s ⊑ t
  | .ub _, _ => ⟨fun _ => trivial, fun _ _ _ ha => nomatch ha⟩
  | .ret _, .ret _ => ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
  | .fuelExhausted, .fuelExhausted => ⟨fun _ => trivial, fun _ => trivial⟩
  | .ret _, .ub _ | .ret _, .fuelExhausted | .fuelExhausted, .ret _
  | .fuelExhausted, .ub _ => ⟨fun h => (h : False).elim, fun h => (h : False).elim⟩

/-- Two behaviours refine as traced behaviours with empty traces exactly when
they refine as behaviours. -/
theorem TBehaviour.ofBehaviour_isRefinedBy_iff {src tgt : Behaviour O} :
    (TBehaviour.ofBehaviour src : TBehaviour A O) ⊑ (TBehaviour.ofBehaviour tgt : TBehaviour A O) ↔
      src ⊑ tgt := by
  constructor
  · intro h t ht
    obtain ⟨_, ⟨s, hs, rfl⟩, hst⟩ := h _ ⟨t, ht, rfl⟩
    exact ⟨s, hs, TOutcome.ofOutcome_isRefinedBy_iff.mp hst⟩
  · rintro h _ ⟨t, ht, rfl⟩
    obtain ⟨s, hs, hst⟩ := h t ht
    exact ⟨_, ⟨s, hs, rfl⟩, TOutcome.ofOutcome_isRefinedBy_iff.mpr hst⟩

end

end Fir
