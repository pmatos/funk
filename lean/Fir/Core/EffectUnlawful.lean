import Fir.Core.EffectLaws

/-!
# A declaration that the obligations reject

The core ops' effects, but `sdiv` declared without may-UB: `sdiv` by zero
is UB, so the effect obligations of the core dialect reject the
declaration, over the core's own semantics with memory.
-/

namespace Fir

namespace Core.Unlawful

/-- The core ops' effects, but `sdiv` declared without may-UB. -/
@[instance_reducible] def sdivNoUB : DialectEffects CoreDialect where
  Mem := Core.Mem
  poisonClass := Core.Op.poisonClass
  effects
    | .sdiv _ x => { mayPoison := x }
    | op => Core.Op.effects op

/-- `sdiv` by zero is UB, so the obligations reject the declaration, over
the core's own semantics with memory: an op left without may-UB must never
end in UB. -/
theorem sdivNoUB_unlawful :
    ¬ @LawfulDialectEffects CoreDialect _ _ _ sdivNoUB _ _
      (@DialectMemDenote.mk CoreDialect _ _ sdivNoUB fun lay ρ L => Core.memDenoteAt lay ρ L) := by
  intro h
  have hnever := @LawfulDialectEffects.neverUB CoreDialect _ _ _ sdivNoUB _ _ _ h
    (.sdiv 8 false) sdiv_typesValid (.inr rfl) rfl
  have hl := (Core.Op.liftsSetM (.sdiv 8 false) rfl rfl (fun _ : Unit => MemLayout.default)
    (fun _ => ())
    RunItems.empty (.cons (.value 1) (.cons (.value 0) .nil))).1
  have hub := (hnever (N := Unit) (fun _ => MemLayout.default) (fun _ => ()) RunItems.empty
    (.cons (.value 1) (.cons (.value 0) .nil))).1 rfl
  rw [hl] at hub
  exact NoUB.of_lift hub Memory.Memories.empty _ ((ruleOfEv_iff _ _ _ _).2 (.inr ⟨_, rfl, rfl⟩))

end Core.Unlawful

end Fir
