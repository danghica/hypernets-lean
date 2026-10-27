import Hypernets.Copying.FullBPermRobustness

/-! Apply the proved robustness theorem to arbitrary original closed paired
fillings, retaining the exact successful-transition count in both directions. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation
open Graph Combined

/-- Any original recursively filled closed pair supplies an initial lifting. -/
theorem filling_initial_lifting {d} {G H : Hypernet d [.term] []}
    (w : FillingWitness template G H) (left : HoleFree G) (right : HoleFree H) :
    (Specimens.system template Specimens.allContexts template_outputClosed).Lifting
      (StateClass.ofState ⟨d,G,(.search,.input 0)⟩) (StateClass.ofState ⟨d,H,(.search,.input 0)⟩) := by
  let S := w.specimen left right (.search,.input 0) rfl
  have l := w.specimen_left left right (.search,.input 0) rfl
  have r := w.specimen_right left right (.search,.input 0) rfl
  refine ⟨S,.inl (by change Focus.search ≠ Focus.rewrite; decide),?_,?_,l.symm,r.symm⟩
  · change StateClass.Rooted (StateClass.ofState S.leftState)
    rw [l]
    exact Search.rooted_initial G 0
  · change StateClass.Rooted (StateClass.ofState S.rightState)
    rw [r]
    exact Search.rooted_initial H 0

/-- Full BPerm has exact quantitative equivalence for every original closed
paired filling. There is no assumption about either continuation terminating. -/
theorem filling_exact_equiv {d} {G H : Hypernet d [.term] []}
    (w : FillingWitness template G H) (left : HoleFree G) (right : HoleFree H) :
    unboundedMachine.Equiv CostOrder.exact
      ⟨d,G,(.search,.input 0)⟩ ⟨d,H,(.search,.input 0)⟩ := by
  have lifting := filling_initial_lifting w left right
  exact ⟨Specimens.sufficiency template Specimens.allContexts template_outputClosed CostOrder.reasonable_exact
      (template_inputSafe _ _ _) (template_robust _ _ _) lifting,
    Specimens.sufficiency_converse template Specimens.allContexts template_outputClosed CostOrder.reasonable_exact
      (template_inputSafe _ _ _) (template_robust_converse _ _ _) lifting⟩

/-- Successful finite runs correspond at each exact count, not merely after
forgetting costs. Divergence and stuckness are not confused with termination. -/
theorem filling_termination_count {d} {G H : Hypernet d [.term] []}
    (w : FillingWitness template G H) (left : HoleFree G) (right : HoleFree H) (n : Nat) :
    (∃ s, unboundedMachine.Steps n ⟨d,G,(.search,.input 0)⟩ s ∧ unboundedMachine.final s) ↔
    (∃ t, unboundedMachine.Steps n ⟨d,H,(.search,.input 0)⟩ t ∧ unboundedMachine.final t) := by
  have eq := filling_exact_equiv w left right
  constructor
  · rintro ⟨a,run,done⟩
    obtain ⟨m,b,cost,run',done'⟩ := eq.1 run done
    cases cost
    exact ⟨b,run',done'⟩
  · rintro ⟨b,run,done⟩
    obtain ⟨m,a,cost,run',done'⟩ := eq.2 run done
    cases cost
    exact ⟨a,run',done'⟩
end Hypernets.Copying.BoxPermutation
